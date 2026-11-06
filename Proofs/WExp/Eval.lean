import Proofs.WExp.Model
import Reasoning.SteleBody

/-!
# `wExp` spec ↔ model correspondence

Determinism at the spec level: *every* `ExecFuncBody` derivation of `wExpFunction.body`
(the internal `wExp`) on a frame whose contract is `wexpContract` and whose locals bind
`"x" ↦ .int x` with `x ∈ [-MAXINPUT, MAXINPUT]` ends in
`.returned _ _ (some [.int (specWExp x)])`; `wExpExternal.body` likewise produces
`specWExpExternal x`.

These are *inversion* theorems: each `ExecBlock`/`ExecStmt` derivation is case-split and
every `evalExpr?` premise is computed, so the revert/static alternatives are ruled out
arithmetically (`evalExpr?` is a function, hence an `.ok` computation contradicts a
`.revert` premise, and `specWExpPos` is strictly positive on the input range so
`1e36 / __pos` never divides by zero).
-/

open Stele ABI
open Reasoning.Theory

namespace WExp

/-- The model of the external `wExp` transition: it delegates to the internal `wExp`. -/
def specWExpExternal (x : Int) : Int := specWExp x

/-! ## `ExecBlock` inversion lemmas -/

/-- A block headed by `ite` either ran a branch to fall-through (`rest` then decides `r`),
    ran a branch that terminated the block, or reverted evaluating the condition. -/
theorem execBlock_ite_cons {cfg : Config} {stele : Frame} {evm : EVM.State}
    {cond : Expr} {thenB elseB rest : List Stmt} {r : ExecResult}
    (h : ExecBlock cfg stele evm (.ite cond thenB elseB :: rest) r) :
    (∃ stele' evm', ExecBlock cfg stele' evm' rest r ∧
        ((evalExpr? cfg stele evm cond = .ok (.bool true) ∧
            ExecBlock cfg stele evm thenB (.ok stele' evm')) ∨
         (evalExpr? cfg stele evm cond = .ok (.bool false) ∧
            ExecBlock cfg stele evm elseB (.ok stele' evm')))) ∨
    ((evalExpr? cfg stele evm cond = .ok (.bool true) ∧
        ExecBlock cfg stele evm thenB r) ∨
     (evalExpr? cfg stele evm cond = .ok (.bool false) ∧
        ExecBlock cfg stele evm elseB r)) ∨
    (evalExpr? cfg stele evm cond = .revert ∧ r = .reverted) := by
  cases h with
  | consNormal hst hrest =>
      cases hst with
      | iteTrue hc hb => exact Or.inl ⟨_, _, hrest, Or.inl ⟨hc, hb⟩⟩
      | iteFalse hc hb => exact Or.inl ⟨_, _, hrest, Or.inr ⟨hc, hb⟩⟩
  | consReturn hst =>
      cases hst with
      | iteTrue hc hb => exact Or.inr (Or.inl (Or.inl ⟨hc, hb⟩))
      | iteFalse hc hb => exact Or.inr (Or.inl (Or.inr ⟨hc, hb⟩))
  | consRevert hst =>
      cases hst with
      | iteTrue hc hb => exact Or.inr (Or.inl (Or.inl ⟨hc, hb⟩))
      | iteFalse hc hb => exact Or.inr (Or.inl (Or.inr ⟨hc, hb⟩))
      | iteCondRevert hc => exact Or.inr (Or.inr ⟨hc, rfl⟩)
  | consBreak hst =>
      cases hst with
      | iteTrue hc hb => exact Or.inr (Or.inl (Or.inl ⟨hc, hb⟩))
      | iteFalse hc hb => exact Or.inr (Or.inl (Or.inr ⟨hc, hb⟩))
  | consContinue hst =>
      cases hst with
      | iteTrue hc hb => exact Or.inr (Or.inl (Or.inl ⟨hc, hb⟩))
      | iteFalse hc hb => exact Or.inr (Or.inl (Or.inr ⟨hc, hb⟩))
  | consStatic hst =>
      cases hst with
      | iteTrue hc hb => exact Or.inr (Or.inl (Or.inl ⟨hc, hb⟩))
      | iteFalse hc hb => exact Or.inr (Or.inl (Or.inr ⟨hc, hb⟩))

/-- A block headed by `let` either bound the evaluated value and ran `rest`, or reverted
    evaluating the right-hand side.  (Like `execBlock_letDecl_cons`, but keeps the revert
    reason so the `r = .reverted` alternative can be refuted by computing `evalExpr?`.) -/
theorem execBlock_letDecl_inv {cfg : Config} {stele : Frame} {evm : EVM.State}
    {name : Ident} {ty : Option ABIType} {e : Expr} {rest : List Stmt} {r : ExecResult}
    (h : ExecBlock cfg stele evm (.letDecl name ty e :: rest) r) :
    (∃ v, evalExpr? cfg stele evm e = .ok v ∧
        ExecBlock cfg { stele with locals := stele.locals.insert name v } evm rest r) ∨
    (evalExpr? cfg stele evm e = .revert ∧ r = .reverted) := by
  cases h with
  | consNormal hst hrest =>
      cases hst with
      | letDecl hv => exact Or.inl ⟨_, hv, hrest⟩
  | consRevert hst =>
      cases hst with
      | letDeclRevert hv => exact Or.inr ⟨hv, rfl⟩
  | consReturn hst => cases hst
  | consBreak hst => cases hst
  | consContinue hst => cases hst
  | consStatic hst => cases hst

/-- A block headed by `return` either returned the evaluated values from the current state
    or reverted evaluating them. -/
theorem execBlock_return_inv {cfg : Config} {stele : Frame} {evm : EVM.State}
    {es : List Expr} {rest : List Stmt} {r : ExecResult}
    (h : ExecBlock cfg stele evm (.return es :: rest) r) :
    (∃ vs, evalExprs? cfg stele evm es = .ok vs ∧ r = .returned stele evm (some vs)) ∨
    (evalExprs? cfg stele evm es = .revert ∧ r = .reverted) := by
  cases h with
  | consReturn hst =>
      cases hst with
      | «return» hvs => exact Or.inl ⟨_, hvs, rfl⟩
  | consRevert hst =>
      cases hst with
      | returnRevert hvs => exact Or.inr ⟨hvs, rfl⟩
  | consNormal hst => cases hst
  | consBreak hst => cases hst
  | consContinue hst => cases hst
  | consStatic hst => cases hst

/-- A block headed by `internalCall`: the callee returned and `rest` ran in the resumed
    frame, or one of the revert/static alternatives fired. -/
theorem execBlock_internalCall_cons {cfg : Config} {stele : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {rest : List Stmt} {r : ExecResult}
    (h : ExecBlock cfg stele evm (.internalCall name args retVar :: rest) r) :
    (∃ argVals callee locals calleeStele calleeEvm value,
        evalExprs? cfg stele evm args = .ok argVals ∧
        lookupCallable? stele.contract name = some callee ∧
        bindParams? callee.params argVals = some locals ∧
        ExecFuncBody cfg { stele with locals := locals } evm callee.body
          (.returned calleeStele calleeEvm value) ∧
        ExecBlock cfg (resumeAfterInternalCall stele retVar value) calleeEvm rest r) ∨
    (∃ argVals callee locals,
        evalExprs? cfg stele evm args = .ok argVals ∧
        lookupCallable? stele.contract name = some callee ∧
        bindParams? callee.params argVals = some locals ∧
        ExecFuncBody cfg { stele with locals := locals } evm callee.body .reverted ∧
        r = .reverted) ∨
    (evalExprs? cfg stele evm args = .revert ∧ r = .reverted) ∨
    (∃ argVals callee locals,
        evalExprs? cfg stele evm args = .ok argVals ∧
        lookupCallable? stele.contract name = some callee ∧
        bindParams? callee.params argVals = some locals ∧
        ExecFuncBody cfg { stele with locals := locals } evm callee.body .staticViolation ∧
        r = .staticViolation) := by
  cases h with
  | consNormal hst hrest =>
      cases hst with
      | internalCallReturn hargs hlookup hbind hbody =>
          exact Or.inl ⟨_, _, _, _, _, _, hargs, hlookup, hbind, hbody, hrest⟩
  | consRevert hst =>
      cases hst with
      | internalCallRevert hargs hlookup hbind hbody =>
          exact Or.inr (Or.inl ⟨_, _, _, hargs, hlookup, hbind, hbody, rfl⟩)
      | internalCallArgsRevert hargs =>
          exact Or.inr (Or.inr (Or.inl ⟨hargs, rfl⟩))
  | consStatic hst =>
      cases hst with
      | internalCallStatic hargs hlookup hbind hbody =>
          exact Or.inr (Or.inr (Or.inr ⟨_, _, _, hargs, hlookup, hbind, hbody, rfl⟩))
  | consReturn hst => cases hst
  | consBreak hst => cases hst
  | consContinue hst => cases hst

/-! ## `evalExpr?` computations on the `wExp` frames -/

theorem evalVar_int {cfg : Config} {stele : Frame} {evm : EVM.State}
    {n : Ident} {i : Int} (h : stele.locals.get? n = some (.int i)) :
    evalExpr? cfg stele evm (.var n) = .ok (.int i) := by
  simp only [evalExpr?, h, EvalResult.ofOption]

/-- The `x < 0` guard evaluates to the literal decision. -/
theorem eval_wExpCond {cfg : Config} {stele : Frame} {evm : EVM.State} {x : Int}
    (hx : stele.locals.get? "x" = some (.int x)) :
    evalExpr? cfg stele evm wExpCond = .ok (.bool (x < 0)) := by
  simp only [wExpCond, evalExpr?, hx, evalBinaryOp?, EvalResult.bind, bind, pure,
    EvalResult.ofOption]

/-- `q = (x + offset) / ln2` — `.sdiv` is `Int.tdiv`. -/
theorem eval_wExpQ {cfg : Config} {stele : Frame} {evm : EVM.State} {x : Int}
    (hx : stele.locals.get? "x" = some (.int x)) :
    evalExpr? cfg stele evm
      (.binary .sdiv (.binary .add (.var "x") (.intLit 322611214989459870))
        (.intLit 693147180559945309)) = .ok (.int (qOf x)) := by
  simp only [evalExpr?, hx, evalBinaryOp?, EvalResult.bind, bind, pure, EvalResult.ofOption]
  rw [if_neg (by decide : (693147180559945309 : Int) ≠ 0)]
  rfl

/-- `r = x - q * ln2`. -/
theorem eval_wExpR {cfg : Config} {stele : Frame} {evm : EVM.State} {x : Int}
    (hx : stele.locals.get? "x" = some (.int x))
    (hq : stele.locals.get? "q" = some (.int (qOf x))) :
    evalExpr? cfg stele evm
      (.binary .sub (.var "x")
        (.binary .mul (.var "q") (.intLit 693147180559945309))) = .ok (.int (rOf x)) := by
  simp only [evalExpr?, hx, hq, evalBinaryOp?, EvalResult.bind, bind, pure,
    EvalResult.ofOption]
  rfl

/-- `secondTerm = r * r / (2 * 1e18)`. -/
theorem eval_wExpS {cfg : Config} {stele : Frame} {evm : EVM.State} {r : Int}
    (hr : stele.locals.get? "r" = some (.int r)) :
    evalExpr? cfg stele evm
      (.binary .sdiv (.binary .mul (.var "r") (.var "r"))
        (.intLit 2000000000000000000)) = .ok (.int (sOf r)) := by
  simp only [evalExpr?, hr, evalBinaryOp?, EvalResult.bind, bind, pure, EvalResult.ofOption]
  rw [if_neg (by decide : (2000000000000000000 : Int) ≠ 0)]
  rfl

/-- `thirdTerm = secondTerm * r / (3 * 1e18)`. -/
theorem eval_wExpT {cfg : Config} {stele : Frame} {evm : EVM.State} {r : Int}
    (hs : stele.locals.get? "secondTerm" = some (.int (sOf r)))
    (hr : stele.locals.get? "r" = some (.int r)) :
    evalExpr? cfg stele evm
      (.binary .sdiv (.binary .mul (.var "secondTerm") (.var "r"))
        (.intLit 3000000000000000000)) = .ok (.int (tOf r)) := by
  simp only [evalExpr?, hs, hr, evalBinaryOp?, EvalResult.bind, bind, pure,
    EvalResult.ofOption]
  rw [if_neg (by decide : (3000000000000000000 : Int) ≠ 0)]
  rfl

/-- `expR = 1e18 + r + secondTerm + thirdTerm` — the `poly` model. -/
theorem eval_wExpE {cfg : Config} {stele : Frame} {evm : EVM.State} {r : Int}
    (ht : stele.locals.get? "thirdTerm" = some (.int (tOf r)))
    (hs : stele.locals.get? "secondTerm" = some (.int (sOf r)))
    (hr : stele.locals.get? "r" = some (.int r)) :
    evalExpr? cfg stele evm
      (.binary .add (.binary .add (.binary .add (.intLit 1000000000000000000) (.var "r"))
        (.var "secondTerm")) (.var "thirdTerm")) = .ok (.int (poly r)) := by
  simp only [evalExpr?, hr, hs, ht, evalBinaryOp?, EvalResult.bind, bind, pure,
    EvalResult.ofOption]
  rfl

/-- `qOf x` stays well under the `uint256` shift limit on the input range. -/
theorem qOf_lt_256 {x : Int} (hx : 0 ≤ x) (hxm : x ≤ MAXINPUT) : qOf x < 256 := by
  rw [qOf_eq x hx]
  have hle : (x + OFFSET) / LN2 ≤ (MAXINPUT + OFFSET) / LN2 := by
    apply Int.ediv_le_ediv (c := LN2) (by unfold LN2; decide)
    omega
  have hM : (MAXINPUT + OFFSET) / LN2 = 24 := by
    unfold MAXINPUT OFFSET LN2; native_decide
  omega

/-- `return uint256(expR) << uint256(q)`: the `.shl` result is `specWExpPos x`. -/
theorem eval_wExpRet {cfg : Config} {stele : Frame} {evm : EVM.State} {x : Int}
    (hq : stele.locals.get? "q" = some (.int (qOf x)))
    (he : stele.locals.get? "expR" = some (.int (poly (rOf x))))
    (hx0 : 0 ≤ x) (hxm : x ≤ MAXINPUT) :
    evalExpr? cfg stele evm
      (.binary (.shl (.uint ⟨256, by decide⟩)) (.cast (.var "expR") uint256)
        (.cast (.var "q") uint256)) = .ok (.int (specWExpPos x)) := by
  have hq0 := qOf_nonneg hx0
  have hq256 := qOf_lt_256 hx0 hxm
  have hpoly0 : 0 < poly (rOf x) := poly_pos (rOf_bounds hx0).1
  have hpolyW : poly (rOf x) ≤ wExpPos x := by
    rw [wExpPos_eq]
    have h2 : (1 : Int) ≤ 2 ^ (qOf x).toNat := by
      have hp : (0 : Int) < 2 ^ (qOf x).toNat := Int.pow_pos (n := 2) (by decide)
      omega
    calc poly (rOf x) = poly (rOf x) * 1 := by simp
      _ ≤ poly (rOf x) * 2 ^ (qOf x).toNat :=
          Int.mul_le_mul_of_nonneg_left h2 (Int.le_of_lt hpoly0)
  have hbound := (wExpPos_bound hx0 hxm).2
  have h2p : Int.ofNat (EVM.twoPow 256) =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    native_decide
  have hnq : normalizeInt (.uint ⟨256, by decide⟩) (qOf x) = qOf x :=
    normalizeInt_uint_eq_self _ _ hq0 (by rw [h2p]; omega)
  have hne : normalizeInt (.uint ⟨256, by decide⟩) (poly (rOf x)) = poly (rOf x) :=
    normalizeInt_uint_eq_self _ _ (Int.le_of_lt hpoly0) (by
      rw [h2p]; unfold MAXOUTPUT at hbound; omega)
  simp only [evalExpr?, he, hq, evalBinaryOp?, castValue_int, hnq, hne, EvalResult.bind,
    bind, EvalResult.ofOption, uint256, StorageType.ofABI]
  rw [if_neg (by omega : ¬ qOf x < 0)]
  rw [if_neg (show ¬ (IntType.uint ⟨256, by decide⟩).bitWidth.val ≤ (qOf x).toNat from by
    have hbw : (IntType.uint ⟨256, by decide⟩).bitWidth.val = 256 := rfl
    rw [hbw]; omega)]
  have ht2 : Int.ofNat (EVM.twoPow (qOf x).toNat) = (2 : Int) ^ (qOf x).toNat := by
    simp [EVM.twoPow]
  rw [ht2, show poly (rOf x) * 2 ^ (qOf x).toNat = wExpPos x from (wExpPos_eq x).symm]
  rfl

/-! ## The `x ≥ 0` (else) branch -/

/-- Any execution of the else-branch block returns `specWExpPos x`. -/
theorem wExpElseBlock_inv {cfg : Config} {stele : Frame} {evm : EVM.State}
    {x : Int} {r : ExecResult}
    (hx : stele.locals.get? "x" = some (.int x))
    (hx0 : 0 ≤ x) (hxm : x ≤ MAXINPUT)
    (hb : ExecBlock cfg stele evm wExpElseBody r) :
    ∃ stele', r = .returned stele' evm (some [.int (specWExpPos x)]) := by
  -- q := sdiv(x + offset, ln2)
  have hq := eval_wExpQ (cfg := cfg) (evm := evm) hx
  obtain ⟨v, hev, hb⟩ | ⟨hev, _⟩ := execBlock_letDecl_inv hb
  swap; · rw [hq] at hev; cases hev
  obtain rfl := EvalResult.ok.inj (hq ▸ hev)
  set stele1 : Frame := {stele with locals := stele.locals.insert "q" (.int (qOf x))}
  have hx1 : stele1.locals.get? "x" = some (.int x) := by
    show (stele.locals.insert "q" _).get? "x" = _
    rw [store_get_ne _ _ (by decide : ("q" == "x") = false), hx]
  have hq1 : stele1.locals.get? "q" = some (.int (qOf x)) := store_get_self _ _ _
  -- r := x - q * ln2
  have hr := eval_wExpR (cfg := cfg) (evm := evm) hx1 hq1
  obtain ⟨v, hev, hb⟩ | ⟨hev, _⟩ := execBlock_letDecl_inv hb
  swap; · rw [hr] at hev; cases hev
  obtain rfl := EvalResult.ok.inj (hr ▸ hev)
  set stele2 : Frame := {stele1 with locals := stele1.locals.insert "r" (.int (rOf x))}
  have hr2 : stele2.locals.get? "r" = some (.int (rOf x)) := store_get_self _ _ _
  -- secondTerm := sdiv(r * r, 2e18)
  have hs := eval_wExpS (cfg := cfg) (evm := evm) hr2
  obtain ⟨v, hev, hb⟩ | ⟨hev, _⟩ := execBlock_letDecl_inv hb
  swap; · rw [hs] at hev; cases hev
  obtain rfl := EvalResult.ok.inj (hs ▸ hev)
  set stele3 : Frame :=
    {stele2 with locals := stele2.locals.insert "secondTerm" (.int (sOf (rOf x)))}
  have hs3 : stele3.locals.get? "secondTerm" = some (.int (sOf (rOf x))) :=
    store_get_self _ _ _
  have hr3 : stele3.locals.get? "r" = some (.int (rOf x)) := by
    show (((stele.locals.insert "q" _).insert "r" _).insert "secondTerm" _).get? "r" = _
    rw [store_get_ne _ _ (by decide : ("secondTerm" == "r") = false)]
    exact store_get_self _ _ _
  -- thirdTerm := sdiv(secondTerm * r, 3e18)
  have ht := eval_wExpT (cfg := cfg) (evm := evm) hs3 hr3
  obtain ⟨v, hev, hb⟩ | ⟨hev, _⟩ := execBlock_letDecl_inv hb
  swap; · rw [ht] at hev; cases hev
  obtain rfl := EvalResult.ok.inj (ht ▸ hev)
  set stele4 : Frame :=
    {stele3 with locals := stele3.locals.insert "thirdTerm" (.int (tOf (rOf x)))}
  have ht4 : stele4.locals.get? "thirdTerm" = some (.int (tOf (rOf x))) :=
    store_get_self _ _ _
  have hs4 : stele4.locals.get? "secondTerm" = some (.int (sOf (rOf x))) := by
    show ((((stele.locals.insert "q" _).insert "r" _).insert "secondTerm" _).insert
        "thirdTerm" _).get? "secondTerm" = _
    rw [store_get_ne _ _ (by decide : ("thirdTerm" == "secondTerm") = false)]
    exact store_get_self _ _ _
  have hr4 : stele4.locals.get? "r" = some (.int (rOf x)) := by
    show ((((stele.locals.insert "q" _).insert "r" _).insert "secondTerm" _).insert
        "thirdTerm" _).get? "r" = _
    rw [store_get_ne2 _ _ _ (by decide : ("secondTerm" == "r") = false)
      (by decide : ("thirdTerm" == "r") = false)]
    exact store_get_self _ _ _
  -- expR := 1e18 + r + secondTerm + thirdTerm
  have he := eval_wExpE (cfg := cfg) (evm := evm) ht4 hs4 hr4
  obtain ⟨v, hev, hb⟩ | ⟨hev, _⟩ := execBlock_letDecl_inv hb
  swap; · rw [he] at hev; cases hev
  obtain rfl := EvalResult.ok.inj (he ▸ hev)
  set stele5 : Frame :=
    {stele4 with locals := stele4.locals.insert "expR" (.int (poly (rOf x)))}
  have he5 : stele5.locals.get? "expR" = some (.int (poly (rOf x))) := store_get_self _ _ _
  have hq5 : stele5.locals.get? "q" = some (.int (qOf x)) := by
    show (((((stele.locals.insert "q" _).insert "r" _).insert "secondTerm" _).insert
        "thirdTerm" _).insert "expR" _).get? "q" = _
    rw [store_get_ne4 _ _ _ _ _ (by decide : ("r" == "q") = false)
      (by decide : ("secondTerm" == "q") = false)
      (by decide : ("thirdTerm" == "q") = false)
      (by decide : ("expR" == "q") = false)]
    exact store_get_self _ _ _
  -- return uint256(expR) << uint256(q)
  have hret := eval_wExpRet (cfg := cfg) (evm := evm) hq5 he5 hx0 hxm
  obtain ⟨vs, hvs, hr⟩ | ⟨hvs, _⟩ := execBlock_return_inv hb
  swap; · rw [evalExprs?_singleton hret] at hvs; cases hvs
  rw [evalExprs?_singleton hret] at hvs
  obtain rfl := EvalResult.ok.inj hvs
  exact ⟨_, hr⟩

/-- Any `ExecBlock` on `wExpFunction.body` at `x ≥ 0` returns `specWExpPos x`. -/
theorem wExp_body_inv_nonneg {cfg : Config} {stele : Frame} {evm : EVM.State}
    {x : Int} {r : ExecResult}
    (hx : stele.locals.get? "x" = some (.int x))
    (hx0 : 0 ≤ x) (hxm : x ≤ MAXINPUT)
    (hb : ExecBlock cfg stele evm wExpFunction.body r) :
    ∃ stele', r = .returned stele' evm (some [.int (specWExpPos x)]) := by
  have hce := eval_wExpCond (cfg := cfg) (evm := evm) hx
  obtain ⟨s, e, _, hcase⟩ | hterm | ⟨hrev, _⟩ := execBlock_ite_cons hb
  · obtain ⟨hc, hb2⟩ | ⟨hc, hb2⟩ := hcase
    · -- then-branch ran to `.ok`: cond evaluated `true`, contradicting `0 ≤ x`.
      have h2 := EvalResult.ok.inj (hc.symm.trans hce)
      have hlt : x < 0 := of_decide_eq_true (Value.bool.inj h2).symm
      omega
    · -- else-branch cannot fall through to `.ok` — it always returns.
      obtain ⟨_, hbad⟩ := wExpElseBlock_inv hx hx0 hxm hb2
      cases hbad
  · obtain ⟨hc, hb2⟩ | ⟨hc, hb2⟩ := hterm
    · have h2 := EvalResult.ok.inj (hc.symm.trans hce)
      have hlt : x < 0 := of_decide_eq_true (Value.bool.inj h2).symm
      omega
    · exact wExpElseBlock_inv hx hx0 hxm hb2
  · rw [hce] at hrev; cases hrev

/-- Any `ExecFuncBody` on `wExpFunction.body` at `x ≥ 0` returns `specWExpPos x`. -/
theorem wExpFuncBody_nonneg {cfg : Config} {stele : Frame} {evm : EVM.State}
    {x : Int} {r : ExecResult}
    (hx : stele.locals.get? "x" = some (.int x))
    (hx0 : 0 ≤ x) (hxm : x ≤ MAXINPUT)
    (h : ExecFuncBody cfg stele evm wExpFunction.body r) :
    ∃ stele' evm', r = .returned stele' evm' (some [.int (specWExpPos x)]) := by
  cases h with
  | execBlockOK hb =>
      obtain ⟨s, hbad⟩ := wExp_body_inv_nonneg hx hx0 hxm hb
      exact ⟨s, evm, by cases hbad⟩
  | execBlockRet hb =>
      obtain ⟨s, hret⟩ := wExp_body_inv_nonneg hx hx0 hxm hb
      exact ⟨s, evm, hret⟩
  | execBlockRevert hb =>
      obtain ⟨s, hbad⟩ := wExp_body_inv_nonneg hx hx0 hxm hb; cases hbad
  | execBlockBreak hb =>
      obtain ⟨s, hbad⟩ := wExp_body_inv_nonneg hx hx0 hxm hb; cases hbad
  | execBlockContinue hb =>
      obtain ⟨s, hbad⟩ := wExp_body_inv_nonneg hx hx0 hxm hb; cases hbad
  | execBlockStatic hb =>
      obtain ⟨s, hbad⟩ := wExp_body_inv_nonneg hx hx0 hxm hb; cases hbad

/-! ## The `x < 0` (then) branch -/

/-- Any execution of the then-branch block returns `1e36 / specWExpPos (-x)` —
    the recursive internal call on `-x` lands in the else branch since `-x ≥ 0`. -/
theorem wExpThenBlock_inv {cfg : Config} {stele : Frame} {evm : EVM.State}
    {x : Int} {r : ExecResult}
    (hcontract : stele.contract = wexpContract)
    (hx : stele.locals.get? "x" = some (.int x))
    (hx0 : x < 0) (hxm : -MAXINPUT ≤ x)
    (hb : ExecBlock cfg stele evm wExpThenBody r) :
    ∃ stele' evm', r = .returned stele' evm'
      (some [.int ((10 ^ 36 : Int) / specWExpPos (-x))]) := by
  have hneg : evalExpr? cfg stele evm (.unary .neg (.var "x")) = .ok (.int (-x)) := by
    simp only [evalExpr?, hx, evalUnaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
  have hargs : evalExprs? cfg stele evm [.unary .neg (.var "x")] = .ok [.int (-x)] :=
    evalExprs?_singleton hneg
  have hlookup : lookupCallable? stele.contract "wExp" = some wExpFunction.toCallable := by
    rw [hcontract]; rfl
  have hbind : bindParams? wExpFunction.toCallable.params [.int (-x)] =
      some ((∅ : Store).insert "x" (.int (-x))) := rfl
  have hxl : ({stele with locals := (∅ : Store).insert "x" (.int (-x))} : Frame).locals.get?
      "x" = some (.int (-x)) := store_get_self _ _ _
  have hpne : specWExpPos (-x) ≠ 0 :=
    (specWExpPos_pos (by omega : 0 ≤ -x) (by omega : -x ≤ MAXINPUT)).ne'
  obtain ⟨argVals, callee, locals, cs, ce, value, hargs', hlookup', hbind', hbody, hb⟩ |
      ⟨argVals, callee, locals, hargs', hlookup', hbind', hbody, _⟩ |
      ⟨hargs', _⟩ |
      ⟨argVals, callee, locals, hargs', hlookup', hbind', hbody, _⟩ :=
    execBlock_internalCall_cons hb
  · -- the callee returned `specWExpPos (-x)`; the `1e36 / __pos` return follows.
    rw [hargs] at hargs'; obtain rfl := EvalResult.ok.inj hargs'
    rw [hlookup] at hlookup'; obtain rfl := Option.some.inj hlookup'
    rw [hbind] at hbind'; obtain rfl := Option.some.inj hbind'
    obtain ⟨_, _, hres⟩ := wExpFuncBody_nonneg
      (stele := {stele with locals := (∅ : Store).insert "x" (.int (-x))}) (x := -x) hxl
      (by omega : 0 ≤ -x) (by omega : -x ≤ MAXINPUT) hbody
    cases hres
    -- resumed frame: __pos ↦ specWExpPos (-x)
    have hres_lookup : (resumeAfterInternalCall stele "__pos"
        (some [.int (specWExpPos (-x))])).locals.get? "__pos" =
        some (.int (specWExpPos (-x))) := by
      show (stele.locals.insert "__pos" (collapseReturns [.int (specWExpPos (-x))])).get?
          "__pos" = _
      exact store_get_self _ _ _
    have hdiv : evalExpr? cfg (resumeAfterInternalCall stele "__pos"
        (some [.int (specWExpPos (-x))])) ce
        (.binary .div (.intLit 1000000000000000000000000000000000000) (.var "__pos")) =
        .ok (.int ((10 ^ 36 : Int) / specWExpPos (-x))) := by
      simp only [evalExpr?, hres_lookup, evalBinaryOp?, EvalResult.bind, bind, pure,
        EvalResult.ofOption]
      rw [if_neg hpne, show (1000000000000000000000000000000000000 : Int) = 10 ^ 36
        from by decide]
    obtain ⟨vs, hvs, hr⟩ | ⟨hvs, _⟩ := execBlock_return_inv hb
    swap; · rw [evalExprs?_singleton hdiv] at hvs; cases hvs
    rw [evalExprs?_singleton hdiv] at hvs
    obtain rfl := EvalResult.ok.inj hvs
    exact ⟨_, _, hr⟩
  · -- the callee `.reverted` — impossible, it returns `specWExpPos (-x)`.
    rw [hargs] at hargs'; obtain rfl := EvalResult.ok.inj hargs'
    rw [hlookup] at hlookup'; obtain rfl := Option.some.inj hlookup'
    rw [hbind] at hbind'; obtain rfl := Option.some.inj hbind'
    obtain ⟨_, _, hbad⟩ := wExpFuncBody_nonneg
      (stele := {stele with locals := (∅ : Store).insert "x" (.int (-x))}) (x := -x) hxl
      (by omega : 0 ≤ -x) (by omega : -x ≤ MAXINPUT) hbody
    cases hbad
  · -- argument evaluation reverted — impossible, `-x` evaluates fine.
    rw [hargs] at hargs'; cases hargs'
  · -- the callee `.staticViolation` — impossible, it returns.
    rw [hargs] at hargs'; obtain rfl := EvalResult.ok.inj hargs'
    rw [hlookup] at hlookup'; obtain rfl := Option.some.inj hlookup'
    rw [hbind] at hbind'; obtain rfl := Option.some.inj hbind'
    obtain ⟨_, _, hbad⟩ := wExpFuncBody_nonneg
      (stele := {stele with locals := (∅ : Store).insert "x" (.int (-x))}) (x := -x) hxl
      (by omega : 0 ≤ -x) (by omega : -x ≤ MAXINPUT) hbody
    cases hbad

/-- Any `ExecBlock` on `wExpFunction.body` on `[-MAXINPUT, MAXINPUT]` returns
    `specWExp x`. -/
theorem wExp_body_inv {cfg : Config} {stele : Frame} {evm : EVM.State}
    {x : Int} {r : ExecResult}
    (hcontract : stele.contract = wexpContract)
    (hx : stele.locals.get? "x" = some (.int x))
    (hlo : -MAXINPUT ≤ x) (hhi : x ≤ MAXINPUT)
    (hb : ExecBlock cfg stele evm wExpFunction.body r) :
    ∃ stele' evm', r = .returned stele' evm' (some [.int (specWExp x)]) := by
  have hce := eval_wExpCond (cfg := cfg) (evm := evm) hx
  obtain ⟨s, e, _, hcase⟩ | hterm | ⟨hrev, _⟩ := execBlock_ite_cons hb
  · obtain ⟨hc, hb2⟩ | ⟨hc, hb2⟩ := hcase
    · -- then-branch `.ok`: impossible — the branch always returns.
      have hlt : x < 0 := by
        have h2 := EvalResult.ok.inj (hc.symm.trans hce)
        exact of_decide_eq_true (Value.bool.inj h2).symm
      obtain ⟨_, _, hbad⟩ := wExpThenBlock_inv hcontract hx hlt hlo hb2
      cases hbad
    · -- else-branch `.ok`: impossible — the branch always returns.
      have hxf : ¬ x < 0 := by
        have h2 := EvalResult.ok.inj (hc.symm.trans hce)
        exact of_decide_eq_false (Value.bool.inj h2).symm
      obtain ⟨_, hbad⟩ := wExpElseBlock_inv hx (by omega) hhi hb2
      cases hbad
  · obtain ⟨hc, hb2⟩ | ⟨hc, hb2⟩ := hterm
    · -- then-branch terminated the block.
      have hlt : x < 0 := by
        have h2 := EvalResult.ok.inj (hc.symm.trans hce)
        exact of_decide_eq_true (Value.bool.inj h2).symm
      obtain ⟨s', e', hret⟩ := wExpThenBlock_inv hcontract hx hlt hlo hb2
      refine ⟨s', e', hret.trans ?_⟩
      congr 1
      unfold specWExp; rw [if_pos hlt]
    · -- else-branch terminated the block.
      have hxf : ¬ x < 0 := by
        have h2 := EvalResult.ok.inj (hc.symm.trans hce)
        exact of_decide_eq_false (Value.bool.inj h2).symm
      obtain ⟨s', hret⟩ := wExpElseBlock_inv hx (by omega) hhi hb2
      refine ⟨s', evm, hret.trans ?_⟩
      congr 1
      unfold specWExp; rw [if_neg hxf]
  · rw [hce] at hrev; cases hrev

/-- **The correspondence**: every `wExp` internal-body execution on
    `x ∈ [-MAXINPUT, MAXINPUT]` returns `.int (specWExp x)`. -/
theorem wExp_result {cfg : Config} {stele : Frame} {evm : EVM.State}
    {x : Int} {r : ExecResult}
    (hcontract : stele.contract = wexpContract)
    (hx : stele.locals.get? "x" = some (.int x))
    (hlo : -MAXINPUT ≤ x) (hhi : x ≤ MAXINPUT)
    (h : ExecFuncBody cfg stele evm wExpFunction.body r) :
    ∃ stele' evm', r = .returned stele' evm' (some [.int (specWExp x)]) := by
  cases h with
  | execBlockOK hb =>
      obtain ⟨s, e, hbad⟩ := wExp_body_inv hcontract hx hlo hhi hb; cases hbad
  | execBlockRet hb => exact wExp_body_inv hcontract hx hlo hhi hb
  | execBlockRevert hb =>
      obtain ⟨s, e, hbad⟩ := wExp_body_inv hcontract hx hlo hhi hb; cases hbad
  | execBlockBreak hb =>
      obtain ⟨s, e, hbad⟩ := wExp_body_inv hcontract hx hlo hhi hb; cases hbad
  | execBlockContinue hb =>
      obtain ⟨s, e, hbad⟩ := wExp_body_inv hcontract hx hlo hhi hb; cases hbad
  | execBlockStatic hb =>
      obtain ⟨s, e, hbad⟩ := wExp_body_inv hcontract hx hlo hhi hb; cases hbad

/-- Any `ExecBlock` on `wExpExternal.body` returns `specWExpExternal x`: the wrapper's
    internal call delegates to `wExp` and returns `__w`. -/
theorem wExpExternal_body_inv {cfg : Config} {stele : Frame} {evm : EVM.State}
    {x : Int} {r : ExecResult}
    (hcontract : stele.contract = wexpContract)
    (hx : stele.locals.get? "x" = some (.int x))
    (hlo : -MAXINPUT ≤ x) (hhi : x ≤ MAXINPUT)
    (hb : ExecBlock cfg stele evm wExpExternal.body r) :
    ∃ stele' evm', r = .returned stele' evm' (some [.int (specWExpExternal x)]) := by
  have hargs : evalExprs? cfg stele evm [.var "x"] = .ok [.int x] :=
    evalExprs?_singleton (evalVar_int (cfg := cfg) (evm := evm) hx)
  have hlookup : lookupCallable? stele.contract "wExp" = some wExpFunction.toCallable := by
    rw [hcontract]; rfl
  have hbind : bindParams? wExpFunction.toCallable.params [.int x] =
      some ((∅ : Store).insert "x" (.int x)) := rfl
  have hxl : ({stele with locals := (∅ : Store).insert "x" (.int x)} : Frame).locals.get?
      "x" = some (.int x) := store_get_self _ _ _
  obtain ⟨argVals, callee, locals, cs, ce, value, hargs', hlookup', hbind', hbody, hb⟩ |
      ⟨argVals, callee, locals, hargs', hlookup', hbind', hbody, _⟩ |
      ⟨hargs', _⟩ |
      ⟨argVals, callee, locals, hargs', hlookup', hbind', hbody, _⟩ :=
    execBlock_internalCall_cons hb
  · rw [hargs] at hargs'; obtain rfl := EvalResult.ok.inj hargs'
    rw [hlookup] at hlookup'; obtain rfl := Option.some.inj hlookup'
    rw [hbind] at hbind'; obtain rfl := Option.some.inj hbind'
    obtain ⟨_, _, hres⟩ := wExp_result
      (stele := {stele with locals := (∅ : Store).insert "x" (.int x)})
      (by show {stele with locals := (∅ : Store).insert "x" (.int x)}.contract =
        wexpContract; exact hcontract)
      hxl hlo hhi hbody
    cases hres
    have hres_lookup : (resumeAfterInternalCall stele "__w"
        (some [.int (specWExp x)])).locals.get? "__w" = some (.int (specWExp x)) := by
      show (stele.locals.insert "__w" (collapseReturns [.int (specWExp x)])).get? "__w" = _
      exact store_get_self _ _ _
    have hret : evalExpr? cfg (resumeAfterInternalCall stele "__w"
        (some [.int (specWExp x)])) ce (.var "__w") = .ok (.int (specWExp x)) :=
      evalVar_int (cfg := cfg) (evm := ce) hres_lookup
    obtain ⟨vs, hvs, hr⟩ | ⟨hvs, _⟩ := execBlock_return_inv hb
    swap; · rw [evalExprs?_singleton hret] at hvs; cases hvs
    rw [evalExprs?_singleton hret] at hvs
    obtain rfl := EvalResult.ok.inj hvs
    exact ⟨_, _, hr⟩
  · rw [hargs] at hargs'; obtain rfl := EvalResult.ok.inj hargs'
    rw [hlookup] at hlookup'; obtain rfl := Option.some.inj hlookup'
    rw [hbind] at hbind'; obtain rfl := Option.some.inj hbind'
    obtain ⟨_, _, hbad⟩ := wExp_result
      (stele := {stele with locals := (∅ : Store).insert "x" (.int x)})
      (by show {stele with locals := (∅ : Store).insert "x" (.int x)}.contract =
        wexpContract; exact hcontract)
      hxl hlo hhi hbody
    cases hbad
  · rw [hargs] at hargs'; cases hargs'
  · rw [hargs] at hargs'; obtain rfl := EvalResult.ok.inj hargs'
    rw [hlookup] at hlookup'; obtain rfl := Option.some.inj hlookup'
    rw [hbind] at hbind'; obtain rfl := Option.some.inj hbind'
    obtain ⟨_, _, hbad⟩ := wExp_result
      (stele := {stele with locals := (∅ : Store).insert "x" (.int x)})
      (by show {stele with locals := (∅ : Store).insert "x" (.int x)}.contract =
        wexpContract; exact hcontract)
      hxl hlo hhi hbody
    cases hbad

/-- The `wExpExternal` transition correspondence. -/
theorem wExpExternal_result {cfg : Config} {stele : Frame} {evm : EVM.State}
    {x : Int} {r : ExecResult}
    (hcontract : stele.contract = wexpContract)
    (hx : stele.locals.get? "x" = some (.int x))
    (hlo : -MAXINPUT ≤ x) (hhi : x ≤ MAXINPUT)
    (h : ExecFuncBody cfg stele evm wExpExternal.body r) :
    ∃ stele' evm', r = .returned stele' evm' (some [.int (specWExpExternal x)]) := by
  cases h with
  | execBlockOK hb =>
      obtain ⟨s, e, hbad⟩ := wExpExternal_body_inv hcontract hx hlo hhi hb; cases hbad
  | execBlockRet hb => exact wExpExternal_body_inv hcontract hx hlo hhi hb
  | execBlockRevert hb =>
      obtain ⟨s, e, hbad⟩ := wExpExternal_body_inv hcontract hx hlo hhi hb; cases hbad
  | execBlockBreak hb =>
      obtain ⟨s, e, hbad⟩ := wExpExternal_body_inv hcontract hx hlo hhi hb; cases hbad
  | execBlockContinue hb =>
      obtain ⟨s, e, hbad⟩ := wExpExternal_body_inv hcontract hx hlo hhi hb; cases hbad
  | execBlockStatic hb =>
      obtain ⟨s, e, hbad⟩ := wExpExternal_body_inv hcontract hx hlo hhi hb; cases hbad

end WExp
