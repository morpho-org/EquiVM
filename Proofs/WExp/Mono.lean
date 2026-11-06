import Proofs.WExp.Eval

/-!
# `wExp` monotonicity on the Stele spec

`wExp_step_spec` / `wExpExternal_step_spec`: any two spec executions of the internal
`wExp` body (resp. the external `wExp` transition) on consecutive inputs
`x, x + 1` with `x ∈ [-MAXINPUT, MAXINPUT)` return nondecreasing `uint256` values.

These lift the model-level `specWExp_step` through the `Eval.lean` correspondence:
`wExp_result`/`wExpExternal_result` pin every derivation's returned value to the model,
so the spec-level steps inherit the model's arithmetic monotonicity.
-/

open Stele ABI

namespace WExp

/-- Consecutive inputs on `[-MAXINPUT, MAXINPUT)` give nondecreasing `wExp` results. -/
theorem wExp_step_spec {cfg : Config} {stele₁ stele₂ stele₁' stele₂' : Frame}
    {evm evm₁' evm₂' : EVM.State} {x : Int} {v₁ v₂ : Value}
    (hc₁ : stele₁.contract = wexpContract) (hx₁ : stele₁.locals.get? "x" = some (.int x))
    (hc₂ : stele₂.contract = wexpContract) (hx₂ : stele₂.locals.get? "x" = some (.int (x + 1)))
    (hlo : -MAXINPUT ≤ x) (hhi : x < MAXINPUT)
    (h₁ : ExecFuncBody cfg stele₁ evm wExpFunction.body (.returned stele₁' evm₁' (some [v₁])))
    (h₂ : ExecFuncBody cfg stele₂ evm wExpFunction.body (.returned stele₂' evm₂' (some [v₂]))) :
    ∃ i j, v₁ = .int i ∧ v₂ = .int j ∧ i ≤ j := by
  obtain ⟨_, _, h₁⟩ := wExp_result hc₁ hx₁ hlo (Int.le_of_lt hhi) h₁
  obtain ⟨_, _, h₂⟩ := wExp_result hc₂ hx₂ (by omega) (by omega) h₂
  cases h₁; cases h₂
  exact ⟨specWExp x, specWExp (x + 1), rfl, rfl, specWExp_step hlo hhi⟩

/-- The same step on the external `wExp` transition body. -/
theorem wExpExternal_step_spec {cfg : Config} {stele₁ stele₂ stele₁' stele₂' : Frame}
    {evm evm₁' evm₂' : EVM.State} {x : Int} {v₁ v₂ : Value}
    (hc₁ : stele₁.contract = wexpContract) (hx₁ : stele₁.locals.get? "x" = some (.int x))
    (hc₂ : stele₂.contract = wexpContract) (hx₂ : stele₂.locals.get? "x" = some (.int (x + 1)))
    (hlo : -MAXINPUT ≤ x) (hhi : x < MAXINPUT)
    (h₁ : ExecFuncBody cfg stele₁ evm wExpExternal.body (.returned stele₁' evm₁' (some [v₁])))
    (h₂ : ExecFuncBody cfg stele₂ evm wExpExternal.body (.returned stele₂' evm₂' (some [v₂]))) :
    ∃ i j, v₁ = .int i ∧ v₂ = .int j ∧ i ≤ j := by
  obtain ⟨_, _, h₁⟩ := wExpExternal_result hc₁ hx₁ hlo (Int.le_of_lt hhi) h₁
  obtain ⟨_, _, h₂⟩ := wExpExternal_result hc₂ hx₂ (by omega) (by omega) h₂
  cases h₁; cases h₂
  exact ⟨specWExp x, specWExp (x + 1), rfl, rfl, specWExp_step hlo hhi⟩

end WExp
