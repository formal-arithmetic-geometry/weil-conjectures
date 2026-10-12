module
public import Sheaf.AlgebraicGeometry.DiagonalConormal
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The difference derivation into the diagonal conormal, with its local formula.
Source: Stacks Project, Tag 08S2. Construct the difference of the two splittings
of the square-zero diagonal extension and check the formula locally.
(blueprint: lem-sc-diagonal-conormal-derivation-core-exists). -/
theorem exists_diagonalConormalDerivation_core (f : X ⟶ S) :
    ∃ D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf,
      ∀ (U : X.Opens) (W : (pullback f f).Opens)
        (h₁ : W ≤ (pullback.fst f f) ⁻¹ᵁ U)
        (h₂ : W ≤ (pullback.snd f f) ⁻¹ᵁ U)
        (hδ : U ≤ (pullback.diagonal f) ⁻¹ᵁ W)
        (a : Γ(X, U)) (s : Γ(kernel (SheafOfModules.unitToPushforwardObjUnit
          (pullback.diagonal f).toRingCatSheafHom), W)),
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s =
            (pullback.snd f f).appLE U W h₂ a -
              (pullback.fst f f).appLE U W h₁ a →
        D.d (X := op U) a =
          (diagonalConormal f).presheaf.map (homOfLE hδ).op
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
              (pullback.diagonal f))).unit.app
                (kernel (SheafOfModules.unitToPushforwardObjUnit
                  (pullback.diagonal f).toRingCatSheafHom))).val.app (op W) s) := by
  sorry
end AlgebraicGeometry
