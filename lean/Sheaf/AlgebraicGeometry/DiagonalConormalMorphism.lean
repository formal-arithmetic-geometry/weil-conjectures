module

public import Sheaf.AlgebraicGeometry.DiagonalConormal
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The sheaf morphism underlying the normalized difference derivation.
Source: Stacks Project, Tag 08S2. Construct the morphism from the universal relative
 differential sheaf by the difference of the two splittings of the square-zero diagonal
 extension; the local kernel calculation gives the displayed normalization.
(blueprint: lem-sc-diagonal-conormal-morphism-exists). -/
theorem exists_diagonalConormalMorphism (f : X ⟶ S) :
    ∃ φ : f.relativeDifferentials ⟶ diagonalConormal f,
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
        (f.relativeDifferentialsDerivation.postcomp φ.val).d (X := op U) a =
          (diagonalConormal f).presheaf.map (homOfLE hδ).op
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
              (pullback.diagonal f))).unit.app
                (kernel (SheafOfModules.unitToPushforwardObjUnit
                  (pullback.diagonal f).toRingCatSheafHom))).val.app (op W) s) := by
  sorry

end AlgebraicGeometry
