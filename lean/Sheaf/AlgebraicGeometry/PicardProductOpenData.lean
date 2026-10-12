module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.PicardH1MultipleLocus
import Sheaf.AlgebraicGeometry.PicardH1ProductInjective
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar

/-! Explicit-isomorphism form of the geometric Picard product openness construction.

Source: Stacks Project, More on Morphisms, Lemma pic-of-product, Tag 0BF3
(blueprint: lem-sc-picard-product-open-data).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The geometric construction returns explicit isomorphisms for both factors.
Source: Stacks Project, Tag 0BF3, Picard-locus construction.
The explicit-isomorphism output is the data-level form used to compose the auxiliary
module trivialization in `picard_product_open_core`.
(blueprint: lem-sc-picard-product-open-data). -/
theorem picard_product_open_data
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [Flat g] [IsProper g] [LocallyOfFinitePresentation g]
    (σ : S ⟶ X) (τ : S ⟶ Y)
    (hσ : σ ≫ f = 𝟙 S) (hτ : τ ≫ g = 𝟙 S)
    (s : S) (L : (pullback f g).Modules) [L.IsInvertible]
    (hO : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hO' : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd g t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (h₁ : Nonempty ((Scheme.Modules.tensorPullback
      (pullback.lift (𝟙 X) (f ≫ τ) (by simp [hτ]))).obj L ≅
        SheafOfModules.unit X.ringCatSheaf))
    (h₂ : Nonempty ((Scheme.Modules.tensorPullback
      (pullback.lift (g ≫ σ) (𝟙 Y) (by simp [hσ]))).obj L ≅
        SheafOfModules.unit Y.ringCatSheaf))
    (hs : Nonempty ((Scheme.Modules.tensorPullback
      ((pullback.fst f g ≫ f).fiberι s)).obj L ≅ SheafOfModules.unit _)) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ N : (pullback (pullback.fst f g ≫ f) U.ι).Modules,
      ∃ eL : (Scheme.Modules.tensorPullback
        (pullback.fst (pullback.fst f g ≫ f) U.ι)).obj L ≅ N,
      ∃ eN : N ≅ SheafOfModules.unit
        (pullback (pullback.fst f g ≫ f) U.ι).ringCatSheaf, True := by
  sorry

end AlgebraicGeometry.Scheme
