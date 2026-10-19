module

public import Sheaf.RingTheory.StablyFreeComplexLift
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.RingTheory.RingPseudoCoherent
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

@[expose] public section
set_option autoImplicit false
universe u v w w'
open CategoryTheory
namespace DerivedCategory

/-- The unmarked finite-free lifting data needed before checking the prescribed marking.
Source: Stacks Project, More on Algebra, Tags 0H76 and 0BCB.
(blueprint: lem-weil-pbc-nilpotent-marked-free-complex-lift-unmarked)
The construction first lifts a bounded-above finite-free model through the nilpotent
quotient, retaining the upper bound and finite freeness. The remaining compatibility
with the prescribed derived marking is a separate comparison argument.
-/
theorem exists_unmarked_finiteFree_lift_of_nilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hnil : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = 0)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} (R ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (F : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) (hFbound : F.IsStrictlyLE b)
    (hFterms : ∀ i : ℤ, Module.Free (R ⧸ I) (F.X i) ∧ Module.Finite (R ⧸ I) (F.X i))
    (α : L.obj K ≅ Q.obj F) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β : Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) := by
  sorry

end DerivedCategory
