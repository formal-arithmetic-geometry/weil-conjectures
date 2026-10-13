module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel

@[expose] public section

universe u
open CategoryTheory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

/-- Transport a model's localization comparison through an isomorphism to a shifted complex.
Source: Stacks Project, Tags 06Y6 and 08IB, with the shift argument of Tag 0DJA(1).

Proof: retain the derived functor, counit and universal property of mK. Extension of
scalars on homotopy categories commutes with integer shifts. Uniqueness in the left-derived
universal property therefore gives the derived shift isomorphism compatible with the counit.
Set the new cohomology in degree j to mK.cohomology (j-n). Define cohomologyIso using
restriction of e, the derived shift isomorphism and the homology shift isomorphism.
Naturality of these maps in multiplication by a in A proves cohomologyIso_smul, while
B-linearity preserves the other tensor-algebra action. Transport ordinaryIso along e
and the termwise scalar-extension shift maps; its tensor formula follows on generators.
Construct ordinaryToLocalized by its coefficient map on tensors. Define comparison by
the counit equation and the transported cohomologyIso. Naturality in multiplication by
A makes this map tensor-algebra linear, and the transported ordinaryIso proves comparison_eq.
Define localizedComparison by transposing comparison followed by the coefficient map through
extension/restriction adjunction. This proves localized_eq. Thus all model data are explicit
constructions from mK, e and the uniquely determined derived shift map. At j=i+n, reindexing
identifies the source with mK.cohomology i; extension to C gives eS. The counit shift equation,
comparison_eq and localized_eq give the displayed equation with the prescribed homology
shift map. No arbitrary existence witness is chosen. The construction works for n=0,
zero complexes and any complex isomorphism e, without flatness hypotheses.
(blueprint: lem-pc-localized-tensor-comparison-shift-square-data). -/
theorem exists_shift_square_data
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (e : L ≅ K⟦-n⟧)
    (mK : BaseDerivedTensorCohomologyModel R A B K C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let eH := (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) (i + n)).mapIso
      (F.mapIso e ≪≫ (F.commShiftIso (-n)).app K) ≪≫
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C) (-n) (i + n) i
        (by omega)).app (F.obj K)
    ∃ (mL : BaseDerivedTensorCohomologyModel R A B L C)
      (eS : (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mL.cohomology (i + n)) ≅
        (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mK.cohomology i)),
    mK.localizedComparison i = eS.inv ≫ mL.localizedComparison (i + n) ≫ eH.hom := by
  sorry

end ModuleCat
