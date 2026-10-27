module

public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData
import Sheaf.AlgebraicGeometry.ResolutionCocycleAdjunctionClass

/-! # The cocycle class of raw resolution evaluation

Source: Stacks Project, Tags 03Q8 and 072W.
(blueprint: lem-weil-pbc-raw-restricted-resolution-class).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local instance] normalizationShiftedResolution_restriction_isKInjective
attribute [local irreducible] normalizationResolutionClass normalizationRestrictedIso
  RawRestrictedComparison.shiftIso normalizationResolutionCocycleIso
  RawRestrictedComparison.resolutionSectionsIso abelianHigherDirectImageClass

/-- The prescribed resolution evaluation represents the canonical derived-adjunction class.
Source: Stacks Project, Tags 072W, 0DVC and 09T5, termwise adjunction on an
injective representative and the associated-cohomology-presheaf construction.
(blueprint: lem-weil-pbc-raw-restricted-resolution-class).

Proof: By extensionality of abelian-group homomorphisms, it suffices to compare
the two maps at an arbitrary raw class z. Put A=f^{-1}Z[V] and let I be
the chosen injective resolution.
Compose z with the shifted augmentation F[0][q] -> Q(I)[q]. Since I[q] is
K-injective, localization and the homotopy quotient supply a chain representative
c:A[0] -> I[q]. Exact etale restriction preserves injectives, so the restricted
complex has the same resolution property. The resolution evaluation formula sends
c to the homology class of its value at the pulled-back identity generator.
The termwise normalizationSectionsIso identifies this value with the corresponding
section of I[q] over V times_S X. Undoing the shift gives its degree-q section
cocycle in the homology presheaf of f_*I.

Take the ordinary termwise adjunct c':Z[V][0] -> f_*I[q]. Its value at the
identity generator is exactly that same section cocycle, by the unit formula for
the ordinary adjunction. The factorization of the derived adjunction unit through
the ordinary unit identifies the derived adjunct of Q(c) with Q(c') followed by
the right-derived comparison. This follows by moving the localization comparison
through the unit using naturality and then applying the adjunction triangle
identity. Naturality with the augmentation gives the derived adjunct of z.

The definition of normalizationResolutionClass first sheafifies the homology
presheaf, uses exactness of sheafification to identify its homology, applies the
sheafification counit to the direct-image complex, and finally applies the two
augmentation-normalized derived-functor comparisons. On a section cocycle,
homology-map naturality with the cycle projection shows that the first three
factors give its class in the homology sheaf of f_*I. Hence this composite sends
the evaluated representative c to the degree-q class of c' at the identity generator,
with the prescribed augmentation comparison at the end.

Finally, applying H^0 to the derived adjunct of z and evaluating the generator
is the definition of abelianHigherDirectImageClass. The single-complex homology
comparison and the homology shift comparison identify H^0(Q(c')) evaluated at
the generator with the degree-q class of that generator's image in f_*I.
Their naturality with the derived-unit and augmentation comparisons gives the
same augmentation-normalized class just computed. The derived adjunction shift
compatibility uses these same shift comparisons, so their signs agree. Homotopic
representatives differ by boundaries, and both constructions send a boundary to
zero. This proves the formula for every z, including q=0 and empty charts. The value
of normalizationKappa is the canonical class by definition; extensionality gives
the asserted equality of homomorphisms. -/
theorem rawRestrictedResolution_class {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale) :
    rawRestrictedCohomologyComparison f q F V ≫ normalizationIota f q F V =
      (normalizationKappa f q F).app (op V) := by
  ext z
  let I := injectiveResolution F
  let J := normalizationShiftedResolution F I q
  let a := normalizationShiftedAugmentation F I q
  have : J.obj.IsKInjective := by
    change (I.cochainComplex⟦(q : ℤ)⟧).IsKInjective
    infer_instance
  let A := (CochainComplex.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V))
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ (.up ℤ)).obj A) J.obj).surjective
      (DerivedCategory.Plus.ι.map (z ≫ a.hom))
  obtain ⟨c, rfl⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective g
  let qc : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V)) ⟶
        DerivedCategory.Plus.Q.obj J := DerivedCategory.Plus.ι.preimage
          (X := (DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V)))
          (Y := DerivedCategory.Plus.Q.obj J) (DerivedCategory.Q.map c)
  have hc : qc = z ≫ a.hom := by
    apply DerivedCategory.Plus.ι.map_injective
    dsimp only [qc]
    rw [Functor.map_preimage]
    exact hg
  have hz : qc ≫ a.inv = z := by
    rw [hc]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (normalizationResolutionClass f q F I).app (op V)
    ((normalizationRestrictedIso f q F I V).hom
      (rawRestrictedCohomologyComparison f q F V z)) =
        abelianHigherDirectImageClass f q F V z
  rw [← hz]
  let W := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  let T := RawRestrictedComparison.sectionsFunctor W ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  let x := (RawRestrictedComparison.zeroIso W
    ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V))).inv
      (RawRestrictedComparison.generator f V)
  let zc := qc ≫ a.inv
  have ha : T.map a.hom (T.map zc x) =
      T.map (qc) x := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    simp only [zc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hs := ConcreteCategory.congr_hom
    (rawRestricted_resolution_shift_square f q F I V) (T.map zc x)
  simp only [ConcreteCategory.comp_apply] at hs
  change (normalizationRestrictedIso f q F I V).hom
      ((RawRestrictedComparison.shiftIso f q F V).hom (T.map zc x)) =
    (normalizationResolutionCocycleIso f q F I V).hom
      ((RawRestrictedComparison.resolutionSectionsIso W J).hom
        (T.map a.hom (T.map zc x))) at hs
  have he := RawRestrictedComparison.rawRestricted_resolution_evaluation f V J c
  change (RawRestrictedComparison.resolutionSectionsIso W J).hom (T.map qc x) =
    RawRestrictedComparison.chainEvaluation f V J.obj c at he
  have hv : (normalizationRestrictedIso f q F I V).hom
      (rawRestrictedCohomologyComparison f q F V zc) =
        (normalizationResolutionCocycleIso f q F I V).hom
          (RawRestrictedComparison.chainEvaluation f V J.obj c) := by
    change (normalizationRestrictedIso f q F I V).hom
      ((RawRestrictedComparison.shiftIso f q F V).hom (T.map zc x)) = _
    rw [hs, ha, he]
  change (normalizationResolutionClass f q F I).app (op V)
      ((normalizationRestrictedIso f q F I V).hom
        (rawRestrictedCohomologyComparison f q F V zc)) =
    abelianHigherDirectImageClass f q F V zc
  have hclass := resolutionCocycle_adjunction_class f q F I V c
  change (normalizationResolutionClass f q F I).app (op V)
      ((normalizationResolutionCocycleIso f q F I V).hom
        (RawRestrictedComparison.chainEvaluation f V J.obj c)) =
    abelianHigherDirectImageClass f q F V zc at hclass
  have hmap := congrArg
    (fun y : ((normalizationPresheafComplex f F I).homology (q : ℤ)).obj (op V) =>
      (normalizationResolutionClass f q F I).app (op V) y) hv
  exact Eq.trans hmap hclass

end AlgebraicGeometry.Etale
