/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Mathlib.CategoryTheory.Triangulated.Subcategory

import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Ambient realization of the constructible coefficient cocone

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-thm-sfb-qlbar-two-colimit/lem-sfb-constructible-cocone-obj.proof.md`,
Modules and Complexes paragraphs (blueprint: lem-sfb-constructible-cocone-ambient-realization).

All coefficients, predicates, categories, functors and cocone comparisons are the existing
ones. The ambient vertex functor is the specified vertex followed by the full inclusion.
Its comparison with termwise scalar extension is the canonical exact-derived comparison.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The specified cocone vertex functor followed by its full ambient inclusion.
Source: blueprint main-20261015, constructible-cocone-obj, Complexes paragraph
(blueprint: lem-sfb-constructible-cocone-ambient-realization). -/
noncomputable abbrev constructibleCoconeAmbientFunctor (E : FiniteIntermediateField ℓ) :
    PadicSubfieldConstructible X ℓ E ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) :=
  (constructibleCocone X ℓ).Φ E ⋙ (boundedConstructible (padicAlgClRingObj X ℓ)).ι

/-- The ambient vertex is the restriction of derived scalar extension, on objects and maps.
Source: blueprint main-20261015, constructible-cocone-obj, Complexes paragraph
(blueprint: lem-sfb-constructible-cocone-ambient-realization). -/
noncomputable def constructibleCoconeAmbientDerivedIso (E : FiniteIntermediateField ℓ) :
    constructibleCoconeAmbientFunctor X ℓ E ≅
      (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        derivedExtendScalarsToPadicAlgCl X ℓ E :=
  Iso.refl _

/-- The canonical realization by exact ordinary scalar extension applied termwise.
Source: blueprint main-20261015, constructible-cocone-obj, Complexes paragraph
(blueprint: lem-sfb-constructible-cocone-ambient-realization). -/
noncomputable def constructibleCoconeAmbientTermwiseIso (E : FiniteIntermediateField ℓ) :
    constructibleCoconeAmbientFunctor X ℓ E ≅
      (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory :=
  constructibleCoconeAmbientDerivedIso X ℓ E ≪≫
    Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
      (Mod.extendScalars
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorIsoMapDerivedCategory

/-- Integer shift comparison transported from exact termwise scalar extension.
Source: blueprint main-20261015, constructible-cocone-obj, Complexes paragraph
(blueprint: lem-sfb-constructible-cocone-ambient-realization). -/
noncomputable instance constructibleCoconeAmbientCommShift
    [TopologicalSpace.NoetherianSpace X] (E : FiniteIntermediateField ℓ) :
    (constructibleCoconeAmbientFunctor X ℓ E).CommShift ℤ :=
  Functor.CommShift.ofIso (constructibleCoconeAmbientTermwiseIso X ℓ E).symm ℤ

/-- The coefficient and category identifications with the archived condensed construction.
Source: blueprint main-20261015, constructible-cocone-obj, Modules paragraph
(blueprint: lem-sfb-constructible-cocone-ambient-realization).

Proof: the finite coefficient sheaf is continuous functions in the restricted norm topology;
the closure sheaf is continuous functions valued in one finite intermediate field. The point
pullback is the same sheafified left Kan extension followed by scheme inverse image
(def-sfb-padic-subfield-condensed-ring, sk-def-sfb-qlbar-condensed,
sk-def-sfb-pullback-from-point, def-weil-pbc-condensed-e-module-category). Thus the coefficient
rings and their pointwise operations coincide. The archived categories use exactly the same
boundedness and stratified local finite-presentation predicate, hence the same full subcategories
(def-sfb-dcons-subfield, def-sfb-dcons-qlbar, sk-def-sfb-bounded-constructible). -/
theorem constructibleCocone_coefficient_identifications :
    (∀ E : FiniteIntermediateField ℓ,
      padicSubfieldRingObj X ℓ E =
        (sfbPullbackFromPoint X).obj (Profinite.continuousMapRingObj E)) ∧
    padicAlgClRingObj X ℓ =
      (sfbPullbackFromPoint X).obj (Profinite.padicAlgClRingObj ℓ) ∧
    (∀ E : FiniteIntermediateField ℓ,
      PadicSubfieldConstructible X ℓ E =
        BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X)) ∧
    PadicAlgClConstructible X ℓ =
      BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) :=
  sorry

/-- Constructibility means stratified pro-etale local finite presentation, for both coefficients.
Source: blueprint main-20261015, constructible-cocone-obj, Modules paragraph
(blueprint: lem-sfb-constructible-cocone-ambient-realization).

Proof: unfold IsConstructibleModuleObject to obtain the finite locally closed stratification,
then IsLocallyFinitelyPresented to obtain the pro-etale cover of each stratum. On each cover
member Mod.IsFinitelyPresented is exactly a cokernel of a map of finite free modules
(def-sfb-constructible-module, def-sfb-locally-finitely-presented,
def-sfb-finitely-presented-module). These are the archived local presentations, without Tor
amplitude or completeness assumptions. The same argument applies to the specified closure ring. -/
theorem constructibleCocone_constructibility_identifications :
    (∀ (E : FiniteIntermediateField ℓ)
      (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E) M ↔
        ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
          ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a), ∀ i : 𝒰.I₀,
            Mod.IsFinitelyPresented
              ((upperStar Ab.{u + 1} (𝒰.f i)).obj
                ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj X ℓ E)))
              (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
                ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj X ℓ E))).obj
                (((upperStar Ab.{u + 1} (S.immersion a)).mapMod
                  (padicSubfieldRingObj X ℓ E)).obj M))) ∧
    (∀ M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ),
      IsConstructibleModuleObject (padicAlgClRingObj X ℓ) M ↔
        ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
          ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a), ∀ i : 𝒰.I₀,
            Mod.IsFinitelyPresented
              ((upperStar Ab.{u + 1} (𝒰.f i)).obj
                ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicAlgClRingObj X ℓ)))
              (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
                ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicAlgClRingObj X ℓ))).obj
                (((upperStar Ab.{u + 1} (S.immersion a)).mapMod
                  (padicAlgClRingObj X ℓ)).obj M))) :=
  sorry

/-- The finite stages inherit triangles and additive integer shifts, and their ambient vertex
functors are triangulated with the canonical termwise realization.
Source: blueprint main-20261015, constructible-cocone-obj, Complexes paragraph
(blueprint: lem-sfb-constructible-cocone-ambient-realization).

Proof: lem-weil-pbc-condensed-constructible-serre gives kernel, cokernel and extension closure
for finite coefficients on the given topologically Noetherian scheme. Zero uses the zero finite
presentation, with the empty stratification on the empty scheme; presentations transport across
isomorphisms. The conditional bounded-constructible criterion and
def-weil-triangulated-subcategory give inherited triangles and a triangulated inclusion.
Ambient complex shifts preserve addition, as do their restrictions. By lem-sfb-qlbar-flat and
sk-def-sfb-change-of-scalars, ordinary extension is exact; lem-sfb-preserving-colimits-additive
gives additivity. def-sfb-left-derived-exact identifies its derived extension with the termwise
functor, triangulated by lem-sf-exact-functor-derived-triangulated. The specified cocone vertex
is its restriction by lem-sfb-extend-to-qlbar-constructible and
def-sfb-constructible-extend-to-qlbar. Its ambient composite therefore preserves triangles,
and the transported shift structure makes the canonical realization compatible with shifts.
No triangulated structure on the closure constructible category is required. -/
theorem constructibleCocone_ambient_triangulated [TopologicalSpace.NoetherianSpace X]
    (E : FiniteIntermediateField ℓ) :
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated ∧
    (∀ n : ℤ, (shiftFunctor (PadicSubfieldConstructible X ℓ E) n).Additive) ∧
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.IsTriangulated ∧
    (constructibleCoconeAmbientFunctor X ℓ E).IsTriangulated ∧
    NatTrans.CommShift (constructibleCoconeAmbientTermwiseIso X ℓ E).hom ℤ :=
  sorry

/-- The actual forward and inverse cocone comparisons become the restricted tensor comparisons.
Source: blueprint main-20261015, constructible-cocone-obj, Complexes paragraph
(blueprint: lem-sfb-constructible-cocone-ambient-realization).

Proof: def-sfb-constructible-extend-subfield restricts ambient scalar extension. The specified
cocone comparison is def-sfb-constructible-extend-comp-iso, obtained by full faithfulness from
def-sfb-derived-extend-comp-iso. Applying the full inclusion to its forward and inverse
components gives those ambient components, evaluated on the underlying complex; naturality is
the identical equation in the full subcategory and ambient category. -/
theorem constructibleCocone_ambient_comparisons {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) (K : PadicSubfieldConstructible X ℓ E) :
    (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map
        (((constructibleCocone X ℓ).iso h).hom.app K) =
      (derivedExtendScalarsCompIso X ℓ h).hom.app K.obj ∧
    (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map
        (((constructibleCocone X ℓ).iso h).inv.app K) =
      (derivedExtendScalarsCompIso X ℓ h).inv.app K.obj :=
  sorry

end AlgebraicGeometry.ProEtale
