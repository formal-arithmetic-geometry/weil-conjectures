/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement
public import Mathlib.CategoryTheory.Localization.Bifunctor

/-!
# Canonical representative identifications for convolution localization

Source: Stacks Project, More on Algebra, Tag 0H7Y (proposition-kunneth-filtered),
with the convolution construction preceding Tag 0H7W and Derived Categories Tags
05S2--05S3 (blueprint: def-kun-filtered-tensor-representative-interface).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CochainComplex

namespace CochainComplex

variable {R : Type u} [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-! The following wrappers make the representative-to-homotopy passage explicit in the
statement below.  They are the canonical quotient maps, rather than choices of
representatives. -/

/-- A good filtered complex viewed as a finite filtered complex.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable abbrev kunnethFiniteRepresentative
    (P : KunnethFilteredComplex R) : FiniteFilteredModuleComplex R :=
  ⟨P.obj, P.property.1⟩

/-- The homotopy class of a good filtered complex in the good full subcategory.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable abbrev kunnethGoodRepresentative
    (P : KunnethFilteredComplex R) : GoodFiniteFilteredModuleHomotopy R :=
  ⟨(finiteFilteredModuleHomotopyQuotient R).obj (kunnethFiniteRepresentative P), P.property⟩

/-- A filtered chain map viewed in the finite filtered category.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable abbrev kunnethRepresentativeMap
    {P P' : KunnethFilteredComplex R} (f : P ⟶ P') :
    kunnethFiniteRepresentative P ⟶ kunnethFiniteRepresentative P' :=
  ObjectProperty.homMk f.hom

/-- The filtered homotopy class of a map of good representatives.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable abbrev kunnethGoodRepresentativeMap
    {P P' : KunnethFilteredComplex R} (f : P ⟶ P') :
    kunnethGoodRepresentative P ⟶ kunnethGoodRepresentative P' :=
  ObjectProperty.homMk
    ((finiteFilteredModuleHomotopyQuotient R).map (kunnethRepresentativeMap f))

/-- The convolution complex, with its supplied proof of goodness.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable abbrev kunnethConvolutionRepresentative
    (h : ∀ P Q : KunnethFilteredComplex R,
      HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    (P Q : KunnethFilteredComplex R) : KunnethFilteredComplex R :=
  ⟨kunnethConvolutionObject P.obj Q.obj, h P Q⟩

/-- The convolution chain map viewed in the good full subcategory.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable abbrev kunnethConvolutionRepresentativeMap
    (h : ∀ P Q : KunnethFilteredComplex R,
      HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    {P P' Q Q' : KunnethFilteredComplex R}
    (f : kunnethConvolutionObject P.obj Q.obj ⟶
      kunnethConvolutionObject P'.obj Q'.obj) :
    kunnethConvolutionRepresentative h P Q ⟶
      kunnethConvolutionRepresentative h P' Q' :=
  ObjectProperty.homMk f

/-- The image of a good representative under the replacement equivalence.
Source: Stacks, Tags 0H7X and 05S2, inclusion-induced equivalence
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable abbrev kunnethLocalizedRepresentative
    (E : (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (P : KunnethFilteredComplex R) : (finiteFilteredModuleQuasiIso R).Localization :=
  E.functor.obj ((goodFiniteFilteredModuleQuasiIso R).Q.obj (kunnethGoodRepresentative P))

/-- The canonical identification of a localized representative after forgetting or grading.
It is the composite of the inclusion square `eE`, the localization witness `hH`, the
representative object equality, and the ordinary quotient-to-derived-category comparison.
Source: Stacks, Tags 05S2 and 0H7Y, descent of forgetting and associated graded
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable def kunnethRepresentativeLiftIso
    (E : (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (eE : (goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ≅
      goodFiniteFilteredModuleInclusion R ⋙ (finiteFilteredModuleQuasiIso R).Q)
    (H : (finiteFilteredModuleQuasiIso R).Localization ⥤ DerivedCategory (ModuleCat.{u} R))
    (FH : FiniteFilteredModuleHomotopy R ⥤ DerivedCategory (ModuleCat.{u} R))
    (hH : Localization.Lifting (finiteFilteredModuleQuasiIso R).Q
      (finiteFilteredModuleQuasiIso R) FH H)
    (C : FiniteFilteredModuleHomotopy R → CochainComplex (ModuleCat.{u} R) ℤ)
    (hobj : ∀ K : FiniteFilteredModuleHomotopy R,
      FH.obj K = HomologicalComplexUpToQuasiIso.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj (C K)))
    (P : KunnethFilteredComplex R) :
    H.obj (kunnethLocalizedRepresentative E P) ≅
      DerivedCategory.Q.obj (C ((goodFiniteFilteredModuleInclusion R).obj
        (kunnethGoodRepresentative P))) :=
  H.mapIso (eE.app (kunnethGoodRepresentative P)) ≪≫
    (@Localization.Lifting.iso _ _ _ _ _ _
      (finiteFilteredModuleQuasiIso R).Q (finiteFilteredModuleQuasiIso R) FH H hH).app
        ((goodFiniteFilteredModuleInclusion R).obj (kunnethGoodRepresentative P)) ≪≫
    eqToIso (hobj ((goodFiniteFilteredModuleInclusion R).obj
      (kunnethGoodRepresentative P))) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app
      (C ((goodFiniteFilteredModuleInclusion R).obj (kunnethGoodRepresentative P)))

/-- The canonical convolution identification on a pair of localized representatives.
Transport by `τ`, then the inverse unit of `E` in each variable, then the bifunctor
localization witness `hB`, and finally the representative object equality. These fixed
composites prevent a free isomorphism from absorbing the comparison being characterized.
Source: Stacks, Tags 05S2--05S3 and the convolution before Tag 0H7W
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable def kunnethStarRepresentativeIso
    (E : (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (F : GoodFiniteFilteredModuleHomotopy R ⥤ GoodFiniteFilteredModuleHomotopy R ⥤
      (goodFiniteFilteredModuleQuasiIso R).Localization)
    (B : (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
      (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
      (goodFiniteFilteredModuleQuasiIso R).Localization)
    (hB : Localization.Lifting₂ (goodFiniteFilteredModuleQuasiIso R).Q
      (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
      (goodFiniteFilteredModuleQuasiIso R) F B)
    (hconv : ∀ P Q : KunnethFilteredComplex R,
      HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    (hrep : ∀ P Q : KunnethFilteredComplex R,
      (F.obj (kunnethGoodRepresentative P)).obj (kunnethGoodRepresentative Q) =
        (goodFiniteFilteredModuleQuasiIso R).Q.obj
          (kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv P Q)))
    (star : (finiteFilteredModuleQuasiIso R).Localization ⥤
      (finiteFilteredModuleQuasiIso R).Localization ⥤
      (finiteFilteredModuleQuasiIso R).Localization)
    (τ : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
      (star.obj U).obj V ≅
        E.functor.obj ((B.obj (E.inverse.obj U)).obj (E.inverse.obj V)))
    (P Q : KunnethFilteredComplex R) :
    (star.obj (kunnethLocalizedRepresentative E P)).obj
      (kunnethLocalizedRepresentative E Q) ≅
        kunnethLocalizedRepresentative E (kunnethConvolutionRepresentative hconv P Q) :=
  τ _ _ ≪≫ E.functor.mapIso
    (((B.mapIso (E.unitIso.symm.app
      ((goodFiniteFilteredModuleQuasiIso R).Q.obj (kunnethGoodRepresentative P)))).app
        (E.inverse.obj (kunnethLocalizedRepresentative E Q))) ≪≫
      (B.obj ((goodFiniteFilteredModuleQuasiIso R).Q.obj
        (kunnethGoodRepresentative P))).mapIso (E.unitIso.symm.app
          ((goodFiniteFilteredModuleQuasiIso R).Q.obj (kunnethGoodRepresentative Q))) ≪≫
      ((@Localization.Lifting₂.iso _ _ _ _ _ _ _ _ _ _
        (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R).Q
        (goodFiniteFilteredModuleQuasiIso R) (goodFiniteFilteredModuleQuasiIso R) F B hB).app
          (kunnethGoodRepresentative P)).app (kunnethGoodRepresentative Q) ≪≫
      eqToIso (hrep P Q))

/-- The graded comparison `e` supplied by `filteredTensor_graded_comparison`.
Its tensor-of-residue-classes equation uniquely determines this isomorphism; the
choice only postpones the proof of that canonical property, never the choice of a
mathematically unspecified object. In particular this is the dependency's `e`, rather
than an independently quantified isomorphism with the same endpoints.
Source: Stacks, convolution comparison preceding Tag 0H7W
(blueprint: def-kun-filtered-tensor-representative-interface). -/
noncomputable def kunnethRepresentativeGradedComparison
    (P Q : KunnethFilteredComplex R) (a : ℤ) :
    (∐ kunnethTensorGraded P.obj Q.obj a) ≅
      (kunnethConvolution P.obj Q.obj).gradedPiece a :=
  (filteredTensor_graded_comparison (R := R)).choose_spec.choose_spec.choose P Q a

end CochainComplex
