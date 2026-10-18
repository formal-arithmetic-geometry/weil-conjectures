/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement
public import Sheaf.Algebra.Homology.FilteredTensorGradedComparison
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Mathlib.CategoryTheory.Localization.Bifunctor
import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy

/-!
# Convolution tensor on the finite filtered localization

Source: Stacks Project, More on Algebra, Tag 0H7Y (proposition-kunneth-filtered),
with the convolution construction preceding Tag 0H7W and Derived Categories Tags
05S2--05S3 (blueprint: lem-kun-filtered-tensor-localization).
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
(blueprint: lem-kun-filtered-tensor-localization). -/
noncomputable def kunnethFiniteRepresentative
    (P : KunnethFilteredComplex R) : FiniteFilteredModuleComplex R :=
  ⟨P.obj, P.property.1⟩

/-- The homotopy class of a good filtered complex in the good full subcategory.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: lem-kun-filtered-tensor-localization). -/
noncomputable def kunnethGoodRepresentative
    (P : KunnethFilteredComplex R) : GoodFiniteFilteredModuleHomotopy R :=
  ⟨(finiteFilteredModuleHomotopyQuotient R).obj (kunnethFiniteRepresentative P), P.property⟩

/-- A filtered chain map viewed in the finite filtered category.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: lem-kun-filtered-tensor-localization). -/
noncomputable def kunnethRepresentativeMap
    {P P' : KunnethFilteredComplex R} (f : P ⟶ P') :
    kunnethFiniteRepresentative P ⟶ kunnethFiniteRepresentative P' :=
  ObjectProperty.homMk f.hom

/-- The filtered homotopy class of a map of good representatives.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: lem-kun-filtered-tensor-localization). -/
noncomputable def kunnethGoodRepresentativeMap
    {P P' : KunnethFilteredComplex R} (f : P ⟶ P') :
    kunnethGoodRepresentative P ⟶ kunnethGoodRepresentative P' :=
  ObjectProperty.homMk
    ((finiteFilteredModuleHomotopyQuotient R).map (kunnethRepresentativeMap f))

/-- The convolution complex, with its supplied proof of goodness.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: lem-kun-filtered-tensor-localization). -/
noncomputable def kunnethConvolutionRepresentative
    (h : ∀ P Q : KunnethFilteredComplex R,
      HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    (P Q : KunnethFilteredComplex R) : KunnethFilteredComplex R :=
  ⟨kunnethConvolutionObject P.obj Q.obj, h P Q⟩

/-- The convolution chain map viewed in the good full subcategory.
Source: Stacks, Tags 0H7W and 05S2, representative passage in localization
(blueprint: lem-kun-filtered-tensor-localization). -/
noncomputable def kunnethConvolutionRepresentativeMap
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
(blueprint: lem-kun-filtered-tensor-localization). -/
noncomputable def kunnethLocalizedRepresentative
    (E : (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (P : KunnethFilteredComplex R) : (finiteFilteredModuleQuasiIso R).Localization :=
  E.functor.obj ((goodFiniteFilteredModuleQuasiIso R).Q.obj (kunnethGoodRepresentative P))

/-- The canonical identification of a localized representative after forgetting or grading.
It is the composite of the inclusion square `eE`, the localization witness `hH`, the
representative object equality, and the ordinary quotient-to-derived-category comparison.
Source: Stacks, Tags 05S2 and 0H7Y, descent of forgetting and associated graded
(blueprint: lem-kun-filtered-tensor-localization). -/
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
(blueprint: lem-kun-filtered-tensor-localization). -/
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
(blueprint: lem-kun-filtered-tensor-localization). -/
noncomputable def kunnethRepresentativeGradedComparison
    (P Q : KunnethFilteredComplex R) (a : ℤ) :
    (∐ kunnethTensorGraded P.obj Q.obj a) ≅
      (kunnethConvolution P.obj Q.obj).gradedPiece a :=
  (filteredTensor_graded_comparison (R := R)).choose_spec.choose_spec.choose P Q a

/-- The convolution tensor descends through filtered homotopy localizations, and its
underlying and associated-graded comparisons are natural in both localized variables.
Source: Stacks Project, More on Algebra, Tags 0H7W and 0H7Y, and Derived Categories
Tags 05S2--05S3 (blueprint: lem-kun-filtered-tensor-localization).

Proof sketch (the nine steps of the node):
1. On good representatives, `filteredTensor_graded_comparison` constructs the signed
   total tensor with convolution filtration, proves goodness, and fixes `m`, `e`, `c`,
   and `cgr` by their representative equations.
2. Tensoring filtered homotopies gives filtered homotopies; the mixed Koszul terms cancel,
   so the representative operation descends to the homotopy category.
3. The graded comparison shows that the operation inverts a graded quasi-isomorphism in
   either variable, hence it inverts the product class of denominators.
4. The product localization universal property supplies `B`; its `Lifting₂` witness
   records the canonical comparison with representatives.
5. The replacement theorem supplies `E` and its natural square with inclusion; transport
   across this equivalence gives `star`.
6. The family `τ` below is natural in both localized variables, so `star` is fixed by the
   transported representative bifunctor rather than objectwise choices.
7. Forgetting and grading invert denominators by finite filtration induction and by
   definition; their `Lifting` witnesses characterize `omega` and `gr`.
8. The fixed derived tensor comparison `c` descends to the natural underlying comparison
   `eta`, agreeing with tensoring representative maps.
9. The fixed `e` and `cgr` comparisons descend uniformly to finite diagonal biproducts;
   common finite support gives the final graded naturality square.
-/
theorem filteredTensor_localization :
    ∃ (E :
        (goodFiniteFilteredModuleQuasiIso R).Localization ≌
          (finiteFilteredModuleQuasiIso R).Localization),
      ∃ (eE :
        (goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ≅
          goodFiniteFilteredModuleInclusion R ⋙ (finiteFilteredModuleQuasiIso R).Q),
      ∃ (F :
        GoodFiniteFilteredModuleHomotopy R ⥤
          GoodFiniteFilteredModuleHomotopy R ⥤
            (goodFiniteFilteredModuleQuasiIso R).Localization),
        ∃ (B :
          (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
            (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
              (goodFiniteFilteredModuleQuasiIso R).Localization),
          ∃ hB : Localization.Lifting₂
            (goodFiniteFilteredModuleQuasiIso R).Q
            (goodFiniteFilteredModuleQuasiIso R).Q
            (goodFiniteFilteredModuleQuasiIso R)
            (goodFiniteFilteredModuleQuasiIso R) F B,
            ∃ (hconv : ∀ P Q : KunnethFilteredComplex R,
              HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj)),
            ∃ (conv : GoodFiniteFilteredModuleHomotopy R →
              GoodFiniteFilteredModuleHomotopy R → GoodFiniteFilteredModuleHomotopy R),
              (∀ P Q : GoodFiniteFilteredModuleHomotopy R,
                (F.obj P).obj Q = (goodFiniteFilteredModuleQuasiIso R).Q.obj (conv P Q)) ∧
              (∀ P Q : GoodFiniteFilteredModuleHomotopy R,
                (conv P Q).obj.as.obj = kunnethConvolutionObject P.obj.as.obj Q.obj.as.obj) ∧
              (∃ (hrep : ∀ P Q : KunnethFilteredComplex R,
                  (F.obj (kunnethGoodRepresentative P)).obj (kunnethGoodRepresentative Q) =
                    (goodFiniteFilteredModuleQuasiIso R).Q.obj
                      (kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv P Q))),
              ∃ (m : ∀ (P P' Q Q' : KunnethFilteredComplex R)
                    (f : P ⟶ P') (g : Q ⟶ Q'),
                  kunnethConvolutionObject P.obj Q.obj ⟶
                    kunnethConvolutionObject P'.obj Q'.obj),
                (∀ (P P' Q Q' : KunnethFilteredComplex R)
                    (f : P ⟶ P') (g : Q ⟶ Q'),
                  (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom) ∧
                (∀ P Q : KunnethFilteredComplex R,
                  m P P Q Q (𝟙 P) (𝟙 Q) = 𝟙 _) ∧
                (∀ (P P' P'' Q Q' Q'' : KunnethFilteredComplex R)
                    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q''),
                  m P P'' Q Q'' (f ≫ f') (g ≫ g') =
                    m P P' Q Q' f g ≫ m P' P'' Q' Q'' f' g') ∧
              (∀ (P P' Q Q' : KunnethFilteredComplex R)
                  (f : P ⟶ P') (g : Q ⟶ Q'),
                (F.map (kunnethGoodRepresentativeMap f)).app
                      (kunnethGoodRepresentative Q) ≫
                    (F.obj (kunnethGoodRepresentative P')).map
                      (kunnethGoodRepresentativeMap g) =
                  eqToHom (hrep P Q) ≫
                    (goodFiniteFilteredModuleQuasiIso R).Q.map
                      (kunnethGoodRepresentativeMap
                        (kunnethConvolutionRepresentativeMap hconv
                          (m P P' Q Q' f g))) ≫
                    eqToHom (hrep P' Q').symm) ∧
              ∃ (star :
                (finiteFilteredModuleQuasiIso R).Localization ⥤
                  (finiteFilteredModuleQuasiIso R).Localization ⥤
                    (finiteFilteredModuleQuasiIso R).Localization),
                ∃ (τ : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
                  (star.obj U).obj V ≅
                    E.functor.obj ((B.obj (E.inverse.obj U)).obj (E.inverse.obj V))),
                  (∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
                      (f : U ⟶ U') (g : V ⟶ V'),
                    (τ U V).hom ≫
                        E.functor.map ((B.map (E.inverse.map f)).app (E.inverse.obj V) ≫
                          (B.obj (E.inverse.obj U')).map (E.inverse.map g)) =
                      (star.map f).app V ≫ (star.obj U').map g ≫ (τ U' V').hom) ∧
                  ∃ (omega :
                    (finiteFilteredModuleQuasiIso R).Localization ⥤
                      DerivedCategory (ModuleCat.{u} R)),
                    ∃ (Fω : FiniteFilteredModuleHomotopy R ⥤
                      DerivedCategory (ModuleCat.{u} R)),
                      ∃ hω : Localization.Lifting
                        (finiteFilteredModuleQuasiIso R).Q
                        (finiteFilteredModuleQuasiIso R)
                        Fω omega,
                        ∃ (hωobj : ∀ K : FiniteFilteredModuleHomotopy R,
                          Fω.obj K =
                            HomologicalComplexUpToQuasiIso.Qh.obj
                              ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                                K.as.obj.obj)),
                          (∀ (K L : FiniteFilteredModuleHomotopy R)
                              (f : K.as ⟶ L.as),
                            Fω.map ((finiteFilteredModuleHomotopyQuotient R).map f) =
                              eqToHom (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
                                HomologicalComplexUpToQuasiIso.Qh.map
                                  ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                                    f.hom.hom) ≫
                                eqToHom
                                  (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm
                                  ) ∧
                          ∃ (gr : ℤ →
                          (finiteFilteredModuleQuasiIso R).Localization ⥤
                            DerivedCategory (ModuleCat.{u} R)),
                          ∃ (Fgr : ∀ a : ℤ, FiniteFilteredModuleHomotopy R ⥤
                            DerivedCategory (ModuleCat.{u} R)),
                            ∃ hgr : ∀ a : ℤ, Localization.Lifting
                              (finiteFilteredModuleQuasiIso R).Q
                              (finiteFilteredModuleQuasiIso R)
                              (Fgr a) (gr a),
                              ∃ (hgro : ∀ (a : ℤ) (K : FiniteFilteredModuleHomotopy R),
                                (Fgr a).obj K =
                                  HomologicalComplexUpToQuasiIso.Qh.obj
                                    ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                                      (K.as.obj.filtration.gradedPiece a))),
                                (∀ (a : ℤ) (K L : FiniteFilteredModuleHomotopy R)
                                    (f : K.as ⟶ L.as),
                                  (Fgr a).map ((finiteFilteredModuleHomotopyQuotient R).map f) =
                                    eqToHom
                                      (hgro a ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
                                      HomologicalComplexUpToQuasiIso.Qh.map
                                        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                                          (FilteredObject.gradedMapSteps f.hom a)) ≫
                                      eqToHom
                                        (hgro a
                                          ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm
                                      ) ∧
                                (∃ η : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
                                omega.obj ((star.obj U).obj V) ≅
                                  (omega.obj U) ⊗ (omega.obj V),
                                (∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
                                    (f : U ⟶ U') (g : V ⟶ V'),
                                  (η U V).hom ≫ (omega.map f ⊗ₘ omega.map g) =
                                    omega.map ((star.map f).app V ≫
                                      (star.obj U').map g) ≫ (η U' V').hom) ∧
                                ∃ (cη : ∀ P Q : KunnethFilteredComplex R,
                                  DerivedCategory.Q.obj P.obj.obj ⊗
                                      DerivedCategory.Q.obj Q.obj.obj ≅
                                    DerivedCategory.Q.obj (P.obj.obj ⊗ Q.obj.obj)),
                                  (∀ P Q : KunnethFilteredComplex R,
                                    (cη P Q).hom = Functor.LaxMonoidal.μ
                                      DerivedCategory.Q P.obj.obj Q.obj.obj) ∧
                                  (∀ P Q : KunnethFilteredComplex R,
                                    (η (kunnethLocalizedRepresentative E P)
                                      (kunnethLocalizedRepresentative E Q)).hom ≫
                                      ((kunnethRepresentativeLiftIso E eE omega Fω hω
                                        (fun K ↦ K.as.obj.obj) hωobj P).hom ⊗ₘ
                                      (kunnethRepresentativeLiftIso E eE omega Fω hω
                                        (fun K ↦ K.as.obj.obj) hωobj Q).hom) =
                                    omega.map
                                      (kunnethStarRepresentativeIso E F B hB hconv hrep
                                        star τ P Q).hom ≫
                                      (kunnethRepresentativeLiftIso E eE omega Fω hω
                                        (fun K ↦ K.as.obj.obj) hωobj
                                        (kunnethConvolutionRepresentative hconv P Q)).hom ≫
                                      (cη P Q).inv)) ∧
                              ∃ (e : ∀ (a : ℤ)
                                  (U V : (finiteFilteredModuleQuasiIso R).Localization)
                                  (s : Finset ℤ),
                                  (∀ i : ℤ, i ∉ s →
                                    IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))) →
                                  ((gr a).obj ((star.obj U).obj V) ≅
                                    (⨁ fun i : ↥s =>
                                      ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V)))),
                                (∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization),
                                  ∃ s : Finset ℤ,
                                    (∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))) ∧
                                (∀ (a : ℤ)
                                    (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
                                    (f : U ⟶ U') (g : V ⟶ V') (s : Finset ℤ)
                                    (hs : ∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))
                                    (hs' : ∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj U') ⊗ ((gr (a - i)).obj V'))),
                                  (e a U V s hs).hom ≫ biproduct.map (fun i : ↥s =>
                                    (gr i.1).map f ⊗ₘ (gr (a - i.1)).map g) =
                                    (gr a).map ((star.map f).app V ≫
                                      (star.obj U').map g) ≫ (e a U' V' s hs').hom)
                                ∧ (∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization)
                                    (s t : Finset ℤ) (hst : s ⊆ t)
                                    (hs : ∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))
                                    (ht : ∀ i : ℤ, i ∉ t →
                                      IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))),
                                  ∃ (ι :
                                      (⨁ fun i : ↥s =>
                                        ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V)) ⟶
                                      (⨁ fun i : ↥t =>
                                        ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V))),
                                    (∀ i : ↥s,
                                      biproduct.ι (fun j : ↥s =>
                                        ((gr j.1).obj U) ⊗ ((gr (a - j.1)).obj V)) i ≫ ι =
                                      biproduct.ι (fun j : ↥t =>
                                        ((gr j.1).obj U) ⊗ ((gr (a - j.1)).obj V))
                                        ⟨i.1, hst i.2⟩) ∧
                                    (e a U V s hs).hom ≫ ι =
                                      (e a U V t ht).hom)
                                ∧ (∀ (P Q : KunnethFilteredComplex R) (a : ℤ)
                                    (s : Finset ℤ)
                                    (hs : ∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj (kunnethLocalizedRepresentative E P)) ⊗
                                        ((gr (a - i)).obj (kunnethLocalizedRepresentative E Q)))),
                                  ∃ (cgr : ∀ i : ℤ,
                                    kunnethDerivedGraded P.obj Q.obj a i ≅
                                      DerivedCategory.Q.obj
                                        (kunnethTensorGraded P.obj Q.obj a i)),
                                  (∀ i : ℤ, (cgr i).hom =
                                    Functor.LaxMonoidal.μ DerivedCategory.Q
                                      (P.obj.filtration.gradedPiece i)
                                      (Q.obj.filtration.gradedPiece (a - i))) ∧
                                  (e a (kunnethLocalizedRepresentative E P)
                                      (kunnethLocalizedRepresentative E Q) s hs).hom ≫
                                    biproduct.desc (fun i : ↥s ↦
                                      ((kunnethRepresentativeLiftIso E eE (gr i.1) (Fgr i.1)
                                        (hgr i.1) (fun K ↦ K.as.obj.filtration.gradedPiece i.1)
                                        (hgro i.1) P).hom ⊗ₘ
                                      (kunnethRepresentativeLiftIso E eE (gr (a - i.1))
                                        (Fgr (a - i.1)) (hgr (a - i.1))
                                        (fun K ↦ K.as.obj.filtration.gradedPiece (a - i.1))
                                        (hgro (a - i.1)) Q).hom) ≫
                                      (cgr i.1).hom ≫ DerivedCategory.Q.map
                                        (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i.1)) =
                                    (gr a).map
                                      (kunnethStarRepresentativeIso E F B hB hconv hrep
                                        star τ P Q).hom ≫
                                    (kunnethRepresentativeLiftIso E eE (gr a) (Fgr a) (hgr a)
                                      (fun K ↦ K.as.obj.filtration.gradedPiece a) (hgro a)
                                      (kunnethConvolutionRepresentative hconv P Q)).hom ≫
                                    (DerivedCategory.Q.mapIso
                                      (kunnethRepresentativeGradedComparison P Q a)).inv))
              := by
  sorry

end CochainComplex
