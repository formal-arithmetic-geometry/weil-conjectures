/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.OrdinaryFlatCoefficientComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Flat coefficient comparison and derived reduction adjuncts

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 0D6D and 07A6;
sites-modules.tex, Tag 05V4
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct).

The presentations and their normalization are the existing K-flat derived scalar
extensions, not new choices of tensor products or adjunctions. Tensor formulas below
use the scalar-first convention: the paper's `x ⊗ s` is `sectionTensor ... s x`.
The ordinary and derived comparisons are specified together, including their descent
through the universal counits, so the assertion fixes the canonical balanced maps.

## Main definitions

- `flatCoefficientMultiplication`: the normalized multiplication map.
- `flatCoefficientChange`: the canonical coefficient-change arrow.
- `flatCoefficientUnit`: the canonical scalar-extension unit identification.
- `FlatCoefficientReductionComparison`: the fully normalized comparison interface.

## Main statements

- `flat_coefficient_reduction_adjunct`: the comparison and all its compatibilities.
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

universe u v r w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
open SheafOfModules.SuccessiveDerivedQuotient

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [hD : ∀ A : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules A)]
  (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
  (N : Normalization p)
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)

/-- The multiplication `B ⊗_R S → S`, as a morphism of B-module sheaves.
The normalized ordinary counit sends `b ⊗ s` to `ψ(b)s`.
Source: Stacks 05V4 and 07A6
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct). -/
noncomputable def flatCoefficientMultiplication {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) :
    (p φ).ordinary.obj ((restriction φ).obj
      ((restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S)))) ⟶
      (restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S)) :=
  (N.ordinaryAdjunction φ).counit.app
    ((restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S)))

/-- Coefficient change `X ⊗^L_A S → Res(X ⊗^L_A T)` for `S → T`.
This is the normalized extension unit followed by the canonical associator.
Source: Stacks 0D6D and 07A6
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct). -/
noncomputable def flatCoefficientChange {A S T : Sheaf J CommRingCat.{r}}
    (a : A ⟶ S) (τ : S ⟶ T) (X : DerivedCategory (Modules A)) :
    (p a).derived.obj X ⟶ (N.right τ).obj ((p (a ≫ τ)).derived.obj X) :=
  (N.adjunction τ).unit.app ((p a).derived.obj X) ≫
    (N.right τ).map ((N.derived a τ).hom.app X)

/-- The scalar-extension unit identification on `X ⊗^L_A S`.
Its flat-model formula is `(x ⊗ s) ⊗ t ↦ x ⊗ st`, since the associator
is normalized by that formula and `a ≫ 𝟙 S = a`.
Source: Stacks 0D6D, identity-map case
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct). -/
noncomputable def flatCoefficientUnit {A S : Sheaf J CommRingCat.{r}}
    (a : A ⟶ S) (X : DerivedCategory (Modules A)) :
    (p (𝟙 S)).derived.obj ((p a).derived.obj X) ⟶ (p a).derived.obj X :=
  (N.derived a (𝟙 S)).hom.app X ≫
    eqToHom (congrArg (fun b ↦ (p b).derived.obj X) (Category.comp_id a))

/-- The canonical balanced comparison, with its K-flat representative, all derived
adjuncts, coefficient naturality, and successive-extension and unit normalizations.
All maps in the coherence clauses are the existing normalized scalar maps.
Source: Stacks 0G7E, 0D6D, 07A6 and 05V4
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct). -/
structure FlatCoefficientReductionComparison where
  /-- The ordinary balanced comparison, natural in the B-module. -/
  ordinary : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (_hμ : IsIso (flatCoefficientMultiplication p N φ ψ)),
    restriction φ ⋙ (p (φ ≫ ψ)).ordinary ≅ (p ψ).ordinary
  /-- Its actual formula on sheafified pure tensors. -/
  ordinary_pure : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (M : Modules B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
    ((ordinary ψ hμ).hom.app M).val.app U
        (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x) =
      sectionTensor (p ψ) M U s x
  /-- The comparison in D(S), natural in every derived B-module. -/
  derived : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (_hμ : IsIso (flatCoefficientMultiplication p N φ ψ)),
    N.right φ ⋙ (p (φ ≫ ψ)).derived ≅ (p ψ).derived
  /-- The restricted flat-term K-flat model computes the R-side. -/
  restricted_computed : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (P : CochainComplex (Modules B) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
    IsIso ((p (φ ≫ ψ)).counit.app
      (((restriction φ).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)))
  /-- The derived map is represented by the displayed ordinary balanced map. -/
  representative : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (P : CochainComplex (Modules B) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
    (derived ψ hμ).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p ψ).counit.app ((HomotopyCategory.quotient _ _).obj P) =
    (p (φ ≫ ψ)).derived.map
        ((N.right_factors φ).hom.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p (φ ≫ ψ)).counit.app
        (((restriction φ).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (ordinary ψ hμ) (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj P))
  /-- Adjuncts of arbitrary derived morphisms agree under the comparison. -/
  adjunct : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (M : DerivedCategory (Modules B)) (Q : DerivedCategory (Modules S))
    (f : M ⟶ (N.right ψ).obj Q),
    ((N.adjunction (φ ≫ ψ)).homEquiv _ _).symm
        ((N.right φ).map f ≫ (N.rightComp φ ψ).hom.app Q) =
      (derived ψ hμ).hom.app M ≫ ((N.adjunction ψ).homEquiv M Q).symm f
  /-- Naturality for a morphism S → S', with the arrows restricted to D(S). -/
  coefficient_naturality : ∀ {S S' : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) (τ : S ⟶ S')
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (hμ' : IsIso (flatCoefficientMultiplication p N φ (ψ ≫ τ)))
    (M : DerivedCategory (Modules B)),
    flatCoefficientChange p N (φ ≫ ψ) τ ((N.right φ).obj M) ≫
        (N.right τ).map
          (eqToHom (congrArg (fun a ↦ (p a).derived.obj ((N.right φ).obj M))
            (Category.assoc φ ψ τ)) ≫ (derived (ψ ≫ τ) hμ').hom.app M) =
      (derived ψ hμ).hom.app M ≫ flatCoefficientChange p N ψ τ M
  /-- Compatibility with successive derived extension under the canonical associators.
  Together with N.associative, this includes every finite iteration. -/
  successive : ∀ {S S' : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S) (τ : S ⟶ S')
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (hμ' : IsIso (flatCoefficientMultiplication p N φ (ψ ≫ τ)))
    (M : DerivedCategory (Modules B)),
    (p τ).derived.map ((derived ψ hμ).hom.app M) ≫ (N.derived ψ τ).hom.app M =
      (N.derived (φ ≫ ψ) τ).hom.app ((N.right φ).obj M) ≫
        eqToHom (congrArg (fun a ↦ (p a).derived.obj ((N.right φ).obj M))
          (Category.assoc φ ψ τ)) ≫ (derived (ψ ≫ τ) hμ').hom.app M
  /-- The equal-index case uses the canonical scalar-extension unit identification. -/
  equal_index : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (M : DerivedCategory (Modules B)),
    (p (𝟙 S)).derived.map ((derived ψ hμ).hom.app M) ≫ flatCoefficientUnit p N ψ M =
      flatCoefficientUnit p N (φ ≫ ψ) ((N.right φ).obj M) ≫ (derived ψ hμ).hom.app M

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.MonoidalCategory
attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem restriction_exact {A S : Sheaf J CommRingCat.{r}} (a : A ⟶ S) :
    PreservesFiniteLimits (restriction a) ∧ PreservesFiniteColimits (restriction a) := by
  obtain ⟨hl, hc, _⟩ := sheafRingDerivedCoefficientAdjunction a
  exact ⟨hl, hc⟩

private theorem restricted_flat_models
    (hflat : exactFunctor (Modules R) (Modules B) (p φ).ordinary)
    (P : CochainComplex (Modules B) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
        (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ i : ℤ, IsFlatOnSite (R := R) (((restriction φ).obj (P.X i))) := by
  classical
  let := monoidalCategory R
  let := monoidalCategory B
  let := symmetricCategory R
  let := symmetricCategory B
  let E := (p φ).ordinary
  let U := restriction φ
  have : PreservesFiniteLimits E := hflat.1
  have : PreservesFiniteColimits E := hflat.2
  have : PreservesFiniteLimits U := (restriction_exact φ).1
  have : PreservesFiniteColimits U := (restriction_exact φ).2
  obtain ⟨e₀, he₀⟩ := exists_changeOfRings_tensorCancellation_independentCoefficients φ
  let e (M : Modules B) (F : Modules R) :
      U.obj (M ⊗ E.obj F) ≅ U.obj M ⊗ F :=
    U.mapIso (((curriedTensor _).obj M).mapIso (eqToIso ((p φ).obj_eq F))) ≪≫ e₀ M F
  have he {M M' : Modules B} {F F' : Modules R} (f : M ⟶ M') (g : F ⟶ F') :
      U.map (tensorHom f (E.map g)) ≫ (e M' F').hom =
        (e M F).hom ≫ tensorHom (U.map f) g := by
    have hs : tensorHom f (E.map g) ≫ whiskerLeft M' (eqToHom ((p φ).obj_eq F')) =
        whiskerLeft M (eqToHom ((p φ).obj_eq F)) ≫
          tensorHom f (changeOfRingsHom φ F g) := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
        tensorHom_comp_tensorHom]
      simp only [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp,
        E, (p φ).map_eq, Category.assoc,
        eqToHom_trans, eqToHom_refl]
    change U.map (tensorHom f (E.map g)) ≫
        U.map (whiskerLeft M' (eqToHom ((p φ).obj_eq F'))) ≫ (e₀ M' F').hom =
      U.map (whiskerLeft M (eqToHom ((p φ).obj_eq F))) ≫
        (e₀ M F).hom ≫ tensorHom (U.map f) g
    rw [← U.map_comp_assoc, hs, U.map_comp, Category.assoc, he₀ f g]
  let e' (M : Modules B) (F : Modules R) :
      U.obj (E.obj F ⊗ M) ≅ F ⊗ U.obj M :=
    U.mapIso (β_ (E.obj F) M) ≪≫ e M F ≪≫ β_ (U.obj M) F
  have he' {M M' : Modules B} {F F' : Modules R} (f : M ⟶ M') (g : F ⟶ F') :
      U.map (tensorHom (E.map g) f) ≫ (e' M' F').hom =
        (e' M F).hom ≫ tensorHom g (U.map f) := by
    dsimp only [e', Iso.trans_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    rw [← U.map_comp_assoc, BraidedCategory.braiding_naturality, U.map_comp_assoc,
      reassoc_of% he f g, BraidedCategory.braiding_naturality]
  constructor
  · intro A hA
    let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj A)).obj P
    have hcolims (A : Sheaf J CommRingCat.{r}) :
        PreservesColimitsOfSize.{r, r} (toSheaf (derivedChangeRingIndependentCoefficients J A)) :=
      ⟨fun {D} _ ↦ ((moduleSheaves_colimits_forgetful
        (derivedChangeRingIndependentCoefficients J A)).2.2.2.2.2 D).2.1⟩
    have := hcolims R
    have := hcolims B
    have := preservesSmallestColimits_of_preservesColimits
      (toSheaf (derivedChangeRingIndependentCoefficients J R))
    have := preservesSmallestColimits_of_preservesColimits
      (toSheaf (derivedChangeRingIndependentCoefficients J B))
    have hcolim (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
      have : PreservesColimitsOfShape D (U ⋙ toSheaf
          (derivedChangeRingIndependentCoefficients J R)) :=
        inferInstanceAs (PreservesColimitsOfShape D
          (toSheaf (derivedChangeRingIndependentCoefficients J B)))
      have : ReflectsColimitsOfShape D (toSheaf
          (derivedChangeRingIndependentCoefficients J R)) :=
        reflectsColimitsOfShape_of_reflectsIsomorphisms
      exact preservesColimitsOfShape_of_reflects_of_preserves U (toSheaf _)
    have : PreservesColimitsOfSize.{0, 0} U := ⟨fun {D} instD ↦ @hcolim D instD⟩
    have : U.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
    let t := (HomologicalComplex₂.mapTotalIso U T (.up ℤ)).symm
    let f :
        (((U.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
        (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
          ((U.mapHomologicalComplex (.up ℤ)).obj P) :=
      HomologicalComplex.Hom.isoOfComponents
        (fun i ↦ HomologicalComplex.Hom.isoOfComponents
          (fun j ↦ e' (P.X j) (A.X i)) (by
            intro j j' hj
            change (e' (P.X j) (A.X i)).hom ≫ whiskerLeft (A.X i) (U.map (P.d j j')) =
              U.map (whiskerLeft (E.obj (A.X i)) (P.d j j')) ≫
                (e' (P.X j') (A.X i)).hom
            simpa only [E.map_id, id_tensorHom] using
              (he' (P.d j j') (𝟙 (A.X i))).symm))
        (by
          intro i i' hi
          apply HomologicalComplex.Hom.ext
          funext j
          change (e' (P.X j) (A.X i)).hom ≫ whiskerRight (A.d i i') (U.obj (P.X j)) =
            U.map (whiskerRight (E.map (A.d i i')) (P.X j)) ≫
              (e' (P.X j) (A.X i')).hom
          simpa only [U.map_id, tensorHom_id] using
            (he' (𝟙 (P.X j)) (A.d i i')).symm)
    have hEA : ((E.mapHomologicalComplex (.up ℤ)).obj A).Acyclic := by
      intro i
      exact (hA i).map E
    have ht := hP ((E.mapHomologicalComplex (.up ℤ)).obj A) hEA
    have hu : (((U.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor
          ((E.mapHomologicalComplex (.up ℤ)).obj A) P (curriedTensor _)))).Acyclic := by
      intro i
      exact (ht i).map U
    intro i
    exact (hu i).of_iso (t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ))
  · intro i
    let q : E ⋙ tensorRight (P.X i) ⋙ U ≅ tensorRight (U.obj (P.X i)) :=
      NatIso.ofComponents (fun M ↦ e' (P.X i) M) (by
        intro M M' g
        change U.map (whiskerRight (E.map g) (P.X i)) ≫ _ =
          _ ≫ whiskerRight g (U.obj (P.X i))
        simpa only [U.map_id, tensorHom_id] using he' (𝟙 (P.X i)) g)
    have : PreservesFiniteLimits (siteSheafTensorRight (P.X i)) := (hf i).1
    have : PreservesFiniteColimits (siteSheafTensorRight (P.X i)) := (hf i).2
    have : PreservesFiniteLimits (tensorRight (P.X i)) :=
      preservesFiniteLimits_of_natIso (siteSheafTensorRightIso B (P.X i))
    have : PreservesFiniteColimits (tensorRight (P.X i)) :=
      preservesFiniteColimits_of_natIso (siteSheafTensorRightIso B (P.X i))
    have : PreservesFiniteLimits (tensorRight (P.X i) ⋙ U) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits (tensorRight (P.X i) ⋙ U) :=
      comp_preservesFiniteColimits _ _
    have : PreservesFiniteLimits (E ⋙ tensorRight (P.X i) ⋙ U) :=
      comp_preservesFiniteLimits E _
    have : PreservesFiniteColimits (E ⋙ tensorRight (P.X i) ⋙ U) :=
      comp_preservesFiniteColimits E _
    have : PreservesFiniteLimits (tensorRight (U.obj (P.X i))) :=
      preservesFiniteLimits_of_natIso q
    have : PreservesFiniteColimits (tensorRight (U.obj (P.X i))) :=
      preservesFiniteColimits_of_natIso q
    exact ⟨preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R (U.obj (P.X i))).symm,
      preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R (U.obj (P.X i))).symm⟩

private theorem normalized_hom_comparison {A S : Sheaf J CommRingCat.{r}} (a : A ⟶ S)
    (P : CochainComplex (Modules A) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := A) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := A) (P.X i))
    (H : HomotopyCategory (Modules S) (.up ℤ))
    (g : ((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ _).obj P) ⟶ H) :
    (N.adjunction a).homEquiv _ _
        ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P) ≫ DerivedCategory.Qh.map g) =
      DerivedCategory.Qh.map
        (((N.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).homEquiv _ _ g) ≫
          (N.right_factors a).inv.app H := by
  rw [Adjunction.homEquiv_unit, (N.right a).map_comp]
  apply (cancel_mono ((N.right_factors a).hom.app H)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Category.comp_id]
  erw [(N.right_factors a).hom.naturality g]
  simp only [Functor.comp_map, Category.assoc, CategoryTheory.Category.comp_id]
  rw [reassoc_of% N.adjunction_normalization a P hP hf,
    ← DerivedCategory.Qh.map_comp]
  erw [CategoryTheory.Category.comp_id]
  rfl

private theorem ordinary_comparison_unit {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (o : restriction φ ⋙ (p (φ ≫ ψ)).ordinary ≅ (p ψ).ordinary)
    (ho : ∀ (M : Modules B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
        (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x) =
          sectionTensor (p ψ) M U s x) (M : Modules B) :
    (N.ordinaryAdjunction (φ ≫ ψ)).unit.app ((restriction φ).obj M) ≫
        (restriction (φ ≫ ψ)).map (o.hom.app M) =
      (restriction φ).map ((N.ordinaryAdjunction ψ).unit.app M) ≫
        (N.restrictionComp φ ψ).hom.app ((p ψ).ordinary.obj M) := by
  ext U x
  change (o.hom.app M).val.app U
      (((N.ordinaryAdjunction (φ ≫ ψ)).unit.app ((restriction φ).obj M)).val.app U x) =
    ((N.restrictionComp φ ψ).hom.app ((p ψ).ordinary.obj M)).val.app U
      (((N.ordinaryAdjunction ψ).unit.app M).val.app U x)
  rw [N.ordinary_unit, ho, N.restrictionComp_sections, N.ordinary_unit]

private theorem ordinary_comparison_homotopy_unit {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) (o : restriction φ ⋙ (p (φ ≫ ψ)).ordinary ≅ (p ψ).ordinary)
    (ho : ∀ (M : Modules B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
        (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x) =
          sectionTensor (p ψ) M U s x)
    (H : HomotopyCategory (Modules B) (.up ℤ)) :
    ((N.ordinaryAdjunction (φ ≫ ψ)).mapHomotopyCategory (.up ℤ)).homEquiv _ _
        ((Functor.mapHomotopyCategoryCompIso o (.up ℤ)).hom.app H) =
      ((restriction φ).mapHomotopyCategory (.up ℤ)).map
          (((N.ordinaryAdjunction ψ).mapHomotopyCategory (.up ℤ)).unit.app H) ≫
        (Functor.mapHomotopyCategoryCompIso (N.restrictionComp φ ψ) (.up ℤ)).hom.app
          (((p ψ).ordinary.mapHomotopyCategory (.up ℤ)).obj H) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  rw [Adjunction.homEquiv_unit]
  have hc := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
    (N.ordinaryAdjunction (φ ≫ ψ))
    (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P)
  erw [hc, Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ =
    (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext i : 1
  exact ordinary_comparison_unit p N φ ψ o ho (P.X i)

private theorem rightComp_inverse_normalization {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) (H : HomotopyCategory (Modules S) (.up ℤ)) :
    (N.right φ).map ((N.right_factors ψ).inv.app H) ≫
        (N.rightComp φ ψ).hom.app (DerivedCategory.Qh.obj H) =
      (N.right_factors φ).hom.app
          (((restriction ψ).mapHomotopyCategory (.up ℤ)).obj H) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (N.restrictionComp φ ψ) (.up ℤ)).hom.app H) ≫
        (N.right_factors (φ ≫ ψ)).inv.app H := by
  apply (cancel_mono ((N.right_factors (φ ≫ ψ)).hom.app H)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [N.rightComp_normalization]
  simp only [← (N.right φ).map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp]
  erw [CategoryTheory.Category.comp_id]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def reductionMap {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S) :
    N.right φ ⋙ (p (φ ≫ ψ)).derived ⟶ (p ψ).derived where
  app M := (N.derived φ ψ).inv.app ((N.right φ).obj M) ≫
    (p ψ).derived.map ((N.adjunction φ).counit.app M)
  naturality {M M'} f := by
    dsimp
    rw [(N.derived φ ψ).inv.naturality_assoc]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    exact congrArg (fun k ↦ (N.derived φ ψ).inv.app ((N.right φ).obj M) ≫
      (p ψ).derived.map k) ((N.adjunction φ).counit.naturality f)

private theorem reductionMap_adjunct {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (M : DerivedCategory (Modules B)) (Q : DerivedCategory (Modules S))
    (f : M ⟶ (N.right ψ).obj Q) :
    ((N.adjunction (φ ≫ ψ)).homEquiv _ _).symm
        ((N.right φ).map f ≫ (N.rightComp φ ψ).hom.app Q) =
      (reductionMap p N φ ψ).app M ≫ ((N.adjunction ψ).homEquiv M Q).symm f := by
  apply ((N.adjunction (φ ≫ ψ)).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  let g := ((N.adjunction ψ).homEquiv M Q).symm f
  have hf : (N.adjunction ψ).homEquiv M Q g = f := Equiv.apply_symm_apply _ _
  dsimp only [reductionMap]
  rw [Category.assoc]
  change _ = (N.adjunction (φ ≫ ψ)).homEquiv _ _
    ((N.derived φ ψ).inv.app ((N.right φ).obj M) ≫
      (p ψ).derived.map ((N.adjunction φ).counit.app M) ≫ g)
  rw [Adjunction.homEquiv_unit]
  have hu := N.unit_comp φ ψ ((N.right φ).obj M)
  have hi := congrArg (fun k ↦ k ≫ (N.right (φ ≫ ψ)).map
    ((N.derived φ ψ).inv.app ((N.right φ).obj M))) hu
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hi
  erw [CategoryTheory.Functor.map_id] at hi
  simp only [CategoryTheory.Category.comp_id] at hi
  rw [Functor.map_comp, ← Category.assoc, ← hi]
  simp only [Category.assoc]
  erw [← (N.rightComp φ ψ).hom.naturality]
  change _ = (N.adjunction φ).unit.app _ ≫
    (N.right φ).map ((N.adjunction ψ).unit.app _) ≫
    (N.right φ).map ((N.right ψ).map
      ((p ψ).derived.map ((N.adjunction φ).counit.app M) ≫ g)) ≫ _
  rw [← (N.right φ).map_comp_assoc, ← Adjunction.homEquiv_unit,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [(N.adjunction φ).right_triangle_components_assoc]
  rw [← Adjunction.homEquiv_unit]
  exact congrArg (fun k ↦ (N.right φ).map k ≫ (N.rightComp φ ψ).hom.app Q) hf.symm

private theorem reductionMap_representative
    (hflat : exactFunctor (Modules R) (Modules B) (p φ).ordinary)
    {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (o : restriction φ ⋙ (p (φ ≫ ψ)).ordinary ≅ (p ψ).ordinary)
    (ho : ∀ (M : Modules B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
        (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x) =
          sectionTensor (p ψ) M U s x)
    (P : CochainComplex (Modules B) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) :
    (reductionMap p N φ ψ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p ψ).counit.app ((HomotopyCategory.quotient _ _).obj P) =
    (p (φ ≫ ψ)).derived.map
        ((N.right_factors φ).hom.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p (φ ≫ ψ)).counit.app
        (((restriction φ).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso o (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj P)) := by
  let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
  let UP := ((restriction φ).mapHomologicalComplex (.up ℤ)).obj P
  have hUP := restricted_flat_models p φ hflat P hP hf
  let K := ((p ψ).ordinary.mapHomotopyCategory (.up ℤ)).obj H
  let eps := (p ψ).counit.app H
  have hκ := reductionMap_adjunct p N φ ψ (DerivedCategory.Qh.obj H)
    (DerivedCategory.Qh.obj K) ((N.adjunction ψ).homEquiv _ _ eps)
  rw [Equiv.symm_apply_apply] at hκ
  apply ((N.adjunction (φ ≫ ψ)).homEquiv _ _).injective
  erw [← hκ, Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
  have heps := normalized_hom_comparison p N ψ P hP hf K (𝟙 K)
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Adjunction.homEquiv_id] at heps
  rw [heps]
  erw [normalized_hom_comparison p N (φ ≫ ψ) UP hUP.1 hUP.2 K]
  erw [ordinary_comparison_homotopy_unit p N φ ψ o ho H]
  simp only [(N.right φ).map_comp, DerivedCategory.Qh.map_comp, Category.assoc]
  rw [rightComp_inverse_normalization p N φ ψ K]
  erw [(N.right_factors φ).hom.naturality_assoc]
  rfl

private theorem isIso_app_transport {A D : Type*} [Category A] [Category D]
    {F G : A ⥤ D} (α : F ⟶ G) {X Y : A} (e : X ≅ Y) [IsIso (α.app X)] :
    IsIso (α.app Y) := by
  have : IsIso (F.map e.hom ≫ α.app Y) := by
    rw [α.naturality e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map e.hom) (α.app Y)

private theorem reductionMap_isIso
    (hflat : exactFunctor (Modules R) (Modules B) (p φ).ordinary)
    {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (o : restriction φ ⋙ (p (φ ≫ ψ)).ordinary ≅ (p ψ).ordinary)
    (ho : ∀ (M : Modules B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
        (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x) =
          sectionTensor (p ψ) M U s x) : IsIso (reductionMap p N φ ψ) := by
  classical
  have hmodel (P : CochainComplex (Modules B) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P)
      (hf : ∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) :
      IsIso ((reductionMap p N φ ψ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) := by
    have hUP := restricted_flat_models p φ hflat P hP hf
    have := N.computed ψ P hP hf
    have hcomp : IsIso ((p (φ ≫ ψ)).counit.app
        (((restriction φ).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P))) :=
      N.computed (φ ≫ ψ) (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P)
        hUP.1 hUP.2
    have : IsIso ((reductionMap p N φ ψ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
          (p ψ).counit.app ((HomotopyCategory.quotient _ _).obj P)) := by
      rw [reductionMap_representative p N φ hflat ψ o ho P hP hf]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((p ψ).counit.app
      ((HomotopyCategory.quotient _ _).obj P))
  have hH (H : HomotopyCategory (Modules B) (.up ℤ)) :
      IsIso ((reductionMap p N φ ψ).app (DerivedCategory.Qh.obj H)) := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
    obtain ⟨P, f, hP, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := B) K
    have hflatP (i : ℤ) : IsFlatOnSite (R := B) (P.X i) := by
      let := monoidalCategory B
      have : PreservesFiniteLimits (tensorRight (P.X i)) := (hf i).1
      have : PreservesFiniteColimits (tensorRight (P.X i)) := (hf i).2
      exact ⟨preservesFiniteLimits_of_natIso (siteSheafTensorRightIso B (P.X i)).symm,
        preservesFiniteColimits_of_natIso (siteSheafTensorRightIso B (P.X i)).symm⟩
    have := hmodel P hP hflatP
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map f)) :=
      Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ)) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq)
    exact isIso_app_transport (reductionMap p N φ ψ) (asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (.up ℤ)).map f)))
  have hX (X : DerivedCategory (Modules B)) : IsIso ((reductionMap p N φ ψ).app X) := by
    have := hH (DerivedCategory.Qh.objPreimage X)
    exact isIso_app_transport (reductionMap p N φ ψ) (DerivedCategory.Qh.objObjPreimageIso X)
  exact NatIso.isIso_of_isIso_app (reductionMap p N φ ψ)

private theorem reductionMap_successive {S T : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) (τ : S ⟶ T) (M : DerivedCategory (Modules B)) :
    (p τ).derived.map ((reductionMap p N φ ψ).app M) ≫
        (N.derived ψ τ).hom.app M =
      (N.derived (φ ≫ ψ) τ).hom.app ((N.right φ).obj M) ≫
        eqToHom (congrArg (fun a ↦ (p a).derived.obj ((N.right φ).obj M))
          (Category.assoc φ ψ τ)) ≫ (reductionMap p N φ (ψ ≫ τ)).app M := by
  dsimp only [reductionMap]
  rw [Functor.map_comp, Category.assoc]
  erw [(N.derived ψ τ).hom.naturality]
  apply (cancel_epi ((p τ).derived.map
    ((N.derived φ ψ).hom.app ((N.right φ).obj M)))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [CategoryTheory.Category.id_comp]
  rw [reassoc_of% N.associative φ ψ τ ((N.right φ).obj M)]
  simp only [eqToHom_refl, CategoryTheory.Category.id_comp, Iso.hom_inv_id_app_assoc]

private theorem reductionMap_coefficient {S T : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) (τ : S ⟶ T) (M : DerivedCategory (Modules B)) :
    flatCoefficientChange p N (φ ≫ ψ) τ ((N.right φ).obj M) ≫
        (N.right τ).map
          (eqToHom (congrArg (fun a ↦ (p a).derived.obj ((N.right φ).obj M))
            (Category.assoc φ ψ τ)) ≫ (reductionMap p N φ (ψ ≫ τ)).app M) =
      (reductionMap p N φ ψ).app M ≫ flatCoefficientChange p N ψ τ M := by
  dsimp only [flatCoefficientChange]
  rw [Category.assoc, ← Functor.map_comp]
  rw [← reductionMap_successive p N φ ψ τ M, Functor.map_comp]
  simpa only [reductionMap, Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map,
    Category.assoc] using
    ((N.adjunction τ).unit.naturality_assoc ((reductionMap p N φ ψ).app M)
      ((N.right τ).map ((N.derived ψ τ).hom.app M))).symm

private theorem reductionMap_equal_index {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) (M : DerivedCategory (Modules B)) :
    (p (𝟙 S)).derived.map ((reductionMap p N φ ψ).app M) ≫
        flatCoefficientUnit p N ψ M =
      flatCoefficientUnit p N (φ ≫ ψ) ((N.right φ).obj M) ≫
        (reductionMap p N φ ψ).app M := by
  dsimp only [flatCoefficientUnit]
  rw [← Category.assoc, reductionMap_successive p N φ ψ (𝟙 S) M]
  simp only [Category.assoc]
  congr 1
  rw [eqToHom_naturality (fun a : B ⟶ S ↦ (reductionMap p N φ a).app M)
    (CategoryTheory.Category.comp_id ψ)]
  simp only [← Category.assoc, eqToHom_trans]

/-- Flat scalar restriction preserves reduction adjuncts, naturally and coherently.
The `Normalization` parameter supplies the canonical adjunctions and associators of
the existing derived scalar extensions. `exactFunctor` states exactly flatness of B/R;
the multiplication-isomorphism hypothesis is imposed at each coefficient S in the result.

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 0D6D and 07A6;
sites-modules.tex, Tag 05V4
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct).

Proof:
1. Resolve a B-complex by a K-flat B-complex P with flat terms (06YS).
Restriction is exact and leaves the underlying abelian sheaf unchanged (07A6).
2. For an acyclic R-complex A, flatness makes B tensor_R A acyclic. Tensor
cancellation (05V4) identifies Tot(Res P tensor_R A) with the restriction of
Tot(P tensor_B (B tensor_R A)). Restriction commutes with direct sums and detects
acyclicity. K-flatness of P proves K-flatness of Res P. The same cancellation
shows each restricted term is flat, so its derived counit is invertible.
3. Cancellation followed by the assumed multiplication isomorphism gives the
ordinary balanced isomorphism, sending x tensor s to x tensor s. This ordinary
assertion, including its section formula, is proved in OrdinaryFlatCoefficientComparison.
4. Define the derived comparison on every object by the inverse composition
isomorphism followed by extension of the R-to-B adjunction counit. The normalized
composition unit and the triangle identity show that its transpose carries every
B-adjunct to the corresponding R-adjunct, with no chain representative required.
5. On a flat-term K-flat complex, apply the normalization of both derived adjunctions
to its localization counit. The ordinary comparison preserves the normalized units,
so injectivity of the R-adjunction identifies the representative with the prescribed
ordinary comparison. Its other factors are invertible by step 2 and Normalization.computed;
therefore the derived comparison is invertible. Resolve an arbitrary homotopy object
by a flat-term K-flat complex and use naturality along the localized quasi-isomorphism.
Essential surjectivity of the homotopy localization gives every derived object.
6. The associative normalization and naturality of the composition isomorphisms give
successive compatibility directly for the counit-defined comparison. Naturality of
the extension unit then gives coefficient naturality for the specified coefficient arrows.
7. Specialize successive compatibility to the identity ring map, and transport along
the right-unit equality of ring maps. This gives exactly the specified equal-index
comparison. Iterated associativity follows from the given coherent normalization.
No flatness of S/B or S'/S, boundedness, or chain representative of f is needed. -/
theorem flat_coefficient_reduction_adjunct
    (hflat : exactFunctor (Modules R) (Modules B) (p φ).ordinary) :
    Nonempty (FlatCoefficientReductionComparison p N φ) := by
  classical
  have ho {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
      (hμ : IsIso (flatCoefficientMultiplication p N φ ψ)) :=
    ordinary_flatCoefficientComparison p N φ ψ hμ
  let o {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
      (hμ : IsIso (flatCoefficientMultiplication p N φ ψ)) := (ho ψ hμ).choose
  have hop {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
      (hμ : IsIso (flatCoefficientMultiplication p N φ ψ)) := (ho ψ hμ).choose_spec
  have hd {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
      (hμ : IsIso (flatCoefficientMultiplication p N φ ψ)) :
      IsIso (reductionMap p N φ ψ) := reductionMap_isIso p N φ hflat ψ (o ψ hμ) (hop ψ hμ)
  refine ⟨{
    ordinary := fun ψ hμ ↦ o ψ hμ
    ordinary_pure := fun ψ hμ ↦ hop ψ hμ
    derived := fun ψ hμ ↦ by
      letI := hd ψ hμ
      exact asIso (reductionMap p N φ ψ)
    restricted_computed := ?_
    representative := ?_
    adjunct := ?_
    coefficient_naturality := ?_
    successive := ?_
    equal_index := ?_
  }⟩
  · intro S ψ P hP hf
    have hUP := restricted_flat_models p φ hflat P hP hf
    exact N.computed (φ ≫ ψ) (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P)
      hUP.1 hUP.2
  · intro S ψ hμ P hP hf
    exact reductionMap_representative p N φ hflat ψ (o ψ hμ) (hop ψ hμ) P hP hf
  · intro S ψ hμ M Q f
    exact reductionMap_adjunct p N φ ψ M Q f
  · intro S S' ψ τ hμ hμ' M
    exact reductionMap_coefficient p N φ ψ τ M
  · intro S S' ψ τ hμ hμ' M
    exact reductionMap_successive p N φ ψ τ M
  · intro S ψ hμ M
    exact reductionMap_equal_index p N φ ψ M

end SheafOfModules
