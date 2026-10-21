/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Paper.CommonQuotientTowerPresentation
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Paper.OrdinaryCommonQuotientTower
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Flat common-quotient reduction, with strict towers and quotient cones

Source: Stacks Project, proetale.tex, Tag 099L, section-derived-completion-noetherian;
sites-cohomology.tex, Tags 06YS, 06YT, 06YY; sites-modules.tex, Tag 03EK.
(blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower).

The quotient ideals are the kernel ideal sheaves in the common-quotient presentation.
Both derived scalar extensions are the existing universal cochain models. The ordinary
comparisons, transitions and cones are characterized by their actual sheafified tensor
sections. Scalar extension in the existing library writes the scalar first: `s ⊗ p`.
-/

@[expose] public noncomputable section
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u v r wR wB wS wA wT
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace SheafOfModules.CommonQuotientReduction

attribute [local irreducible] monoidalCategory
  CochainComplex.IsKFlatIndependentCoefficients IsFlatOnSite

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The recorded module category, with no change of encoding or coefficient universe.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev Modules (A : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J A)

/-- Actual restriction of scalars, used also termwise on complexes.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev restriction {A T : Sheaf J CommRingCat.{r}} (a : A ⟶ T) :
    Modules T ⥤ Modules A :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)

/-- A pure scalar-extension section in the prescribed ordinary presentation of a
cochain derived-change-of-rings model. This is precisely the sheafification-unit
image of the balanced tensor, transported along the model's object equality.
Source: Stacks 03EK (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
def scalarSection {A T : Sheaf J CommRingCat.{r}} {a : A ⟶ T}
    [HasDerivedCategory.{wA} (Modules A)] [HasDerivedCategory.{wT} (Modules T)]
    (F : DerivedChangeOfRingsCochainModel a) (M : Modules A)
    (U : Cᵒᵖ) (s : T.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf a M).presheaf).app U
      (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x))

variable {R B : Sheaf J CommRingCat.{r}} {φ : R ⟶ B}
  (D : CommonQuotientTowerPresentation φ)
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wB} (Modules B)]
  [∀ n : ℕ, HasDerivedCategory.{wS} (Modules (D.S.obj (op n)))]
  (a : ∀ n : ℕ, DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} (D.projection n))
  (b : ∀ n : ℕ, DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (D.extensionProjection n))

/-- The actual `S_n`-linear complex obtained by reduction over `R`.
Source: Stacks 06YY (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev leftComplex (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((a n).E.mapHomologicalComplex (.up ℤ)).obj
    (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P)

/-- The actual `S_n`-linear complex obtained by reduction over `B`.
Source: Stacks 06YY (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev rightComplex (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((b n).E.mapHomologicalComplex (.up ℤ)).obj P

/-- The levels of the first strict tower, restricted to `R`.
Source: Stacks 099L (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev leftLevel (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).obj
    (leftComplex D a n P)

/-- The levels of the second strict tower, also restricted to `R` through `q_n`.
Source: Stacks 099L (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev rightLevel (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).obj
    (rightComplex D b n P)

attribute [local irreducible] scalarSection

/-- The full normalized comparison specification. All maps below are fixed by pure
sections or by localization/counit compatibility; in particular the strict cones
are the quotient cones, not arbitrary morphisms with the same vertices.

Source: Stacks 099L, 03EK and 06YY
(blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
structure Comparison where
  /-- Restriction on derived categories. -/
  res : DerivedCategory (Modules B) ⥤ DerivedCategory (Modules R)
  /-- Its prescribed localization of termwise restriction. -/
  resFactors : DerivedCategory.Q ⋙ res ≅
    (restriction φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- Ordinary, `S_n`-linear, natural comparisons on cochain complexes. -/
  ordinary : ∀ n : ℕ,
    (restriction φ).mapHomologicalComplex (.up ℤ) ⋙
      (a n).E.mapHomologicalComplex (.up ℤ) ≅ (b n).E.mapHomologicalComplex (.up ℤ)
  /-- The ordinary comparison sends `s ⊗ p` to the same pure section. -/
  ordinary_sections : ∀ (n : ℕ) (P : CochainComplex (Modules B) ℤ) (i : ℤ)
    (U : Cᵒᵖ) (s : (D.S.obj (op n)).obj.obj U) (p : (P.X i).val.obj U),
    (((ordinary n).hom.app P).f i).val.app U
      (scalarSection (a n) ((restriction φ).obj (P.X i)) U s p) =
        scalarSection (b n) (P.X i) U s p
  /-- The induced natural derived comparisons. -/
  derived : ∀ n : ℕ, res ⋙ (a n).T ≅ (b n).T
  /-- Their canonical representative normalization, using the existing derived counits. -/
  computes : ∀ (n : ℕ) (P : CochainComplex (Modules B) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
      (derived n).hom.app (DerivedCategory.Q.obj P) ≫ (b n).ε.app P =
        (a n).T.map (resFactors.hom.app P) ≫
          (a n).ε.app (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((ordinary n).hom.app P)
  /-- One flat-term K-flat representative works simultaneously at every level. -/
  representatives : ∀ M : DerivedCategory (Modules B),
    ∃ P : CochainComplex (Modules B) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B) P ∧
      (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ M)
  /-- The strict tower comparisons, their transition formulas and their quotient cones. -/
  strict : ∀ P : CochainComplex (Modules B) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
    ∃ (tL : ∀ n : ℕ, leftLevel D a (n + 1) P ⟶ leftLevel D a n P)
      (tR : ∀ n : ℕ, rightLevel D b (n + 1) P ⟶ rightLevel D b n P)
      (e : Functor.ofOpSequence (X := fun n ↦ leftLevel D a n P) tL ≅
        Functor.ofOpSequence (X := fun n ↦ rightLevel D b n P) tR)
      (ηL : (Functor.const ℕᵒᵖ).obj
          (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ⟶
        Functor.ofOpSequence (X := fun n ↦ leftLevel D a n P) tL)
      (ηR : (Functor.const ℕᵒᵖ).obj
          (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ⟶
        Functor.ofOpSequence (X := fun n ↦ rightLevel D b n P) tR),
      (∀ n : ℕ, e.hom.app (op n) =
        ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).map
          ((ordinary n).hom.app P)) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ)
        (s : (D.S.obj (op (n + 1))).obj.obj U) (p : (P.X i).val.obj U),
        ((tL n).f i).val.app U
          (scalarSection (a (n + 1)) ((restriction φ).obj (P.X i)) U s p) =
            scalarSection (a n) ((restriction φ).obj (P.X i)) U
              ((D.S.map (homOfLE (Nat.le_succ n)).op).hom.app U s) p) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ)
        (s : (D.S.obj (op (n + 1))).obj.obj U) (p : (P.X i).val.obj U),
        ((tR n).f i).val.app U (scalarSection (b (n + 1)) (P.X i) U s p) =
          scalarSection (b n) (P.X i) U
            ((D.S.map (homOfLE (Nat.le_succ n)).op).hom.app U s) p) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (p : (P.X i).val.obj U),
        (((ηL.app (op n)).f i).val.app U p =
          scalarSection (a n) ((restriction φ).obj (P.X i)) U 1 p) ∧
        (((ηR.app (op n)).f i).val.app U p = scalarSection (b n) (P.X i) U 1 p)) ∧
      (ηL ≫ e.hom = ηR) ∧
      (∀ (n : ℕ) (i : ℤ), Epi ((ηL.app (op n)).f i)) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (p : (P.X i).val.obj U),
        ((ηL.app (op n)).f i).val.app U p = 0 ↔
          D.locallyInIdealProduct n ((restriction φ).obj (P.X i)) U p)

attribute [local semireducible] scalarSection

omit [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wB} (Modules B)] in
private theorem restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction φ) :=
  (restrictScalars_exact_kflat ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).1

omit [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wB} (Modules B)] in
private theorem restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction φ) :=
  (restrictScalars_exact_kflat ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).2

private theorem flat_representatives (M : DerivedCategory (Modules B)) :
    ∃ P : CochainComplex (Modules B) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B) P ∧
      (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  let G := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨P, f, hP, hterms, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := B) G
  have := hf
  refine ⟨P, hP, ?_, ⟨asIso (DerivedCategory.Q.map f) ≪≫ e⟩⟩
  intro i
  let := isMonoidal_W_independentCoefficients B
  let := monoidalCategory B
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight (P.X i)) := (hterms i).1
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight (P.X i)) := (hterms i).2
  unfold IsFlatOnSite
  exact ⟨preservesFiniteLimits_of_natIso (siteSheafTensorRightIso B (P.X i)).symm,
    preservesFiniteColimits_of_natIso (siteSheafTensorRightIso B (P.X i)).symm⟩

private theorem flat_extension_exact
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wB} φ)
    (hflat : IsFlatOnSite (R := R)
      ((restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J B)))) :
    PreservesFiniteLimits F.E ∧ PreservesFiniteColimits F.E := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  unfold IsFlatOnSite at hflat
  let S := (restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J B))
  let VR := toSheaf (derivedChangeRingIndependentCoefficients J R)
  let VB := toSheaf (derivedChangeRingIndependentCoefficients J B)
  have : PreservesFiniteLimits (siteSheafTensorRight S) := hflat.1
  have : PreservesFiniteColimits (siteSheafTensorRight S) := hflat.2
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight S) :=
    preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R S)
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight S) :=
    preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R S)
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft S) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight S).symm
  have : PreservesFiniteColimits (MonoidalCategory.tensorLeft S) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight S).symm
  obtain ⟨e, he⟩ := exists_changeOfRings_tensor_comparison_independent φ
  let j : F.E ⋙ VB ≅ MonoidalCategory.tensorLeft S ⋙ VR :=
    NatIso.ofComponents (fun M ↦ VB.mapIso (eqToIso (F.obj_eq M)) ≪≫ e M) (by
      intro M N f
      dsimp
      rw [F.map_eq, Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      simp only [VB, ← Functor.map_comp_assoc, eqToHom_trans, eqToHom_refl]
      rw [Functor.map_comp, Category.assoc]
      exact congrArg (fun g ↦ VB.map (eqToHom (F.obj_eq M)) ≫ g) (he f))
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft S ⋙ VR) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (MonoidalCategory.tensorLeft S ⋙ VR) :=
    comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (F.E ⋙ VB) := preservesFiniteLimits_of_natIso j.symm
  have : PreservesFiniteColimits (F.E ⋙ VB) := preservesFiniteColimits_of_natIso j.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F.E VB,
    preservesFiniteColimits_of_reflects_of_preserves F.E VB⟩

private theorem restriction_kflat
    (hflat : IsFlatOnSite (R := R)
      ((restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J B))))
    (P : CochainComplex (Modules B) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  have : PreservesFiniteLimits (restriction φ) := restriction_preservesFiniteLimits
  have : PreservesFiniteColimits (restriction φ) := restriction_preservesFiniteColimits
  let := isMonoidal_W_independentCoefficients R
  let := isMonoidal_W_independentCoefficients B
  let := monoidalCategory R
  let := monoidalCategory B
  let := symmetricCategory R
  let := symmetricCategory B
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients B
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients B
  obtain ⟨E⟩ := nonempty_derivedChangeOfRingsCochainModel φ
  have hE := flat_extension_exact E hflat
  have : PreservesFiniteLimits E.E := hE.1
  have : PreservesFiniteColimits E.E := hE.2
  let U := restriction φ
  obtain ⟨e₀, he₀⟩ := exists_changeOfRings_tensorCancellation_independentCoefficients φ
  let e (M : Modules B) (N : Modules R) :=
    U.mapIso (((MonoidalCategory.curriedTensor _).obj M).mapIso (eqToIso (E.obj_eq N))) ≪≫
      e₀ M N
  have he {M M' : Modules B} {N N' : Modules R} (f : M ⟶ M') (g : N ⟶ N') :
      U.map (MonoidalCategory.tensorHom f (E.E.map g)) ≫ (e M' N').hom =
        (e M N).hom ≫ MonoidalCategory.tensorHom (U.map f) g := by
    have hs : MonoidalCategory.tensorHom f (E.E.map g) ≫
        MonoidalCategory.whiskerLeft M' (eqToHom (E.obj_eq N')) =
      MonoidalCategory.whiskerLeft M (eqToHom (E.obj_eq N)) ≫
        MonoidalCategory.tensorHom f (changeOfRingsHom φ N g) := by
      rw [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.id_tensorHom,
        MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
      simp only [Category.comp_id, Category.id_comp, E.map_eq, Category.assoc,
        eqToHom_trans, eqToHom_refl]
    change U.map (MonoidalCategory.tensorHom f (E.E.map g)) ≫
      U.map (MonoidalCategory.whiskerLeft M' (eqToHom (E.obj_eq N'))) ≫ (e₀ M' N').hom =
      U.map (MonoidalCategory.whiskerLeft M (eqToHom (E.obj_eq N))) ≫ (e₀ M N).hom ≫
        MonoidalCategory.tensorHom (U.map f) g
    rw [← U.map_comp_assoc, hs, U.map_comp, Category.assoc, he₀ f g]
  let e' (M : Modules B) (N : Modules R) :=
    U.mapIso (BraidedCategory.braiding (E.E.obj N) M) ≪≫ e M N ≪≫
      BraidedCategory.braiding (U.obj M) N
  have he' {M M' : Modules B} {N N' : Modules R} (f : M ⟶ M') (g : N ⟶ N') :
      U.map (MonoidalCategory.tensorHom (E.E.map g) f) ≫ (e' M' N').hom =
        (e' M N).hom ≫ MonoidalCategory.tensorHom g (U.map f) := by
    dsimp only [e', Iso.trans_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    rw [← U.map_comp_assoc, BraidedCategory.braiding_naturality,
      U.map_comp, Category.assoc]
    rw [← Category.assoc (U.map (MonoidalCategory.tensorHom f (E.E.map g)))
      (e M' N').hom, he f g]
    simp only [Category.assoc]
    rw [BraidedCategory.braiding_naturality]
  unfold CochainComplex.IsKFlatIndependentCoefficients at hP ⊢
  intro F hF
  let L := ((E.E.mapHomologicalComplex (.up ℤ)).obj F)
  have hL : L.Acyclic := fun i ↦ (hF i).map E.E
  have hp : (CochainComplex.mapBifunctor L P (MonoidalCategory.curriedTensor _)).Acyclic :=
    hP L hL
  let T := (((MonoidalCategory.curriedTensor _).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj L).obj P
  have hcolim (K : Type) [Category.{0} K] : PreservesColimitsOfShape K U := by
    have : PreservesColimitsOfShape K (U ⋙ toSheaf
        (derivedChangeRingIndependentCoefficients J R)) :=
      inferInstanceAs (PreservesColimitsOfShape K
        (toSheaf (derivedChangeRingIndependentCoefficients J B)))
    have : ReflectsColimitsOfShape K (toSheaf
        (derivedChangeRingIndependentCoefficients J R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves U (toSheaf _)
  have : PreservesColimitsOfSize.{0, 0} U := ⟨fun {K} instK ↦ @hcolim K instK⟩
  have : U.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso U T (.up ℤ)).symm
  let f : (((U.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((MonoidalCategory.curriedTensor _).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj F).obj ((U.mapHomologicalComplex (.up ℤ)).obj P) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ HomologicalComplex.Hom.isoOfComponents
        (fun j ↦ e' (P.X j) (F.X i)) (by
          intro j j' hj
          change (e' (P.X j) (F.X i)).hom ≫
              MonoidalCategory.whiskerLeft (F.X i) (U.map (P.d j j')) =
            U.map (MonoidalCategory.whiskerLeft (E.E.obj (F.X i)) (P.d j j')) ≫
              (e' (P.X j') (F.X i)).hom
          simpa only [E.E.map_id, MonoidalCategory.id_tensorHom]
            using (he' (P.d j j') (𝟙 (F.X i))).symm))
      (by
        intro i i' hi
        apply HomologicalComplex.Hom.ext
        funext j
        change (e' (P.X j) (F.X i)).hom ≫
            MonoidalCategory.whiskerRight (F.d i i') (U.obj (P.X j)) =
          U.map (MonoidalCategory.whiskerRight (E.E.map (F.d i i')) (P.X j)) ≫
            (e' (P.X j) (F.X i')).hom
        simpa only [U.map_id, MonoidalCategory.tensorHom_id]
          using (he' (𝟙 (P.X j)) (F.d i i')).symm)
  have hU : (((U.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor L P (MonoidalCategory.curriedTensor _)))).Acyclic :=
    fun i ↦ (hp i).map U
  exact HomologicalComplex.Acyclic.of_iso hU
    (t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ))

private theorem derived_comparison_of_ordinary
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (hk : ∀ P : CochainComplex (Modules B) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := R)
        (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P))
    (n : ℕ)
    (e : (restriction φ).mapHomologicalComplex (.up ℤ) ⋙
      (a n).E.mapHomologicalComplex (.up ℤ) ≅ (b n).E.mapHomologicalComplex (.up ℤ)) :
    ∃ d : (restriction φ).mapDerivedCategory ⋙ (a n).T ≅ (b n).T,
      ∀ P : CochainComplex (Modules B) ℤ,
        d.hom.app (DerivedCategory.Q.obj P) ≫ (b n).ε.app P =
          (a n).T.map ((restriction φ).mapDerivedCategoryFactors.hom.app P) ≫
            (a n).ε.app (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
              DerivedCategory.Q.map (e.hom.app P) := by
  let U := (restriction φ).mapHomologicalComplex (.up ℤ)
  let V : DerivedCategory (Modules B) ⥤ DerivedCategory (Modules R) :=
    (restriction φ).mapDerivedCategory
  let c : DerivedCategory.Q ⋙ V ≅ U ⋙ DerivedCategory.Q :=
    (restriction φ).mapDerivedCategoryFactors
  let β : DerivedCategory.Q ⋙ (V ⋙ (a n).T) ⟶
      (b n).E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight c.hom (a n).T ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft U (a n).ε ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e.hom DerivedCategory.Q
  let := (b n).universal
  let δ := (b n).T.leftDerivedLift (b n).ε
    (HomologicalComplex.quasiIso (Modules B) (.up ℤ)) (V ⋙ (a n).T) β
  have hδ (P : CochainComplex (Modules B) ℤ) :
      δ.app (DerivedCategory.Q.obj P) ≫ (b n).ε.app P = β.app P :=
    (b n).T.leftDerived_fac_app _ _ _ _ _
  have hδiso (P : CochainComplex (Modules B) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P) :
      IsIso (δ.app (DerivedCategory.Q.obj P)) := by
    have := (b n).computes P hP
    have := (a n).computes (U.obj P) (hk P hP)
    have hβ : IsIso (β.app P) := by
      dsimp only [β, NatTrans.comp_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      simp only [Category.id_comp]
      infer_instance
    have : IsIso (δ.app (DerivedCategory.Q.obj P) ≫ (b n).ε.app P) :=
      (hδ P).symm ▸ hβ
    exact IsIso.of_isIso_comp_right _ ((b n).ε.app P)
  have hδall (M : DerivedCategory (Modules B)) : IsIso (δ.app M) := by
    obtain ⟨P, hP, _, ⟨eP⟩⟩ := flat_representatives M
    have := hδiso P hP
    have : IsIso ((V ⋙ (a n).T).map eP.hom ≫ δ.app M) := by
      rw [δ.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left ((V ⋙ (a n).T).map eP.hom) _
  let : ∀ M, IsIso (δ.app M) := hδall
  have : IsIso δ := NatIso.isIso_of_isIso_app δ
  refine ⟨asIso δ, ?_⟩
  intro P
  simpa only [β, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_id, Category.id_comp, Category.comp_id, U, V, c, asIso_hom] using hδ P

/-- Flat common-quotient reduction gives the canonical derived comparison together
with its ordinary representative, strict quotient-transition and cone normalizations.

Source: Stacks 099L (section-derived-completion-noetherian), 03EK, 06YS, 06YT and 06YY
(blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower).

Proof:
1. Resolve a representative of M over B by a K-flat complex P with flat terms (06YS).
Flat scalar restriction makes Res P K-flat over R with flat terms; restriction leaves
underlying abelian sheaves unchanged, so it preserves the resolution quasi-isomorphism.
Thus a single P computes every reduction, with no compatible choices of resolutions.
2. The sheafified balanced maps p tensor r-bar to [rp], and [p] to p tensor 1,
identify Res P tensor_R S_n with P/I_n P. They are mutually inverse by balancing;
sections of the quotient coefficient ring are lifted locally, never globally (03EK).
3. Repeat over B. The submodule (I_n B)P equals I_n P: a generator (φ(j)b)p equals
φ(j)(bp), and the reverse inclusion takes b=1. Both tensors are therefore the same
quotient. The comparison and its inverse preserve every pure section s tensor p.
4. Apply this calculation in every degree. Both differential composites send s tensor p
to s tensor d(p); both naturality composites send it to s tensor h(p). Pure sections
locally generate the sheaf tensor, so these are actual equalities of sheaf morphisms.
5. The adjacent quotient-transition squares send s tensor p to t_n(s) tensor p.
Restrict to R and assemble them with Functor.ofOpSequence. Their components are
isomorphisms, hence give a strict tower isomorphism. Quotient cones send p to 1 tensor p;
the same calculation proves their transition compatibility and equality under the
comparison. The quotient maps are epimorphisms, with kernel locally I_n P, expressing
both identifications with the actual sheaf quotient, including its quotient projection.
6. The derived-change-of-rings counits compute both sides on this same P (06YT, 06YY).
The ordinary comparison is natural on complexes and inverts quasi-isomorphisms on the
flat-term K-flat resolving class. Descend it and its inverse by the universal resolving-
class construction (06XN). This gives the natural derived isomorphism and the displayed
counit normalization, proving independence of the resolution. Restriction itself is
localized from its exact termwise functor. -/
theorem nonempty_comparison
    (hflat : IsFlatOnSite (R := R)
      ((restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J B)))) :
    Nonempty (Comparison D a b) := by
  classical
  have : PreservesFiniteLimits (restriction φ) := restriction_preservesFiniteLimits
  have : PreservesFiniteColimits (restriction φ) := restriction_preservesFiniteColimits
  obtain ⟨O⟩ := nonempty_ordinaryCommonQuotientTower D a b
  let ordinary (n : ℕ) := Functor.mapHomologicalComplexCompIso (O.ordinary n) (.up ℤ)
  choose d hd using fun n ↦ derived_comparison_of_ordinary D a b
    (restriction_kflat hflat) n (ordinary n)
  refine ⟨{ res := (restriction φ).mapDerivedCategory
            resFactors := (restriction φ).mapDerivedCategoryFactors
            ordinary := ordinary
            ordinary_sections := ?_
            derived := d
            computes := fun n P _ _ ↦ hd n P
            representatives := flat_representatives
            strict := ?_ }⟩
  · intro n P i U s x
    exact O.ordinary_sections n (P.X i) U s x
  · intro P _ _
    let RP := ((restriction φ).mapHomologicalComplex (.up ℤ)).obj P
    let e₀ (n : ℕ) : leftLevel D a n P ≅ rightLevel D b n P :=
      ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).mapIso
        ((ordinary n).app P)
    let tL (n : ℕ) : leftLevel D a (n + 1) P ⟶ leftLevel D a n P :=
      { f := fun i ↦ (O.transition n).app (RP.X i)
        comm' := fun i j _ ↦ ((O.transition n).naturality (RP.d i j)).symm }
    let tR (n : ℕ) : rightLevel D b (n + 1) P ⟶ rightLevel D b n P :=
      (e₀ (n + 1)).inv ≫ tL n ≫ (e₀ n).hom
    let TL := Functor.ofOpSequence (X := fun n ↦ leftLevel D a n P) tL
    let TR := Functor.ofOpSequence (X := fun n ↦ rightLevel D b n P) tR
    let eh : TL ⟶ TR := NatTrans.ofOpSequence (fun n ↦ (e₀ n).hom) (by
      intro n
      simp only [TL, TR, Functor.ofOpSequence_map_homOfLE_succ]
      simp only [tR, Iso.hom_inv_id_assoc])
    have : ∀ n, IsIso (eh.app n) := fun n ↦ by
      change IsIso ((e₀ n.unop).hom)
      infer_instance
    have : IsIso eh := NatIso.isIso_of_isIso_app eh
    let e : TL ≅ TR := asIso eh
    let unitMap (n : ℕ) : RP ⟶ leftLevel D a n P :=
      { f := fun i ↦ (O.unit n).app (RP.X i)
        comm' := fun i j _ ↦ ((O.unit n).naturality (RP.d i j)).symm }
    let ηL : (Functor.const ℕᵒᵖ).obj RP ⟶ TL :=
      NatTrans.ofOpSequence unitMap (by
        intro n
        simp only [TL, Functor.const_obj_map,
          Functor.ofOpSequence_map_homOfLE_succ]
        apply HomologicalComplex.Hom.ext
        funext i
        exact (congrArg (fun f ↦ f.app (RP.X i)) (O.unit_transition n)).symm)
    let ηR := ηL ≫ e.hom
    have sections (n : ℕ) (i : ℤ) (U : Cᵒᵖ)
        (s : (D.S.obj (op n)).obj.obj U) (x : (P.X i).val.obj U) :
        (((e₀ n).hom).f i).val.app U
          (scalarSection (a n) ((restriction φ).obj (P.X i)) U s x) =
            scalarSection (b n) (P.X i) U s x :=
      O.ordinary_sections n (P.X i) U s x
    have inverse_sections (n : ℕ) (i : ℤ) (U : Cᵒᵖ)
        (s : (D.S.obj (op n)).obj.obj U) (x : (P.X i).val.obj U) :
        (((e₀ n).inv).f i).val.app U
          (scalarSection (b n) (P.X i) U s x) =
            scalarSection (a n) ((restriction φ).obj (P.X i)) U s x := by
      rw [← sections n i U s x]
      exact congrArg (fun f ↦ (f.f i).val.app U
        (scalarSection (a n) ((restriction φ).obj (P.X i)) U s x)) (e₀ n).hom_inv_id
    refine ⟨tL, tR, e, ηL, ηR, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · intro n
      rfl
    · intro n i U s x
      exact O.transition_sections n (RP.X i) U s x
    · intro n i U s x
      change (((e₀ n).hom).f i).val.app U
        (((tL n).f i).val.app U
          ((((e₀ (n + 1)).inv).f i).val.app U
            (scalarSection (b (n + 1)) (P.X i) U s x))) = _
      rw [inverse_sections]
      change (((e₀ n).hom).f i).val.app U
        (((O.transition n).app (RP.X i)).val.app U
          (scalarSection (a (n + 1)) (RP.X i) U s x)) = _
      exact (congrArg (fun y ↦ (((e₀ n).hom).f i).val.app U y)
        (O.transition_sections n ((restriction φ).obj (P.X i)) U s x)).trans
          (sections n i U _ x)
    · intro n i U x
      constructor
      · exact O.unit_sections n (RP.X i) U x
      · change (((e₀ n).hom).f i).val.app U
          (((O.unit n).app (RP.X i)).val.app U x) = _
        rw [O.unit_sections]
        exact sections n i U 1 x
    · intro n i
      exact O.unit_epi n (RP.X i)
    · intro n i U x
      exact O.unit_kernel n (RP.X i) U x

end SheafOfModules.CommonQuotientReduction
