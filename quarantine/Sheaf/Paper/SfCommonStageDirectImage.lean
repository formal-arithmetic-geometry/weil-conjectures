/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.SfCommonStageWeilCohomology
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.WeilIndSheafCategory
import Sheaf.Paper.CommonStagePullbackIdentity
import Sheaf.Paper.SfRationalDirectImageAdjunction
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Common-stage direct image and its induced Weil structure

Source: Bhatt--Scholze 6.8.14(2), 6.8.15; blueprint derived-direct-image convention
(blueprint: def-weil-derived-direct-image).
The existing integral tower construction is reexported. Its rational/common-stage
extension is characterized by the derived inverse-image adjunction. Taking fixed pairs
uses the mate of the normalized Frobenius pullback square, not a derived category of pairs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures


namespace DirectImageAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u₁ v₁ u₂ v₂
variable {I : Type w} [Preorder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
  {S : StageSystem C} {T : StageSystem D} (L : S.Morphism T)
  (R : ∀ i, D i ⥤ C i) (a : ∀ i, L.Φ i ⊣ R i)
  (b : ∀ {i j : I} (h : i ≤ j), R i ⋙ S.T h ≅ T.T h ⋙ R j)
  (hb : ∀ {i j : I} (h : i ≤ j) (K : D i),
    (L.Φ j).map ((b h).hom.app K) ≫ (a j).counit.app ((T.T h).obj K) =
      (L.β h).inv.app ((R i).obj K) ≫ (T.T h).map ((a i).counit.app K))

include hb

private theorem mateUnit {i j : I} (h : i ≤ j) (K : C i) :
    (S.T h).map ((a i).unit.app K) ≫ (b h).hom.app ((L.Φ i).obj K) =
      (a j).unit.app ((S.T h).obj K) ≫ (R j).map ((L.β h).inv.app K) := by
  apply ((a j).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hb]
  have hn := (L.β h).inv.naturality ((a i).unit.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at hn
  rw [reassoc_of% hn]
  rw [← (T.T h).map_comp, (a i).left_triangle_components, (T.T h).map_id]
  simp only [Category.comp_id]
  rw [(a j).counit_naturality, ← Category.assoc,
    (a j).left_triangle_components ((S.T h).obj K)]
  exact (Category.id_comp _).symm

private theorem mateCoherence {i j k : I} (h : i ≤ j) (h' : j ≤ k) (K : D i) :
    (S.T h').map ((b h).hom.app K) ≫ (b h').hom.app ((T.T h).obj K) ≫
      (R k).map ((T.assoc h h').hom.app K) =
    (S.assoc h h').hom.app ((R i).obj K) ≫ (b (h.trans h')).hom.app K := by
  apply ((a k).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [(a k).counit_naturality, reassoc_of% (hb h' ((T.T h).obj K))]
  have hn := (L.β h').inv.naturality ((b h).hom.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at hn
  rw [reassoc_of% hn]
  rw [← (T.T h').map_comp_assoc, hb, (T.T h').map_comp]
  have ht := (T.assoc h h').hom.naturality ((a i).counit.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at ht
  simp only [Category.assoc]
  rw [ht]
  have hc := L.coh_inv h h' ((R i).obj K)
  have hc' : (L.β h').inv.app ((S.T h).obj ((R i).obj K)) ≫
      (T.T h').map ((L.β h).inv.app ((R i).obj K)) ≫
      (T.assoc h h').hom.app ((L.Φ i).obj ((R i).obj K)) =
      (L.Φ k).map ((S.assoc h h').hom.app ((R i).obj K)) ≫
        (L.β (h.trans h')).inv.app ((R i).obj K) := by
    rw [← cancel_epi ((L.Φ k).map ((S.assoc h h').inv.app ((R i).obj K)))]
    rw [reassoc_of% hc]
    simp only [Iso.inv_hom_id_app, Category.comp_id,
      ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hc', hb]

private def mateFamily : T.Morphism S where
  Φ := R
  β := b
  coh := mateCoherence L R a b hb

private def mateFamilyUnit : StageSystem.Morphism.Hom (StageSystem.Morphism.id S)
    (L.comp (mateFamily L R a b hb)) where
  τ i := (a i).unit
  comm {i j} h K := by
    simp only [StageSystem.Morphism.id_β_hom_app, StageSystem.Morphism.comp_β_hom_app]
    change (S.T h).map ((a i).unit.app K) ≫
      ((b h).hom.app ((L.Φ i).obj K) ≫ (R j).map ((L.β h).hom.app K)) =
      𝟙 _ ≫ (a j).unit.app ((S.T h).obj K)
    rw [Category.id_comp]
    rw [← Category.assoc, mateUnit L R a b hb, Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    change (a j).unit.app ((S.T h).obj K) ≫
      (R j).map (𝟙 ((L.Φ j).obj ((S.T h).obj K))) = _
    rw [(R j).map_id]
    exact Category.comp_id _

private def mateFamilyCounit : StageSystem.Morphism.Hom
    ((mateFamily L R a b hb).comp L) (StageSystem.Morphism.id T) where
  τ i := (a i).counit
  comm {i j} h K := by
    simp only [StageSystem.Morphism.id_β_hom_app, StageSystem.Morphism.comp_β_hom_app]
    change (T.T h).map ((a i).counit.app K) ≫ 𝟙 _ =
      ((L.β h).hom.app ((R i).obj K) ≫ (L.Φ j).map ((b h).hom.app K)) ≫
        (a j).counit.app ((T.T h).obj K)
    rw [Category.comp_id, Category.assoc, hb, Iso.hom_inv_id_app_assoc]

end DirectImageAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def descendStageAdjunction
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {C' : I → Type*} [∀ i, Category (C' i)]
    {S : StageSystem C} {T : StageSystem C'}
    (L : S.Morphism T) (R : T.Morphism S) (a : ∀ i, L.Φ i ⊣ R.Φ i)
    (η : StageSystem.Morphism.Hom (StageSystem.Morphism.id S) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id T))
    (hη : ∀ i, η.τ i = (a i).unit) (hε : ∀ i, ε.τ i = (a i).counit) :
    L.functor ⊣ R.functor where
  unit := StageSystem.Morphism.functorIdIso.inv ≫
    StageSystem.Morphism.descNatTrans η ≫ (L.functorCompIso R).hom
  counit := (R.functorCompIso L).inv ≫
    StageSystem.Morphism.descNatTrans ε ≫ StageSystem.Morphism.functorIdIso.hom
  left_triangle_components X := by
    simp only [NatTrans.comp_app, StageSystem.Morphism.functorIdIso_inv_app,
      StageSystem.Morphism.functorIdIso_hom_app,
      StageSystem.Morphism.functorCompIso_hom_app,
      StageSystem.Morphism.functorCompIso_inv_app,
      Category.id_comp, Category.comp_id, StageSystem.Morphism.descNatTrans_app,
      hη, hε, StageSystem.Morphism.functor_map_ι]
    change (T.ι X.stage).map ((L.Φ X.stage).map ((a X.stage).unit.app X.obj)) ≫
      (T.ι X.stage).map ((a X.stage).counit.app ((L.Φ X.stage).obj X.obj)) = _
    rw [← CategoryTheory.Functor.map_comp]
    change (T.ι X.stage).map _ =
      𝟙 ((T.ι X.stage).obj ((L.Φ X.stage).obj X.obj))
    calc
      _ = (T.ι X.stage).map (𝟙 ((L.Φ X.stage).obj X.obj)) :=
        congrArg ((T.ι X.stage).map) ((a X.stage).left_triangle_components X.obj)
      _ = _ := (T.ι X.stage).map_id _
  right_triangle_components X := by
    simp only [NatTrans.comp_app, StageSystem.Morphism.functorIdIso_inv_app,
      StageSystem.Morphism.functorIdIso_hom_app,
      StageSystem.Morphism.functorCompIso_hom_app,
      StageSystem.Morphism.functorCompIso_inv_app,
      Category.id_comp, Category.comp_id, StageSystem.Morphism.descNatTrans_app,
      hη, hε, StageSystem.Morphism.functor_map_ι]
    change (S.ι X.stage).map ((a X.stage).unit.app ((R.Φ X.stage).obj X.obj)) ≫
      (S.ι X.stage).map ((R.Φ X.stage).map ((a X.stage).counit.app X.obj)) = _
    rw [← CategoryTheory.Functor.map_comp]
    change (S.ι X.stage).map _ =
      𝟙 ((S.ι X.stage).obj ((R.Φ X.stage).obj X.obj))
    calc
      _ = (S.ι X.stage).map (𝟙 ((R.Φ X.stage).obj X.obj)) :=
        congrArg ((S.ι X.stage).map) ((a X.stage).right_triangle_components X.obj)
      _ = _ := (S.ι X.stage).map_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalStageAdjunction_descends
    (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X))
    (R : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (hΦ : L.Φ = (fun E ↦ rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f))
    (hβ : ∀ (E F : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ F)
      (K : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y),
      HEq ((L.β h).app K) (commonStagePullbackComparison l Ω f ⟨E, K⟩ F h))
    (a : ∀ E, L.Φ E ⊣ R.Φ E)
    (η : StageSystem.Morphism.Hom (StageSystem.Morphism.id _) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id _))
    (hη : ∀ E, η.τ E = (a E).unit) (hε : ∀ E, ε.τ E = (a E).counit) :
    (commonStageDerivedPullback l Ω f).IsLeftAdjoint := by
  have hF : L.functor = commonStageDerivedPullback l Ω f := by
    apply (commonStageDerivedPullback_existsUnique l Ω f).unique
      (y₁ := L.functor)
    · rcases L with ⟨Φ, β, coh⟩
      dsimp only at hΦ
      subst Φ
      constructor
      · intro P
        rfl
      · intro P Q F hP hQ k
        apply heq_of_eq
        change StageSystem.PairCategory.mkHom
          (X := commonStagePullbackObject l Ω f P)
          (Y := commonStagePullbackObject l Ω f Q) F hP hQ
          ((β hP).hom.app P.obj ≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
              f).map k ≫ (β hQ).inv.app Q.obj) = _
        have hp := congrArg Iso.hom (eq_of_heq (hβ P.stage F hP P.obj))
        have hq := congrArg Iso.inv (eq_of_heq (hβ Q.stage F hQ Q.obj))
        dsimp only [Iso.app_hom, Iso.app_inv] at hp hq
        rw [hp, hq]
    · exact (commonStageDerivedPullback_existsUnique l Ω
        f).exists.choose_spec
  have h := (descendStageAdjunction L R a η ε hη hε).isLeftAdjoint
  rwa [hF] at h


private theorem sfModelFrobenius_isEquivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).IsEquivalence := by
  let := sfWeilPrimeInvertible D l hl X₀
  let e := D.geometricFrobenius X₀
  let X := (D.geometricFiber X₀).left
  have : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact (D.geometricFiber X₀).hom :=
    inferInstanceAs (QuasiCompact
      (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber X₀).hom
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber X₀).hom
  have : IsNoetherian X := ⟨⟩
  have : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n) :=
    ⟨AlgebraicGeometry.exists_topologicalKrullDim_le (D.geometricFiber X₀).hom⟩
  have : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)) := ⟨fun x ↦ by
    apply isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk x))
    simpa only [map_natCast] using (isUnit_of_invertible (l : X.residueField x))⟩
  obtain ⟨S, hs, _⟩ := rationalCoefficientCategoryComparison l Ω D hl
  let unit : commonStageDerivedPullback l Ω (𝟙 X) ≅ 𝟭 _ :=
    eqToIso (congrArg₂ (fun hX hY ↦
      @commonStageDerivedPullback l _ Ω _ _ _ X X (𝟙 X) hX hY)
      (Subsingleton.elim (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
        (fun x ↦ fdResidueInvertible l X x))
      (Subsingleton.elim (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
        (fun x ↦ fdResidueInvertible l X x))) ≪≫
      (commonStageDerivedPullback_identity l Ω S hs X).some
  let c₁ : commonStageDerivedPullback l Ω e.hom ⋙
      commonStageDerivedPullback l Ω e.inv ≅ 𝟭 _ :=
    (zlPullComp l Ω e.inv e.hom).symm ≪≫
      eqToIso (congrArg (fun f ↦ commonStageDerivedPullback l Ω f) e.inv_hom_id) ≪≫ unit
  let c₂ : commonStageDerivedPullback l Ω e.inv ⋙
      commonStageDerivedPullback l Ω e.hom ≅ 𝟭 _ :=
    (zlPullComp l Ω e.hom e.inv).symm ≪≫
      eqToIso (congrArg (fun f ↦ commonStageDerivedPullback l Ω f) e.hom_inv_id) ≪≫ unit
  exact Functor.IsEquivalence.mk' (commonStageDerivedPullback l Ω e.inv) c₁.symm c₂

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Composition of geometric pullbacks, descended from finite integral reductions.
Source: Stacks 099N(5), BS 6.8.15 (blueprint: def-weil-derived-direct-image). -/
def sfModelPullComposition {Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] (f : X₀ ⟶ Y₀) (g : Y₀ ⟶ Z₀) :
    zlPull D l hl Ω (f ≫ g) ≅ zlPull D l hl Ω g ⋙ zlPull D l hl Ω f :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := sfWeilPrimeInvertible D l hl Z₀
  eqToIso (congrArg (fun h ↦ commonStageDerivedPullback l Ω h)
    (congrArg (fun h ↦ h.left)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map_comp f g))) ≪≫
    zlPullComp l Ω (zlFiberMap D f) (zlFiberMap D g)

/-- The normalized inverse-image square, built from the composition comparisons.
Source: Stacks 0D6G, BS 6.8.15 (blueprint: def-weil-derived-direct-image). -/
def sfModelPullSquare {V₀ W₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (j : X₀ ⟶ Y₀) (a : W₀ ⟶ Y₀) (b : V₀ ⟶ X₀) (jW : V₀ ⟶ W₀)
    (h : b ≫ j = jW ≫ a) :
    zlPull D l hl Ω a ⋙ zlPull D l hl Ω jW ≅
      zlPull D l hl Ω j ⋙ zlPull D l hl Ω b :=
  (sfModelPullComposition D l hl Ω jW a).symm ≪≫
    eqToIso (congrArg (fun f ↦ zlPull D l hl Ω f) h.symm) ≪≫
      sfModelPullComposition D l hl Ω b j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual geometric inverse image has its constructible derived right adjoint.
Source: BS 6.8.14(2), 6.8.15 (blueprint: def-weil-derived-direct-image).
Proof: ordinary completed-ring derived direct image is right adjoint to completed
inverse image. CompletedCoefficientPushforwardComparison identifies it with the
specified finite-reduction tower and derived limit. SfIntegralDirectImageConstructible
restricts it to bounded constructible objects for finite-type schemes over the field.
Rational transport preserves the adjunction; scalar-extension comparisons preserve
its unit and counit. PbcDescentFunctors descends those functors and maps to common stages.
The descended unit and counit satisfy the triangle identities at each finite stage. -/
theorem sfModelPull_isLeftAdjoint (f : X₀ ⟶ Y₀) :
    (zlPull D l hl Ω f).IsLeftAdjoint := by
  let := sfWeilPrimeInvertible D l hl X₀
  let := sfWeilPrimeInvertible D l hl Y₀
  obtain ⟨L, R, hΦ, hβ, a, β, hmate⟩ :=
    sfRationalDirectImageAdjunctions D l hl Ω f
  exact rationalStageAdjunction_descends l Ω (zlFiberMap D f) L
    (DirectImageAdjunction.mateFamily L R a β hmate) hΦ hβ a
    (DirectImageAdjunction.mateFamilyUnit L R a β hmate)
    (DirectImageAdjunction.mateFamilyCounit L R a β hmate) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- Derived direct image on the actual geometric common-stage category, determined
up to its unique adjunction-compatible isomorphism. The universal property specifies
its data; this is not a choice of an arbitrary functor.
Source: BS 6.8.14(2), 6.8.15 (blueprint: def-weil-derived-direct-image). -/
@[irreducible]
def sfModelDerivedPush (f : X₀ ⟶ Y₀) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left :=
  @Functor.rightAdjoint _ _ _ _ (zlPull D l hl Ω f)
    (sfModelPull_isLeftAdjoint D l hl Ω f)

/-- The unit and counit specifying the geometric derived direct image.
Source: BS 6.8.14(2), 6.8.15 (blueprint: def-weil-derived-direct-image). -/
@[irreducible]
def sfModelDerivedAdjunction (f : X₀ ⟶ Y₀) :
    zlPull D l hl Ω f ⊣ sfModelDerivedPush D l hl Ω f := by
  delta sfModelDerivedPush
  exact @Adjunction.ofIsLeftAdjoint _ _ _ _ (zlPull D l hl Ω f)
    (sfModelPull_isLeftAdjoint D l hl Ω f)

/-- The geometric open-exchange arrow is the mate of the normalized pullback square.
Source: Stacks 0D6G (blueprint: def-weil-derived-direct-image). -/
def sfModelDerivedExchange {V₀ W₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (j : X₀ ⟶ Y₀) (a : W₀ ⟶ Y₀) (b : V₀ ⟶ X₀) (jW : V₀ ⟶ W₀)
    (h : b ≫ j = jW ≫ a)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    (zlPull D l hl Ω a).obj ((sfModelDerivedPush D l hl Ω j).obj K) ⟶
      (sfModelDerivedPush D l hl Ω jW).obj ((zlPull D l hl Ω b).obj K) :=
  (sfModelDerivedAdjunction D l hl Ω jW).homEquiv _ _
    ((sfModelPullSquare D l hl Ω j a b jW h).hom.app
        ((sfModelDerivedPush D l hl Ω j).obj K) ≫
      (zlPull D l hl Ω b).map ((sfModelDerivedAdjunction D l hl Ω j).counit.app K))

/-- The normalized shift structure on geometric inverse image.
Source: BS 6.8.15, cohomological pullback convention
(blueprint: def-weil-derived-direct-image). -/
@[instance_reducible]
def sfModelPullCommShift (f : X₀ ⟶ Y₀) : (zlPull D l hl Ω f).CommShift ℤ :=
  cast (congrArg (fun F ↦ F.CommShift ℤ)
    (congrArg₂ (fun hX hY ↦ @commonStageDerivedPullback l _ Ω _ _ _ _ _
      (zlFiberMap D f) hX hY)
      (Subsingleton.elim (constructiblePullbackResidueUnits D l hl
        (D.geometricFiber X₀).left) (sfWeilPrimeInvertible D l hl X₀))
      (Subsingleton.elim (constructiblePullbackResidueUnits D l hl
        (D.geometricFiber Y₀).left) (sfWeilPrimeInvertible D l hl Y₀))))
    ((constructible_pullback_t_exact D l hl Ω (Padic.finiteCoefficientBase l Ω)
      (zlFiberMap D f)).2.some).commShift

/-- The uniquely adjunction-compatible shift structure on derived direct image.
Source: Stacks 05TE, derived adjunction
(blueprint: def-weil-derived-direct-image). -/
@[instance_reducible]
def sfModelPushCommShift (f : X₀ ⟶ Y₀) : (sfModelDerivedPush D l hl Ω f).CommShift ℤ :=
  letI := sfModelPullCommShift D l hl Ω f
  (sfModelDerivedAdjunction D l hl Ω f).rightAdjointCommShift ℤ

/-- The prescribed image of a connecting map, including the derived shift comparison.
Source: Stacks 05TE (blueprint: def-weil-derived-direct-image). -/
def sfModelPushConnecting (f : X₀ ⟶ Y₀)
    {K L : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left}
    (w : K ⟶ L⟦(1 : ℤ)⟧) :
    (sfModelDerivedPush D l hl Ω f).obj K ⟶
      ((sfModelDerivedPush D l hl Ω f).obj L)⟦(1 : ℤ)⟧ :=
  letI := sfModelPushCommShift D l hl Ω f
  (sfModelDerivedPush D l hl Ω f).map w ≫
    ((sfModelDerivedPush D l hl Ω f).commShiftIso (1 : ℤ)).hom.app L

/-- The induced inverse image of fixed pairs admits the induced derived direct image.
Source: blueprint Weil-equivariant derived operations
(blueprint: def-weil-derived-direct-image).
Proof: take the right-adjoint mate of zlFrobeniusSquare using the derived adjunction.
Frobenius is an automorphism on both schemes; the inverse square supplies the inverse
mate. Its unit/counit equations equip the geometric direct image with its induced
invertible Weil structure and restrict the adjunction to equivariant arrows. -/
theorem sfModelWeilPull_isLeftAdjoint (f : X₀ ⟶ Y₀) :
    (IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f)).IsLeftAdjoint := by
  have := sfModelFrobenius_isEquivalence D l hl Ω X₀
  have := sfModelFrobenius_isEquivalence D l hl Ω Y₀
  exact (IsoAlgebra.mapOfNatIsoAdjunction (sfModelDerivedAdjunction D l hl Ω f)
    (zlFrobeniusSquare D l hl Ω f)
    (IsoAlgebra.mateIso (sfModelDerivedAdjunction D l hl Ω f)
      (zlFrobeniusSquare D l hl Ω f)) rfl).isLeftAdjoint

/-- Derived direct image of Weil fixed pairs; its underlying functor is geometric Rf_*.
Source: blueprint Weil-equivariant derived operations
(blueprint: def-weil-derived-direct-image). -/
@[irreducible]
def sfModelWeilDerivedPush (f : X₀ ⟶ Y₀) :
    sfCommonStageWeilComplex D l hl X₀ Ω ⥤ sfCommonStageWeilComplex D l hl Y₀ Ω :=
  @Functor.rightAdjoint _ _ _ _ (IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f))
    (sfModelWeilPull_isLeftAdjoint D l hl Ω f)

/-- The canonical derived inverse-image/direct-image adjunction on Weil pairs.
Source: BS 6.8.15 (blueprint: def-weil-derived-direct-image). -/
@[irreducible]
def sfModelWeilDerivedAdjunction (f : X₀ ⟶ Y₀) :
    IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f) ⊣
      sfModelWeilDerivedPush D l hl Ω f := by
  delta sfModelWeilDerivedPush
  exact @Adjunction.ofIsLeftAdjoint _ _ _ _ (IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f))
    (sfModelWeilPull_isLeftAdjoint D l hl Ω f)

/-- Forgetting the induced Weil structure gives the actual geometric derived image.
Source: BS 6.8.14(2), blueprint Weil comparison
(blueprint: def-weil-derived-direct-image).
Proof: the mate construction in sfModelWeilPull_isLeftAdjoint has exactly the
geometric derived-image carrier. Uniqueness of right adjoints identifies that
construction with sfModelWeilDerivedPush, compatibly with its unit and counit.
Forgetting gives the displayed natural isomorphism. The counit equation
characterizes it by the geometric adjunction, proving uniqueness. -/
theorem sfModelWeilDerivedPush_forget (f : X₀ ⟶ Y₀) :
    ∃! e : sfModelWeilDerivedPush D l hl Ω f ⋙ sfCommonStageWeilForget D l hl Y₀ Ω ≅
        sfCommonStageWeilForget D l hl X₀ Ω ⋙ sfModelDerivedPush D l hl Ω f,
      ∀ K : sfCommonStageWeilComplex D l hl X₀ Ω,
        (zlPull D l hl Ω f).map (e.hom.app K) ≫
            (sfModelDerivedAdjunction D l hl Ω f).counit.app K.carrier =
          ((sfModelWeilDerivedAdjunction D l hl Ω f).counit.app K).hom.f := by
  have := sfModelFrobenius_isEquivalence D l hl Ω X₀
  have := sfModelFrobenius_isEquivalence D l hl Ω Y₀
  let adj := sfModelDerivedAdjunction D l hl Ω f
  let lifted := IsoAlgebra.mapOfNatIsoAdjunction adj
    (zlFrobeniusSquare D l hl Ω f)
    (IsoAlgebra.mateIso adj (zlFrobeniusSquare D l hl Ω f)) rfl
  let e := Functor.isoWhiskerRight
    ((sfModelWeilDerivedAdjunction D l hl Ω f).rightAdjointUniq lifted)
    (IsoAlgebra.forget (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω))
  have he : ∀ K : sfCommonStageWeilComplex D l hl X₀ Ω,
      (zlPull D l hl Ω f).map (e.hom.app K) ≫ adj.counit.app K.carrier =
        ((sfModelWeilDerivedAdjunction D l hl Ω f).counit.app K).hom.f := by
    intro K
    exact congrArg (fun k ↦ k.hom.f)
      ((sfModelWeilDerivedAdjunction D l hl Ω f).rightAdjointUniq_hom_app_counit lifted K)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (adj.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit, sfCommonStageWeilForget,
    IsoAlgebra.forget_obj, Functor.id_obj, Functor.comp_obj, adj] using (he' K).trans (he K).symm

/-- The forgetful comparison specified by the adjunction counit equation above.
Source: BS 6.8.14(2), blueprint Weil comparison
(blueprint: def-weil-derived-direct-image). -/
def sfModelWeilDerivedPushForget (f : X₀ ⟶ Y₀) :=
  (sfModelWeilDerivedPush_forget D l hl Ω f).exists.choose

end WeilConjectures
