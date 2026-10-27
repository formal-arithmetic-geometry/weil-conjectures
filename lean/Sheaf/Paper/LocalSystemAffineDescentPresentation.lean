/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Sheaf.Paper.FiniteAffineProEtaleRefinement
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-! # Affine descent presentation of a locally constant pro-etale sheaf

Source: blueprint, sec-six-functors-basics, stratified lattice scheme proof (2);
Stacks, Tags 0989, 098Z, 023Q, 03YW, 00WM, 001P and 023V
(blueprint: lem-sfb-local-system-affine-descent-presentation).

The auxiliary definitions name concrete coproducts, component sections,
and the pointwise realization condition for the descent isomorphism. The descent datum
is the existing `Over.DescentDatum`, whose `transport_transport` field is the cocycle
condition for every test scheme, hence in particular on the triple fibre product.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u i

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The actual scheme coproduct of copies of the base, with its codiagonal.
Source: Stacks, Tags 01JB and 03YW
(blueprint: lem-sfb-local-system-affine-descent-presentation). -/
def localSystemCopies (B : Scheme.{u}) (S : Type u) : Over B :=
  Over.mk (Sigma.desc (fun _ : S ↦ 𝟙 B))

/-- The relative representable functor on weakly etale test schemes. `ULift` only
places the Hom sets in the fixed larger universe of sheaf values.
Source: Stacks, Tags 03YW and 098Z
(blueprint: lem-sfb-local-system-affine-descent-presentation). -/
def localSystemCopiesHom (B : Scheme.{u}) (S : Type u) :
    B.ProEtᵒᵖ ⥤ Type (u + 1) :=
  (ProEt.forget B).op ⋙ yoneda.obj (localSystemCopies B S) ⋙ uliftFunctor.{u + 1, u}

/-- A constant label is the corresponding component section, on any test scheme.
Source: Stacks, Tag 03YW
(blueprint: lem-sfb-local-system-affine-descent-presentation). -/
def localSystemLabel {B W : Scheme.{u}} (S : Type u) (w : W ⟶ B) (s : S) :
    Over.mk w ⟶ localSystemCopies B S :=
  Over.homMk (w ≫ Sigma.ι (fun _ : S ↦ B) s) (by simp [localSystemCopies])

/-- A point of the pullback is viewed as a point of the original scheme, using
Mathlib's actual map-pullback adjunction, with no choice of a comparison map.
Source: Stacks, Tag 023V
(blueprint: lem-sfb-local-system-affine-descent-presentation). -/
def localSystemPullbackPoint {B V W : Scheme.{u}} (T : Over V)
    (f : B ⟶ V) (w : W ⟶ B) (a : Over.mk w ⟶ (Over.pullback f).obj T) :
    Over.mk (w ≫ f) ⟶ T :=
  ((Over.mapPullbackAdj f).homEquiv (Over.mk w) T).symm a

/-- The isomorphism of the two pullbacks realizes precisely the specified transport,
for every point over the overlap. This characterizes an actual scheme morphism.
Source: Stacks, Tags 001P and 023V
(blueprint: lem-sfb-local-system-affine-descent-presentation). -/
def LocalSystemTransitionRealizes {X V B : Scheme.{u}} {p : V ⟶ X} {T : Over V}
    (D : Over.DescentDatum p T) (r₁ r₂ : B ⟶ V) (h : r₁ ≫ p = r₂ ≫ p)
    (δ : (Over.pullback r₁).obj T ≅ (Over.pullback r₂).obj T) : Prop :=
  ∀ (W : Scheme.{u}) (w : W ⟶ B) (a : Over.mk w ⟶ (Over.pullback r₁).obj T),
    localSystemPullbackPoint T r₂ w (a ≫ δ.hom) =
      D.transport (w ≫ r₁) (w ≫ r₂) (by simp only [Category.assoc, h])
        (localSystemPullbackPoint T r₁ w a)

/-- The clopen pieces of a source component and the identity map on each piece.
Source: blueprint, stratified lattice scheme proof (2), and Stacks, Tag 03YW
(blueprint: lem-sfb-local-system-affine-descent-presentation). -/
def LocalSystemTransitionClopen {X V B : Scheme.{u}} {p : V ⟶ X} (S : Type u)
    (D : Over.DescentDatum p (localSystemCopies V S))
    (r₁ r₂ : B ⟶ V) (h : r₁ ≫ p = r₂ ≫ p) : Prop :=
  ∀ s : S,
    IsClopenDecomposition B S (fun t ↦
      (D.transport r₁ r₂ h (localSystemLabel S r₁ s)).left ⁻¹ᵁ
        (Sigma.ι (fun _ : S ↦ V) t).opensRange) ∧
    ∀ t : S,
      ((D.transport r₁ r₂ h (localSystemLabel S r₁ s)).left ⁻¹ᵁ
        (Sigma.ι (fun _ : S ↦ V) t).opensRange).ι ≫
          (D.transport r₁ r₂ h (localSystemLabel S r₁ s)).left =
      (((D.transport r₁ r₂ h (localSystemLabel S r₁ s)).left ⁻¹ᵁ
        (Sigma.ι (fun _ : S ↦ V) t).opensRange).ι ≫ r₂) ≫
          Sigma.ι (fun _ : S ↦ V) t

-- Disjoint-cover gluing follows the proof of EtaleDisjointCover and
-- EtaleCoproductRepresentation in the source library (Stacks 03RV and 02W5),
-- using pro-etale open covers and terminal sections on empty test objects.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma comp_map_eq_of_disjoint
    {X : Scheme.{u}} {V : X.ProEt} {ι : Type*}
    (G : Sheaf (topology X) (Type (u + 1))) (W : ι → X.ProEt) (π : ∀ i, W i ⟶ V)
    [∀ i, Mono (π i)]
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base))
    {E : Type (u + 1)} (x : ∀ i, E ⟶ G.obj.obj (op (W i))) ⦃Z : X.ProEt⦄ ⦃i j : ι⦄ (a : Z ⟶ W i)
    (b : Z ⟶ W j) (h : a ≫ π i = b ≫ π j) :
    x i ≫ G.obj.map a.op = x j ≫ G.obj.map b.op := by
  by_cases hij : i = j
  · subst hij
    obtain rfl : a = b := (cancel_mono (π i)).mp h
    rfl
  · -- the source `Z` is empty, so `G Z` is terminal
    have hZ : IsEmpty Z.left := ⟨fun z ↦ by
      have hz := congrArg (fun m ↦ m.left.base z) h
      change (a.left ≫ (π i).left) z = (b.left ≫ (π j).left) z at hz
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hz
      exact Set.disjoint_left.mp (hdisj i j hij) ⟨a.left z, rfl⟩ ⟨b.left z, hz.symm⟩⟩
    exact (ProEt.isTerminalSectionsOfIsEmpty G Z).hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **A sheaf sends a disjoint cover to a product**: if the pairwise disjoint subobjects
`π i : W i ⟶ V` cover `V` in the small pro-etale topology, then the restriction maps exhibit
`G V` as the product of the `G (W i)`. -/
private theorem isIso_piLift_of_disjoint
    {X : Scheme.{u}} {V : X.ProEt} {ι : Type*}
    (G : Sheaf (topology X) (Type (u + 1))) (W : ι → X.ProEt) (π : ∀ i, W i ⟶ V)
    [∀ i, Mono (π i)]
    (hcov : Sieve.ofArrows W π ∈ topology X V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base))
    [HasProduct fun i ↦ G.obj.obj (op (W i))] :
    IsIso (Pi.lift fun i ↦ G.obj.map (π i).op) := by
  refine isIso_of_yoneda_map_bijective _ fun E ↦ ⟨fun x y hxy ↦ ?_, fun φ ↦ ?_⟩
  · obtain ⟨t, -, ht⟩ := G.property.existsUnique_amalgamation_ofArrows π hcov
      (fun i ↦ x ≫ G.obj.map (π i).op) (comp_map_eq_of_disjoint G W π hdisj _)
    refine (ht x fun i ↦ rfl).trans (ht y fun i ↦ ?_).symm
    simpa using (congrArg (· ≫ Pi.π _ i) hxy).symm
  · obtain ⟨t, ht, -⟩ := G.property.existsUnique_amalgamation_ofArrows π hcov
      (fun i ↦ φ ≫ Pi.π _ i) (comp_map_eq_of_disjoint G W π hdisj _)
    exact ⟨t, Pi.hom_ext _ _ fun i ↦ by simpa using ht i⟩


-- Compose a weakly etale object with the open coprojection.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def componentFunctor {ι : Type 0} (X : ι → Scheme.{u}) (i : ι) :
    (X i).ProEt ⥤ (∐ X).ProEt :=
  MorphismProperty.Over.map (f := Sigma.ι X i) ⊤ (inferInstance : WeaklyEtale (Sigma.ι X i))

-- The counit supplies the pullback projections, naturally in the test object.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def componentProjection {ι : Type 0} (X : ι → Scheme.{u}) (i : ι) :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ (Sigma.ι X i) ⋙
      componentFunctor X i ⟶ 𝟭 (∐ X).ProEt :=
  (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.WeaklyEtale ⊤ (Sigma.ι X i)
    (inferInstance : WeaklyEtale (Sigma.ι X i)) trivial).counit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def componentRestriction {ι : Type 0} (X : ι → Scheme.{u})
    (F : Sheaf (topology (∐ X)) (Type (u + 1))) (i : ι) :
    F.obj ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (Sigma.ι X i) ⋙
      componentFunctor X i).op ⋙ F.obj where
  app W := F.obj.map ((componentProjection X i).app W.unop).op
  naturality W W' f := by
    change F.obj.map f ≫ F.obj.map ((componentProjection X i).app W'.unop).op =
      F.obj.map ((componentProjection X i).app W.unop).op ≫
        F.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (Sigma.ι X i) ⋙
          componentFunctor X i).map f.unop).op
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    change F.obj.map (((componentProjection X i).app W'.unop ≫ f.unop).op) = _
    exact congrArg (fun g ↦ F.obj.map g.op) ((componentProjection X i).naturality f.unop).symm

-- The disjoint-cover theorem identifies sections with the product of their restrictions.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem componentRestriction_isIso {ι : Type 0} (X : ι → Scheme.{u})
    (F : Sheaf (topology (∐ X)) (Type (u + 1))) :
    IsIso (Pi.lift (componentRestriction X F)) := by
  have happ (W : (∐ X).ProEtᵒᵖ) :
      IsIso ((Pi.lift (componentRestriction X F)).app W) := by
    let D (i : ι) := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (Sigma.ι X i) ⋙
      componentFunctor X i).obj W.unop
    let π (i : ι) : D i ⟶ W.unop := (componentProjection X i).app W.unop
    have hopen (i : ι) : IsOpenImmersion (π i).left := by
      change IsOpenImmersion (pullback.fst W.unop.hom (Sigma.ι X i))
      infer_instance
    have hmono : ∀ i, Mono (π i) := fun i ↦ by
      exact (MorphismProperty.Over.forget @WeaklyEtale ⊤ (∐ X) ⋙ Over.forget (∐ X)).mono_of_mono_map
        (by change Mono (π i).left; infer_instance)
    have hrange (i : ι) : Set.range (π i).left.base =
        W.unop.hom.base ⁻¹' Set.range (Sigma.ι X i).base :=
      Pullback.range_fst W.unop.hom (Sigma.ι X i)
    have hcov : Sieve.ofArrows D π ∈ topology (∐ X) W.unop := by
      apply mem_topology_iff.mpr
      refine ⟨Presieve.ofArrows D π, ?_, Sieve.le_generate _⟩
      rw [mem_precoverage_iff, Presieve.map_ofArrows]
      apply zariskiPrecoverage_le_proetalePrecoverage
      apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
      refine ⟨?_, hopen⟩
      intro x
      have hx : W.unop.hom x ∈ (⊤ : (∐ X).Opens) := trivial
      rw [← (sigmaOpenCover X).iSup_opensRange] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      refine ⟨i, ?_⟩
      change x ∈ Set.range (π i).left
      rw [hrange]
      exact hi
    have hdisj (i j : ι) (hij : i ≠ j) :
        Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base) := by
      rw [hrange, hrange]
      exact (TopologicalSpace.Opens.coe_disjoint.mpr
        (disjoint_opensRange_sigmaι X i j hij)).preimage _
    have h : (Pi.lift (componentRestriction X F)).app W ≫
        (piObjIso _ W).hom = Pi.lift (fun i ↦ F.obj.map (π i).op) := by
      apply Pi.hom_ext
      intro i
      rw [Category.assoc, piObjIso_hom_comp_π, ← NatTrans.comp_app, Pi.lift_π]
      change (componentRestriction X F i).app W =
        (Pi.lift (fun i ↦ F.obj.map (π i).op)) ≫
          Pi.π (fun i ↦ F.obj.obj (op (D i))) i
      rw [Pi.lift_π]
      rfl
    rw [← Iso.eq_comp_inv] at h
    rw [h]
    have := isIso_piLift_of_disjoint F D π hcov hdisj
    infer_instance
  exact NatIso.isIso_of_isIso_app _

-- Whisker local isomorphisms with base change and conjugate their product by restriction.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem coproduct_sheaf_iso {ι : Type 0} (X : ι → Scheme.{u})
    (F G : Sheaf (topology (∐ X)) (Type (u + 1)))
    (e : ∀ i, (componentFunctor X i).op ⋙ F.obj ≅
      (componentFunctor X i).op ⋙ G.obj) : Nonempty (F.obj ≅ G.obj) := by
  let := componentRestriction_isIso X F
  let := componentRestriction_isIso X G
  exact ⟨asIso (Pi.lift (componentRestriction X F)) ≪≫
    Pi.mapIso (fun i ↦ Functor.isoWhiskerLeft
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (Sigma.ι X i)).op (e i)) ≪≫
    (asIso (Pi.lift (componentRestriction X G))).symm⟩


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem restriction_trivialization
    (X : Scheme.{u}) (F : Sheaf (topology X) (Type (u + 1))) (S : Type u)
    (U V : X.ProEt) (f : V ⟶ U)
    (e : (Scheme.proEtaleSetRestriction X U).obj F ≅
      (constantSheaf (topology U.left) (Type (u + 1))).obj (ULift.{u + 1} S)) :
    Nonempty ((Scheme.proEtaleSetRestriction X V).obj F ≅
      (constantSheaf (topology V.left) (Type (u + 1))).obj (ULift.{u + 1} S)) := by
  have hg : WeaklyEtale f.left := by
    have hcomp : WeaklyEtale (f.left ≫ U.hom) :=
      (MorphismProperty.Over.w f).symm ▸ V.prop
    exact WeaklyEtale.of_comp f.left U.hom
  let R := Scheme.proEtaleSetRestriction U.left (ProEt.mk f.left)
  let G := MorphismProperty.Over.map (f := f.left) ⊤ hg
  let c := (G.pushforwardContinuousSheafificationCompatibility (Type (u + 1))
    (topology V.left) (topology U.left)).app
      ((Functor.const U.left.ProEtᵒᵖ).obj (ULift.{u + 1} S))
  have a : (Scheme.proEtaleSetRestriction X V).obj F ≅
      R.obj ((Scheme.proEtaleSetRestriction X U).obj F) := by
    apply (sheafToPresheaf _ _).preimageIso
    refine NatIso.ofComponents (fun W ↦ F.obj.mapIso (Iso.op ?_)) ?_
    · refine MorphismProperty.Over.isoMk (Iso.refl _) ?_
      change 𝟙 _ ≫ (W.unop.hom ≫ V.hom) = (W.unop.hom ≫ f.left) ≫ U.hom
      simp only [Category.id_comp, Category.assoc, MorphismProperty.Over.w f]
    · intro W W' g
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1
  exact ⟨a ≪≫ R.mapIso e ≪≫ c.symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem coproduct_trivialization
    (X : Scheme.{u}) (F : Sheaf (topology X) (Type (u + 1))) (S : Type u)
    {ι : Type 0} (A : ι → X.ProEt)
    (hA : ∀ j, Nonempty ((Scheme.proEtaleSetRestriction X (A j)).obj F ≅
      (constantSheaf (topology (A j).left) (Type (u + 1))).obj (ULift.{u + 1} S)))
    [WeaklyEtale (Sigma.desc (fun j ↦ (A j).hom))] :
    let B := ProEt.mk (Sigma.desc (fun j ↦ (A j).hom))
    Nonempty ((Scheme.proEtaleSetRestriction X B).obj F ≅
      (constantSheaf (topology B.left) (Type (u + 1))).obj (ULift.{u + 1} S)) := by
  let B := ProEt.mk (Sigma.desc (fun j ↦ (A j).hom))
  let F' := (Scheme.proEtaleSetRestriction X B).obj F
  let G := (constantSheaf (topology B.left) (Type (u + 1))).obj (ULift.{u + 1} S)
  have he : ∀ j, (componentFunctor (fun j ↦ (A j).left) j).op ⋙ F'.obj ≅
      (componentFunctor (fun j ↦ (A j).left) j).op ⋙ G.obj := by
    intro j
    let g := componentFunctor (fun j ↦ (A j).left) j
    have a : g.op ⋙ F'.obj ≅ ((Scheme.proEtaleSetRestriction X (A j)).obj F).obj := by
      refine NatIso.ofComponents (fun W ↦ F.obj.mapIso (Iso.op ?_)) ?_
      · refine MorphismProperty.Over.isoMk (Iso.refl _) ?_
        change 𝟙 _ ≫ ((W.unop.hom ≫ Sigma.ι (fun j ↦ (A j).left) j) ≫ B.hom) =
          W.unop.hom ≫ (A j).hom
        simp [B, Category.assoc]
      · intro W W' f
        change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        congr 1
    have : g.IsContinuous (topology (A j).left) (topology B.left) :=
      isContinuous_overMap (inferInstance : WeaklyEtale
        (Sigma.ι (fun j ↦ (A j).left) j))
    have : g.IsCocontinuous (topology (A j).left) (topology B.left) :=
      isCocontinuous_overMap (inferInstance : WeaklyEtale
        (Sigma.ι (fun j ↦ (A j).left) j))
    let c := (g.pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (topology (A j).left) (topology B.left)).app
        ((Functor.const B.left.ProEtᵒᵖ).obj (ULift.{u + 1} S))
    exact a ≪≫ (sheafToPresheaf _ _).mapIso (hA j).some ≪≫
      (sheafToPresheaf _ _).mapIso c
  obtain ⟨e⟩ := coproduct_sheaf_iso (fun j ↦ (A j).left) F' G he
  exact ⟨(sheafToPresheaf _ _).preimageIso e⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem finite_affine_coproduct_cover
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (S : Type u) (F : Sheaf (topology X) (Type (u + 1)))
    (I : Type i) (U : I → X.ProEt)
    (hcover : Presieve.ofArrows (fun k ↦ (U k).left) (fun k ↦ (U k).hom) ∈
      proetalePrecoverage X)
    (trivializations : ∀ k, (Scheme.proEtaleSetRestriction X (U k)).obj F ≅
      (constantSheaf (topology (U k).left) (Type (u + 1))).obj (ULift.{u + 1} S)) :
    ∃ (n : ℕ) (A : Fin n → X.ProEt) (α : Fin n → I)
      (_refinement : ∀ j, A j ⟶ U (α j)) (V : X.ProEt)
      (ι : ∀ j, (A j).left ⟶ V.left),
      (∀ j, IsAffine (A j).left) ∧
      (∀ j, ι j ≫ V.hom = (A j).hom) ∧
      Nonempty (IsColimit (Cofan.mk V.left ι)) ∧
      IsAffine V.left ∧ Flat V.hom ∧ Surjective V.hom ∧ QuasiCompact V.hom ∧
      Presieve.singleton V.hom ∈ fpqcPrecoverage X ∧
      Presieve.singleton V.hom ∈ proetalePrecoverage X ∧
      Nonempty ((Scheme.proEtaleSetRestriction X V).obj F ≅
        (constantSheaf (topology V.left) (Type (u + 1))).obj (ULift.{u + 1} S)) := by
  classical
  have hfinite : ∃ (n : ℕ) (α : Fin n → I) (O : ∀ j, (U (α j)).left.Opens),
      (∀ j, IsAffineOpen (O j)) ∧
      Presieve.ofArrows (fun j ↦ (O j).toScheme)
        (fun j ↦ (O j).ι ≫ (U (α j)).hom) ∈ proetalePrecoverage X := by
    cases isEmpty_or_nonempty X with
    | inl hX =>
      let α : Fin 0 → I := Fin.elim0
      let O : ∀ j, (U (α j)).left.Opens := fun j ↦ j.elim0
      refine ⟨0, α, O, fun j ↦ j.elim0, ?_⟩
      have hbot := bot_mem_propQCPrecoverage (P := @WeaklyEtale) X
      change _ ∈ propQCPrecoverage @WeaklyEtale X
      have he : Presieve.ofArrows (fun j ↦ (O j).toScheme)
          (fun j ↦ (O j).ι ≫ (U (α j)).hom) = ⊥ := by
        apply le_antisymm
        · rintro W f ⟨j⟩
          exact j.elim0
        · exact bot_le
      rw [he]
      exact hbot
    | inr hX =>
      obtain ⟨n, _, α, O, ha, hc⟩ :=
        Scheme.finite_affine_proetale_refinement X I U hcover
      exact ⟨n, α, O, ha, hc⟩
  obtain ⟨n, α, O, ha, hc⟩ := hfinite
  let A (j : Fin n) : X.ProEt := ProEt.mk ((O j).ι ≫ (U (α j)).hom)
  have (j : Fin n) : IsAffine (A j).left := ha j
  let p : (∐ fun j ↦ (A j).left) ⟶ X := Sigma.desc (fun j ↦ (A j).hom)
  have hp : WeaklyEtale p := IsZariskiLocalAtSource.sigmaDesc
    (P := @WeaklyEtale) (fun j ↦ (A j).prop)
  let V : X.ProEt := ProEt.mk p
  have hsurj : Surjective p := by
    let E : X.Cover (Scheme.precoverage @WeaklyEtale) :=
      { I₀ := Fin n, X j := (A j).left, f j := (A j).hom, mem₀ := hc.2 }
    constructor
    intro x
    obtain ⟨j, y, rfl⟩ := E.exists_eq x
    refine ⟨Sigma.ι (fun j ↦ (A j).left) j y, ?_⟩
    exact congrArg (fun f ↦ f y) (Sigma.ι_desc (fun j ↦ (A j).hom) j)
  have hVaff : IsAffine V.left := by
    change IsAffine (∐ fun j ↦ (A j).left)
    infer_instance
  have hqc : QuasiCompact p := quasiCompact_of_compactSpace p
  have hpro : Presieve.singleton p ∈ proetalePrecoverage X :=
    p.singleton_mem_propQCPrecoverage hp
  refine ⟨n, A, α, fun j ↦ MorphismProperty.Over.homMk (O j).ι rfl,
    V, fun j ↦ Sigma.ι (fun j ↦ (A j).left) j, fun j ↦ inferInstance,
    fun j ↦ Sigma.ι_desc _ j, ?_, inferInstance, inferInstance, hsurj, hqc,
    proetalePrecoverage_le_fpqcPrecoverage X hpro, hpro, ?_⟩
  · exact ⟨coproductIsCoproduct (fun j ↦ (A j).left)⟩
  · have : WeaklyEtale (Sigma.desc (fun j ↦ (A j).hom)) := hp
    apply coproduct_trivialization X F S A
    intro j
    exact restriction_trivialization X F S (U (α j)) (A j)
      (MorphismProperty.Over.homMk (O j).ι rfl) (trivializations (α j))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem constant_copies_comparison (U : Scheme.{u}) (E : Type u) :
    ∃ e : ((constantSheaf (topology U) (Type (u + 1))).obj
        (ULift.{u + 1} E)).obj ≅ localSystemCopiesHom U E,
      Presheaf.IsSheaf (topology U) (localSystemCopiesHom U E) ∧
      ∀ (W : U.ProEt) (s : E),
        e.hom.app (op W)
          ((toSheafify (topology U)
            ((Functor.const U.ProEtᵒᵖ).obj (ULift.{u + 1} E))).app
              (op W) (ULift.up s)) = ULift.up (localSystemLabel E W.hom s) := by
  classical
  let H := localSystemCopiesHom U E
  let P := (Functor.const U.ProEtᵒᵖ).obj (ULift.{u + 1, u} E)
  let c : P ⟶ H :=
    { app := fun W => ↾fun e => ⟨Over.homMk
        (W.unop.hom ≫ Sigma.ι (fun _ : E => U) e.down) (by simp [localSystemCopies, ProEt.forget])⟩
      naturality := by
        intro W V g
        ext e
        apply ULift.ext
        apply Over.OverMorphism.ext
        change V.unop.hom ≫ Sigma.ι (fun _ : E => U) e.down =
          g.unop.left ≫ (W.unop.hom ≫ Sigma.ι (fun _ : E => U) e.down)
        simp [← Category.assoc] }
  have hc : ∀ (W : U.ProEt) (e : E), ((c.app (Opposite.op W)) ⟨e⟩).down.left =
      W.hom ≫ Sigma.ι (fun _ : E => U) e := fun _ _ => rfl
  have hH : Presheaf.IsSheaf (topology U) H := by
    rw [isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf (topology U)
      (((ProEt.forget U).op ⋙ yoneda.obj (localSystemCopies U E)) ⋙
        uliftFunctor.{u + 1, u})
    apply Presieve.isSheaf_comp_uliftFunctor
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (ProEt.forget U).op_comp_isSheaf_of_isSheaf
      (topology U) (proetaleTopology.over U) _
      (isSheaf_iff_isSheaf_of_type _ _ |>.mpr
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
          (yoneda.obj (localSystemCopies U E))))
  have hinj : Presheaf.IsLocallyInjective (topology U) c := by
    constructor
    intro W a b hab
    by_cases h : a = b
    · subst b
      exact (topology U).superset_covering (fun _ _ _ => rfl)
        ((topology U).top_mem _)
    · have hne : a.down ≠ b.down := fun h' => h (ULift.ext a b h')
      have heq : W.unop.hom ≫ Sigma.ι (fun _ : E => U) a.down =
          W.unop.hom ≫ Sigma.ι (fun _ : E => U) b.down :=
        congrArg (fun t => t.down.left) hab
      have ha := (coproductCopiesMorphismsClopen U W.unop.left E W.unop.hom).2.2.2.2.1
      have htop : (⊤ : W.unop.left.Opens) = ⊥ := by
        have h₁ := ha a.down a.down
        have h₂ := ha b.down a.down
        rw [heq] at h₁
        simpa [hne] using h₁.symm.trans h₂
      have : IsEmpty W.unop.left := ⟨fun x => by
        have hx : x ∈ (⊤ : W.unop.left.Opens) := trivial
        rw [htop] at hx
        exact hx⟩
      exact (topology U).superset_covering bot_le (bot_mem_topology W.unop)
  have hsurj : Presheaf.IsLocallySurjective (topology U) c := by
    constructor
    intro W s
    let f : W.left ⟶ ∐ fun _ : E => U := s.down.left
    have hf : f ≫ Sigma.desc (fun _ : E => 𝟙 U) = W.hom := s.down.w
    let V (e : E) := f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange
    have hdecomp := (coproductCopiesMorphismsClopen U W.left E W.hom).1 f hf
    let Z (e : E) : U.ProEt := ProEt.mk ((V e).ι ≫ W.hom)
    let j (e : E) : Z e ⟶ W := MorphismProperty.Over.homMk (V e).ι rfl
    apply mem_topology_of_openImmersion _ (fun e ↦ (V e).ι)
    · intro x
      have hx : x ∈ (⨆ e, V e) := by rw [hdecomp.1.2]; trivial
      obtain ⟨e, he⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨e, ⟨⟨x, he⟩, rfl⟩⟩
    · intro e
      refine ⟨⟨e⟩, ?_⟩
      apply ULift.ext
      apply Over.OverMorphism.ext
      exact (hdecomp.2 e).symm
  let φ : (constantSheaf (topology U) (Type (u + 1))).obj
      (ULift.{u + 1, u} E) ⟶ ⟨H, hH⟩ :=
    ⟨sheafifyLift (topology U) c hH⟩
  have hφ : toSheafify (topology U) P ≫ φ.hom = c :=
    toSheafify_sheafifyLift (topology U) c hH
  have hIso : IsIso φ := by
    apply (Sheaf.isLocallyBijective_iff_isIso φ).mp
    constructor
    · change Presheaf.IsLocallyInjective _ _
      rw [← Presheaf.comp_isLocallyInjective_iff _
        (toSheafify (topology U) P), hφ]
      exact hinj
    · change Presheaf.IsLocallySurjective _ _
      rw [← Presheaf.comp_isLocallySurjective_iff _
        (toSheafify (topology U) P), hφ]
      exact hsurj
  let e := (sheafToPresheaf _ _).mapIso (asIso φ)
  refine ⟨e, hH, ?_⟩
  intro W s
  have hh := NatTrans.congr_app hφ (op W)
  exact congrArg (fun f : P.obj (op W) ⟶ H.obj (op W) ↦ f (ULift.up s)) hh

-- The following transport construction adapts the proved source-library
-- FiniteLocalModelsDescentDatumCompatibilityDatum, TransportDiagonal and
-- TransportCocycle arguments. Only weak etaleness is needed: all universal
-- test schemes remain objects of the small pro-etale site. No finiteness or
-- surjectivity is used (Stacks 03RV and 02W5).
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private structure CompatibleTransport
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q) where
  transport {W : Scheme.{u}} (a b : W ⟶ U.left) (h : a ≫ U.hom = b ≫ U.hom) :
    (Over.mk a ⟶ Over.mk Q.hom) → (Over.mk b ⟶ Over.mk Q.hom)
  naturality {W W' : Scheme.{u}} (g : W' ⟶ W) (a b : W ⟶ U.left)
    (h : a ≫ U.hom = b ≫ U.hom) (x : Over.mk a ⟶ Over.mk Q.hom) :
    transport (g ≫ a) (g ≫ b) (by rw [Category.assoc, Category.assoc, h])
      ((Over.homMk g : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x) =
      (Over.homMk g : Over.mk (g ≫ b) ⟶ Over.mk b) ≫ transport a b h x
  compatibility :
      ∀ (W : T.ProEt) (a b : W ⟶ U) (s : E.obj.obj (op W)),
        (transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
          (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
            (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
          ((e.hom.app (op (Over.mk b))) s).down.left

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localModel_section_naturality
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q)
    (V W : T.ProEt) (a : V ⟶ U) (b : W ⟶ U) (g : W ⟶ V)
    (hg : g ≫ a = b) (s : E.obj.obj (op V)) :
    g.left ≫ ((e.hom.app (op (Over.mk a))) s).down.left =
      ((e.hom.app (op (Over.mk b))) (E.obj.map g.op s)).down.left := by
  let k : Over.mk b ⟶ Over.mk a := Over.homMk g hg
  have hn := ConcreteCategory.congr_hom (e.hom.naturality k.op) s
  exact congrArg (fun z ↦ z.down.left) hn.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def localModel_comparison
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q) :
    Over.mk (CategoryTheory.Limits.pullback.snd (Q.hom ≫ U.hom) U.hom) ⟶
      Over.mk Q.hom := by
  let R := CategoryTheory.Limits.pullback (Q.hom ≫ U.hom) U.hom
  let p : R ⟶ Q.left := CategoryTheory.Limits.pullback.fst _ _
  let b : R ⟶ U.left := CategoryTheory.Limits.pullback.snd _ _
  let V : T.ProEt := ProEt.mk (b ≫ U.hom)
  let a' : V ⟶ U := MorphismProperty.Over.homMk (p ≫ Q.hom)
    (by
      change (p ≫ Q.hom) ≫ U.hom = b ≫ U.hom
      simpa [p, b, Category.assoc] using
        (CategoryTheory.Limits.pullback.condition (f := Q.hom ≫ U.hom)
          (g := U.hom)))
  let b' : V ⟶ U := MorphismProperty.Over.homMk b rfl
  let z : ((sliceTo T U).op ⋙ uliftYoneda.{u + 1}.obj Q).obj
      (op (Over.mk a')) := ULift.up (MorphismProperty.Over.homMk p rfl)
  let s := e.inv.app (op (Over.mk a')) z
  exact Over.homMk ((e.hom.app (op (Over.mk b'))) s).down.left
    (MorphismProperty.Over.w ((e.hom.app (op (Over.mk b'))) s).down)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def localModel_transport
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q)
    {W : Scheme.{u}} (a b : W ⟶ U.left) (h : a ≫ U.hom = b ≫ U.hom)
    (x : Over.mk a ⟶ Over.mk Q.hom) : Over.mk b ⟶ Over.mk Q.hom := by
  let l : W ⟶ CategoryTheory.Limits.pullback (Q.hom ≫ U.hom) U.hom :=
    CategoryTheory.Limits.pullback.lift x.left b
    (by
      have hx : x.left ≫ Q.hom = a := Over.w x
      rw [← Category.assoc, hx, h])
  refine Over.homMk (l ≫ (localModel_comparison T E U Q e).left) ?_
  rw [Category.assoc, Over.w]
  change l ≫ CategoryTheory.Limits.pullback.snd _ _ = b
  exact CategoryTheory.Limits.pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localModel_transport_naturality
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q) :
    ∀ {W W' : Scheme.{u}} (g : W' ⟶ W) (a b : W ⟶ U.left)
      (h : a ≫ U.hom = b ≫ U.hom) (x : Over.mk a ⟶ Over.mk Q.hom),
      localModel_transport T E U Q e (g ≫ a) (g ≫ b)
        (by rw [Category.assoc, Category.assoc, h])
        ((Over.homMk g : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x) =
      (Over.homMk g : Over.mk (g ≫ b) ⟶ Over.mk b) ≫
        localModel_transport T E U Q e a b h x := by
  intro W W' g a b h x
  apply Over.OverMorphism.ext
  simp only [localModel_transport, Over.homMk_left, Over.comp_left]
  simp only [← Category.assoc]
  congr 1
  apply CategoryTheory.Limits.pullback.hom_ext <;>
    simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localModel_transport_compatibility
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q) :
    ∀ (W : T.ProEt) (a b : W ⟶ U) (s : E.obj.obj (op W)),
      (localModel_transport T E U Q e a.left b.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
        (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
          (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
      ((e.hom.app (op (Over.mk b))) s).down.left := by
  intro W a b s
  let R := CategoryTheory.Limits.pullback (Q.hom ≫ U.hom) U.hom
  let p : R ⟶ Q.left := CategoryTheory.Limits.pullback.fst _ _
  let q : R ⟶ U.left := CategoryTheory.Limits.pullback.snd _ _
  let V : T.ProEt := ProEt.mk (q ≫ U.hom)
  let a' : V ⟶ U := MorphismProperty.Over.homMk (p ≫ Q.hom) (by
    change (p ≫ Q.hom) ≫ U.hom = q ≫ U.hom
    simpa [p, q, Category.assoc] using
      (CategoryTheory.Limits.pullback.condition (f := Q.hom ≫ U.hom)
        (g := U.hom)))
  let b' : V ⟶ U := MorphismProperty.Over.homMk q rfl
  let z : ((sliceTo T U).op ⋙ uliftYoneda.{u + 1}.obj Q).obj
      (op (Over.mk a')) := ULift.up (MorphismProperty.Over.homMk p rfl)
  let sV := e.inv.app (op (Over.mk a')) z
  let x := ((e.hom.app (op (Over.mk a))) s).down
  have hx : x.left ≫ Q.hom = a.left := MorphismProperty.Over.w x
  let l : W.left ⟶ R := CategoryTheory.Limits.pullback.lift x.left b.left (by
    rw [← Category.assoc, hx]
    exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
  let g : W ⟶ V := MorphismProperty.Over.homMk l (by
    change l ≫ q ≫ U.hom = W.hom
    rw [← Category.assoc]
    simp only [l, q, CategoryTheory.Limits.pullback.lift_snd]
    exact MorphismProperty.Over.w b)
  have hga : g ≫ a' = a := by
    apply MorphismProperty.Over.Hom.ext
    change l ≫ (p ≫ Q.hom) = a.left
    rw [← Category.assoc]
    simpa [l, p] using hx
  have hgb : g ≫ b' = b := by
    apply MorphismProperty.Over.Hom.ext
    exact CategoryTheory.Limits.pullback.lift_snd _ _ _
  have hsV : e.hom.app (op (Over.mk a')) sV = z :=
    ConcreteCategory.congr_hom (e.inv_hom_id_app (op (Over.mk a'))) z
  have hs : E.obj.map g.op sV = s := by
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app (op (Over.mk a)))).1
    apply ULift.ext
    apply MorphismProperty.Over.Hom.ext
    have hn := localModel_section_naturality T E U Q e V W a' a g hga sV
    rw [hsV] at hn
    simpa [g, z, l, p, x] using hn.symm
  have hn := localModel_section_naturality T E U Q e V W b' b g hgb sV
  rw [hs] at hn
  change l ≫ ((e.hom.app (op (Over.mk b'))) sV).down.left =
    ((e.hom.app (op (Over.mk b))) s).down.left at hn
  exact hn


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localModel_descentDatum_compatibility_transport_diagonal
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q)
    (t : CompatibleTransport T E U Q e) :
    ∀ (W : Scheme.{u}) (a : W ⟶ U.left)
      (x : Over.mk a ⟶ Over.mk Q.hom),
      t.transport a a rfl x = x := by
  intro W a x
  obtain ⟨g, hg, rfl⟩ := Over.homMk_surjective x
  change W ⟶ Q.left at g
  change g ≫ Q.hom = a at hg
  subst a
  let V : T.ProEt := ProEt.mk (Q.hom ≫ U.hom)
  let q : V ⟶ U := MorphismProperty.Over.homMk Q.hom rfl
  let z : ((sliceTo T U).op ⋙ uliftYoneda.{u + 1}.obj Q).obj
      (op (Over.mk q)) := ULift.up (𝟙 Q)
  let s := e.inv.app (op (Over.mk q)) z
  have hs : e.hom.app (op (Over.mk q)) s = z := by
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app (op (Over.mk q))) z
  have h := t.compatibility V q q s
  simp only [hs] at h
  have hn := t.naturality g Q.hom Q.hom rfl
    (𝟙 (Over.mk Q.hom))
  apply Over.OverMorphism.ext
  simp only [Category.comp_id] at hn
  have hh : t.transport Q.hom Q.hom rfl
      (𝟙 (Over.mk Q.hom)) = 𝟙 (Over.mk Q.hom) := by
    apply Over.OverMorphism.ext
    exact h
  rw [hh] at hn
  simpa using congrArg Over.Hom.left hn
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem transport_cocycle_onSite
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q)
    (t : CompatibleTransport T E U Q e)
    (V : T.ProEt) (a b c : V ⟶ U)
    (x : Over.mk a.left ⟶ Over.mk Q.hom) :
    t.transport b.left c.left
        ((MorphismProperty.Over.w b).trans (MorphismProperty.Over.w c).symm)
        (t.transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) x) =
      t.transport a.left c.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w c).symm) x := by
  let z : ((sliceTo T U).op ⋙ uliftYoneda.{u + 1}.obj Q).obj
      (op (Over.mk a)) := ULift.up (MorphismProperty.Over.homMk x.left (Over.w x))
  let s := e.inv.app (op (Over.mk a)) z
  have hs : e.hom.app (op (Over.mk a)) s = z :=
    ConcreteCategory.congr_hom (e.inv_hom_id_app (op (Over.mk a))) z
  let p (d : V ⟶ U) : Over.mk d.left ⟶ Over.mk Q.hom :=
    Over.homMk ((e.hom.app (op (Over.mk d))) s).down.left
      (MorphismProperty.Over.w ((e.hom.app (op (Over.mk d))) s).down)
  have hpa : p a = x := by
    apply Over.OverMorphism.ext
    change ((e.hom.app (op (Over.mk a))) s).down.left = x.left
    rw [hs]
    rfl
  have hp (d f : V ⟶ U) :
      t.transport d.left f.left
        ((MorphismProperty.Over.w d).trans (MorphismProperty.Over.w f).symm) (p d) =
      p f := by
    apply Over.OverMorphism.ext
    exact t.compatibility V d f s
  rw [← hpa, hp a b, hp b c, hp a c]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem transport_cocycle_of_lift
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q)
    (t : CompatibleTransport T E U Q e)
    (R W : Scheme.{u}) (g : W ⟶ R) (aa bb cc : R ⟶ U.left)
    (hab' : aa ≫ U.hom = bb ≫ U.hom) (hbc' : bb ≫ U.hom = cc ≫ U.hom)
    (z : Over.mk aa ⟶ Over.mk Q.hom)
    (hz : t.transport bb cc hbc' (t.transport aa bb hab' z) =
      t.transport aa cc (hab'.trans hbc') z)
    (a b c : W ⟶ U.left) (hab : a ≫ U.hom = b ≫ U.hom)
    (hbc : b ≫ U.hom = c ≫ U.hom) (x : Over.mk a ⟶ Over.mk Q.hom)
    (ga : g ≫ aa = a) (gb : g ≫ bb = b) (gc : g ≫ cc = c)
    (gx : g ≫ z.left = x.left) :
    t.transport b c hbc (t.transport a b hab x) =
      t.transport a c (hab.trans hbc) x := by
  subst a b c
  have hx : (Over.homMk g : Over.mk (g ≫ aa) ⟶ Over.mk aa) ≫ z = x :=
    Over.OverMorphism.ext gx
  have hnab := t.naturality g aa bb hab' z
  have hnbc := t.naturality g bb cc hbc' (t.transport aa bb hab' z)
  have hnac := t.naturality g aa cc (hab'.trans hbc') z
  rw [hx] at hnab hnac
  rw [hnab, hnbc, hz]
  exact hnac.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localModel_descentDatum_compatibility_transport_cocycle
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙
      uliftYoneda.{u + 1}.obj Q)
    (t : CompatibleTransport T E U Q e) :
    ∀ (W : Scheme.{u}) (a b c : W ⟶ U.left)
      (hab : a ≫ U.hom = b ≫ U.hom)
      (hbc : b ≫ U.hom = c ≫ U.hom)
      (x : Over.mk a ⟶ Over.mk Q.hom),
      t.transport b c hbc (t.transport a b hab x) =
        t.transport a c (hab.trans hbc) x := by
  intro W a b c hab hbc x
  have hw : x.left ≫ Q.hom = a := Over.w x
  let f : Q.left ⟶ T := Q.hom ≫ U.hom
  let B := Limits.pullback f U.hom
  let v : B ⟶ T := Limits.pullback.snd f U.hom ≫ U.hom
  let R := Limits.pullback v U.hom
  let q : R ⟶ Q.left := Limits.pullback.fst v U.hom ≫ Limits.pullback.fst f U.hom
  let aa : R ⟶ U.left := q ≫ Q.hom
  let bb : R ⟶ U.left := Limits.pullback.fst v U.hom ≫ Limits.pullback.snd f U.hom
  let cc : R ⟶ U.left := Limits.pullback.snd v U.hom
  have hab' : aa ≫ U.hom = bb ≫ U.hom := by
    dsimp [aa, bb, q]
    simp only [Category.assoc]
    exact congrArg (Limits.pullback.fst v U.hom ≫ ·)
      (Limits.pullback.condition (f := f) (g := U.hom))
  have hbc' : bb ≫ U.hom = cc ≫ U.hom := by
    exact (Category.assoc _ _ _).trans (Limits.pullback.condition (f := v) (g := U.hom))
  let V : T.ProEt := ProEt.mk (cc ≫ U.hom)
  let a' : V ⟶ U := MorphismProperty.Over.homMk aa (hab'.trans hbc')
  let b' : V ⟶ U := MorphismProperty.Over.homMk bb hbc'
  let c' : V ⟶ U := MorphismProperty.Over.homMk cc rfl
  let z : Over.mk aa ⟶ Over.mk Q.hom := Over.homMk q rfl
  have hz : t.transport bb cc hbc' (t.transport aa bb hab' z) =
      t.transport aa cc (hab'.trans hbc') z :=
    transport_cocycle_onSite T E U Q e t V a' b' c' z
  let g₀ : W ⟶ B := Limits.pullback.lift x.left b (by
    change x.left ≫ Q.hom ≫ U.hom = b ≫ U.hom
    rw [← Category.assoc, hw]
    exact hab)
  let g : W ⟶ R := Limits.pullback.lift g₀ c (by
    dsimp [v]
    rw [← Category.assoc, Limits.pullback.lift_snd]
    exact hbc)
  have ga : g ≫ aa = a := by
    dsimp [g, aa, q, g₀]
    simp only [Limits.pullback.lift_fst_assoc, Category.assoc]
    exact hw
  have gb : g ≫ bb = b := by
    dsimp [g, bb, g₀]
    simp only [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd]
  have gc : g ≫ cc = c := by
    exact Limits.pullback.lift_snd _ _ _
  have gx : g ≫ z.left = x.left := by
    change g ≫ q = x.left
    dsimp [g, q, g₀]
    simp only [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst]
  exact transport_cocycle_of_lift T E U Q e t R W g aa bb cc hab' hbc' z hz
    a b c hab hbc x ga gb gc gx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localModel_datum
    (T : Scheme.{u}) (E : Sheaf (topology T) (Type (u + 1)))
    (U : T.ProEt) (Q : U.left.ProEt)
    (e : (E.over U).obj ≅ (sliceTo T U).op ⋙ uliftYoneda.{u + 1}.obj Q) :
    ∃ D : Over.DescentDatum U.hom (Over.mk Q.hom),
      ∀ (W : T.ProEt) (a b : W ⟶ U) (s : E.obj.obj (op W)),
        (D.transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
          (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
            (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
          ((e.hom.app (op (Over.mk b))) s).down.left := by
  let t : CompatibleTransport T E U Q e :=
    { transport := localModel_transport T E U Q e
      naturality := localModel_transport_naturality T E U Q e
      compatibility := localModel_transport_compatibility T E U Q e }
  let D : Over.DescentDatum U.hom (Over.mk Q.hom) :=
    { transport := t.transport
      transport_homMk_comp := t.naturality
      transport_self := fun a x ↦
        localModel_descentDatum_compatibility_transport_diagonal T E U Q e t _ a x
      transport_transport := fun a b c hab hbc x ↦
        localModel_descentDatum_compatibility_transport_cocycle T E U Q e t _
          a b c hab hbc x }
  exact ⟨D, t.compatibility⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def copiesYonedaIso (V : Scheme.{u}) (S : Type u)
    (h : WeaklyEtale (localSystemCopies V S).hom) :
    localSystemCopiesHom V S ≅ uliftYoneda.{u + 1}.obj
      (MorphismProperty.Over.mk ⊤ (localSystemCopies V S).hom h) :=
  NatIso.ofComponents (fun W ↦ Equiv.toIso
    { toFun := fun a ↦ ULift.up (MorphismProperty.Over.homMk a.down.left (Over.w a.down))
      invFun := fun a ↦ ULift.up (Over.homMk a.down.left (MorphismProperty.Over.w a.down))
      left_inv := fun a ↦ ULift.ext _ _ (Over.OverMorphism.ext rfl)
      right_inv := fun a ↦ ULift.ext _ _ (MorphismProperty.Over.Hom.ext rfl) })
    (fun _ ↦ by ext; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def restrictionSliceIso (X : Scheme.{u})
    (F : Sheaf (topology X) (Type (u + 1))) (V : X.ProEt) :
    (F.over V).obj ≅ (sliceTo X V).op ⋙ ((Scheme.proEtaleSetRestriction X V).obj F).obj := by
  refine NatIso.ofComponents (fun W ↦ F.obj.mapIso (Iso.op ?_)) ?_
  · refine MorphismProperty.Over.isoMk (Iso.refl _) ?_
    change 𝟙 _ ≫ W.unop.left.hom = W.unop.hom.left ≫ V.hom
    simp only [Category.id_comp, MorphismProperty.Over.w]
  · intro W W' f
    change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem map_identity_heq (X W : Scheme.{u})
    (F : Sheaf (topology X) (Type (u + 1)))
    (f g : W ⟶ X) [WeaklyEtale f] [WeaklyEtale g] (h : f = g)
    (s : F.obj.obj (op (ProEt.mk g))) :
    HEq (F.obj.map (MorphismProperty.Over.homMk (𝟙 W)
      (by simpa using h.symm) : ProEt.mk f ⟶ ProEt.mk g).op s) s := by
  subst g
  have hi : (MorphismProperty.Over.homMk (𝟙 W) (by simp) :
      ProEt.mk f ⟶ ProEt.mk f) = 𝟙 _ := by rfl
  simp only [hi, op_id, Functor.map_id_apply, heq_eq_eq]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localModel_datum_inverse
    (X : Scheme.{u}) (F : Sheaf (topology X) (Type (u + 1)))
    (V : X.ProEt) (Q : V.left.ProEt)
    (q : ((Scheme.proEtaleSetRestriction X V).obj F).obj ≅ uliftYoneda.{u + 1}.obj Q) :
    ∃ D : Over.DescentDatum V.hom (Over.mk Q.hom),
      ∀ (W : Scheme.{u}) (f₁ f₂ : W ⟶ V.left) [WeaklyEtale f₁] [WeaklyEtale f₂]
        (h : f₁ ≫ V.hom = f₂ ≫ V.hom) (a : Over.mk f₁ ⟶ Over.mk Q.hom),
        HEq (q.inv.app (op (ProEt.mk f₂))
          (ULift.up (MorphismProperty.Over.homMk (D.transport f₁ f₂ h a).left
            (Over.w (D.transport f₁ f₂ h a)))))
          (q.inv.app (op (ProEt.mk f₁))
            (ULift.up (MorphismProperty.Over.homMk a.left (Over.w a)))) := by
  let r : (F.over V).obj ≅ (sliceTo X V).op ⋙ uliftYoneda.{u + 1}.obj Q :=
    restrictionSliceIso X F V ≪≫ Functor.isoWhiskerLeft (sliceTo X V).op q
  obtain ⟨D, hD⟩ := localModel_datum X F V Q r
  refine ⟨D, ?_⟩
  intro W f₁ f₂ hf₁ hf₂ h a
  let W' : X.ProEt := ProEt.mk (f₁ ≫ V.hom)
  let a' : W' ⟶ V := MorphismProperty.Over.homMk f₁ rfl
  let b' : W' ⟶ V := MorphismProperty.Over.homMk f₂ h.symm
  let z : ((sliceTo X V).op ⋙ uliftYoneda.{u + 1}.obj Q).obj
      (op (Over.mk a')) := ULift.up (MorphismProperty.Over.homMk a.left (Over.w a))
  let s := r.inv.app (op (Over.mk a')) z
  have hs : r.hom.app (op (Over.mk a')) s = z := by
    exact ConcreteCategory.congr_hom (r.inv_hom_id_app (op (Over.mk a'))) z
  have ht := hD W' a' b' s
  rw [hs] at ht
  let zD : ULift.{u + 1} ((ProEt.mk f₂) ⟶ Q) :=
    ULift.up (MorphismProperty.Over.homMk (D.transport f₁ f₂ h a).left
      (Over.w (D.transport f₁ f₂ h a)))
  have he : zD = r.hom.app (op (Over.mk b')) s := by
    apply ULift.ext
    apply MorphismProperty.Over.Hom.ext
    exact ht
  change HEq (q.inv.app (op (ProEt.mk f₂)) zD)
    (q.inv.app (op (ProEt.mk f₁)) z)
  have he₂ : q.inv.app (op (ProEt.mk f₂)) zD =
      (restrictionSliceIso X F V).hom.app (op (Over.mk b')) s := by
    rw [he]
    exact ConcreteCategory.congr_hom (q.hom_inv_id_app _) _
  have he₁ : q.inv.app (op (ProEt.mk f₁)) z =
      (restrictionSliceIso X F V).hom.app (op (Over.mk a')) s := by
    rw [← hs]
    exact ConcreteCategory.congr_hom (q.hom_inv_id_app _) _
  rw [he₂, he₁]
  exact (map_identity_heq X W F (f₂ ≫ V.hom) (f₁ ≫ V.hom) h.symm s).trans
    (map_identity_heq X W F (f₁ ≫ V.hom) (f₁ ≫ V.hom) rfl s).symm


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem copies_descentDatum (X : Scheme.{u})
    (F : Sheaf (topology X) (Type (u + 1))) (V : X.ProEt) (S : Type u)
    (ψ : (Scheme.proEtaleSetRestriction X V).obj F ≅
      (constantSheaf (topology V.left) (Type (u + 1))).obj (ULift.{u + 1} S))
    (e : ((constantSheaf (topology V.left) (Type (u + 1))).obj
      (ULift.{u + 1} S)).obj ≅ localSystemCopiesHom V.left S) :
    ∃ D : Over.DescentDatum V.hom (localSystemCopies V.left S),
      ∀ (W : Scheme.{u}) (f₁ f₂ : W ⟶ V.left) [WeaklyEtale f₁] [WeaklyEtale f₂]
          (h : f₁ ≫ V.hom = f₂ ≫ V.hom)
          (a : Over.mk f₁ ⟶ localSystemCopies V.left S),
        HEq (ψ.inv.hom.app (op (ProEt.mk f₂))
            (e.inv.app (op (ProEt.mk f₂)) (ULift.up (D.transport f₁ f₂ h a))))
          (ψ.inv.hom.app (op (ProEt.mk f₁))
            (e.inv.app (op (ProEt.mk f₁)) (ULift.up a))) := by
  have hc : WeaklyEtale (localSystemCopies V.left S).hom :=
    IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) (fun _ ↦ inferInstance)
  let Q : V.left.ProEt := MorphismProperty.Over.mk ⊤ (localSystemCopies V.left S).hom hc
  let q : ((Scheme.proEtaleSetRestriction X V).obj F).obj ≅
      uliftYoneda.{u + 1}.obj Q :=
    (sheafToPresheaf _ _).mapIso ψ ≪≫ e ≪≫ copiesYonedaIso V.left S hc
  obtain ⟨D, hD⟩ := localModel_datum_inverse X F V Q q
  refine ⟨D, ?_⟩
  intro W f₁ f₂ hf₁ hf₂ h a
  exact hD W f₁ f₂ h a


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def transitionMap {X V B : Scheme.{u}} {p : V ⟶ X}
    {T : Over V} (D : Over.DescentDatum p T) (r₁ r₂ : B ⟶ V)
    (h : r₁ ≫ p = r₂ ≫ p) :
    (Over.pullback r₁).obj T ⟶ (Over.pullback r₂).obj T := by
  let q := pullback.snd T.hom r₁
  let a : Over.mk (q ≫ r₁) ⟶ T :=
    Over.homMk (pullback.fst T.hom r₁) pullback.condition
  let b := D.transport (q ≫ r₁) (q ≫ r₂) (by simp only [Category.assoc, h]) a
  exact (Over.mapPullbackAdj r₂).homEquiv ((Over.pullback r₁).obj T) T b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localSystemPullbackPoint_left {B V W : Scheme.{u}} (T : Over V)
    (f : B ⟶ V) (w : W ⟶ B) (a : Over.mk w ⟶ (Over.pullback f).obj T) :
    (localSystemPullbackPoint T f w a).left = a.left ≫ pullback.fst T.hom f := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem transitionMap_realizes {X V B : Scheme.{u}} {p : V ⟶ X}
    {T : Over V} (D : Over.DescentDatum p T) (r₁ r₂ : B ⟶ V)
    (h : r₁ ≫ p = r₂ ≫ p) (W : Scheme.{u}) (w : W ⟶ B)
    (a : Over.mk w ⟶ (Over.pullback r₁).obj T) :
    localSystemPullbackPoint T r₂ w (a ≫ transitionMap D r₁ r₂ h) =
      D.transport (w ≫ r₁) (w ≫ r₂) (by simp only [Category.assoc, h])
        (localSystemPullbackPoint T r₁ w a) := by
  let q := pullback.snd T.hom r₁
  let z : Over.mk (q ≫ r₁) ⟶ T :=
    Over.homMk (pullback.fst T.hom r₁) pullback.condition
  have hn := D.transport_homMk_comp a.left (q ≫ r₁) (q ≫ r₂)
    (by simp only [Category.assoc, h]) z
  have ha : a.left ≫ q = w := Over.w a
  have ha₁ : a.left ≫ (q ≫ r₁) = w ≫ r₁ := by rw [← Category.assoc, ha]
  have ha₂ : a.left ≫ (q ≫ r₂) = w ≫ r₂ := by rw [← Category.assoc, ha]
  apply Over.OverMorphism.ext
  have hn' := congrArg Over.Hom.left hn
  rw [D.transport_left_congr (by simp only [Category.assoc, h])
    (by simp only [Category.assoc, h])
    (localSystemPullbackPoint T r₁ w a)
    ((Over.homMk a.left : Over.mk (a.left ≫ (q ≫ r₁)) ⟶ Over.mk (q ≫ r₁)) ≫ z)
    ha₁.symm ha₂.symm (by rfl)]
  rw [hn']
  simp [localSystemPullbackPoint, transitionMap, Over.mapPullbackAdj,
    Category.assoc, z, q]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem transitionMap_inverse {X V B : Scheme.{u}} {p : V ⟶ X}
    {T : Over V} (D : Over.DescentDatum p T) (r₁ r₂ : B ⟶ V)
    (h : r₁ ≫ p = r₂ ≫ p) :
    transitionMap D r₁ r₂ h ≫ transitionMap D r₂ r₁ h.symm = 𝟙 _ := by
  apply ((Over.mapPullbackAdj r₁).homEquiv ((Over.pullback r₁).obj T) T).symm.injective
  change localSystemPullbackPoint T r₁ _
    ((𝟙 _ ≫ transitionMap D r₁ r₂ h) ≫ transitionMap D r₂ r₁ h.symm) =
    localSystemPullbackPoint T r₁ _ (𝟙 _)
  rw [transitionMap_realizes, transitionMap_realizes, D.transport_transport,
    D.transport_self]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem transition_iso {X V B : Scheme.{u}} {p : V ⟶ X}
    {T : Over V} (D : Over.DescentDatum p T) (r₁ r₂ : B ⟶ V)
    (h : r₁ ≫ p = r₂ ≫ p) :
    ∃! δ : (Over.pullback r₁).obj T ≅ (Over.pullback r₂).obj T,
      LocalSystemTransitionRealizes D r₁ r₂ h δ ∧
      LocalSystemTransitionRealizes D r₂ r₁ h.symm δ.symm := by
  let δ : (Over.pullback r₁).obj T ≅ (Over.pullback r₂).obj T :=
    { hom := transitionMap D r₁ r₂ h
      inv := transitionMap D r₂ r₁ h.symm
      hom_inv_id := transitionMap_inverse D r₁ r₂ h
      inv_hom_id := transitionMap_inverse D r₂ r₁ h.symm }
  refine ⟨δ, ⟨transitionMap_realizes D r₁ r₂ h,
    transitionMap_realizes D r₂ r₁ h.symm⟩, ?_⟩
  intro ε hε
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hh := hε.1 ((Over.pullback r₁).obj T).left
      ((Over.pullback r₁).obj T).hom (𝟙 _)
    have hd := transitionMap_realizes D r₁ r₂ h
      ((Over.pullback r₁).obj T).left ((Over.pullback r₁).obj T).hom (𝟙 _)
    have hh' := congrArg Over.Hom.left (hh.trans hd.symm)
    simpa only [localSystemPullbackPoint_left, Over.comp_left, Over.id_left,
      Category.id_comp] using hh'
  · exact (Over.w ε.hom).trans (Over.w δ.hom).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Finite affine coproduct descent presentation, including arbitrary and empty label sets.

Source: blueprint, sec-six-functors-basics, stratified lattice scheme proof (2);
Stacks, Tags 0989, 098A, 098C, 098Z, 023Q, 03YW, 00WM, 00WK, 001P and 023V
(blueprint: lem-sfb-local-system-affine-descent-presentation).

Proof plan:
1. For nonempty X apply `lem-sfb-finite-affine-cover-refinement-general`; for empty X
   take the empty family. Keep the maps to the original trivializing charts.
2. Form the finite coproduct (`lem-weil-pbc-scheme-coproduct-family`), which is affine
   by `lem-weil-pbc-finite-affine-coproduct-spectrum`. Source locality of weakly etale
   maps makes its codiagonal weakly etale, hence flat. Joint surjectivity and qcqs
   permanence give surjectivity and quasi-compactness. The finite-affine-open criterion
   gives both fpqc and pro-etale singleton covers, including the empty-base case.
3. For any base B the coproduct of S copies has sections precisely the clopen
   decompositions, by `lem-galois-coproduct-copies-morphisms-clopen`. Component sections
   give the constant labels, naturally under all pullbacks and changes of base.
4. Its relative representable is a sheaf by fpqc descent of scheme morphisms
   (`lem-weil-pbc-fpqc-representable-descent`), also for empty coverings.
5. The constant-presheaf map is locally surjective on the clopen pieces and locally
   injective by disjointness; use the empty cover for the empty test scheme. Apply
   `lem-cbc-set-presheaf-sheafification-local-bijection` to obtain the comparison iso.
6. Weakly etale localization identifies restrictions on the same underlying schemes;
   `lem-weil-pbc-site-sheafification-sections-local` gives uniqueness of the
   constant-sheaf comparisons and compatibility with successive restrictions.
7. Glue the supplied trivializations on the disjoint affine summands. Empty overlaps
   have singleton sections, so gluing and its inverse are natural and inverse.
8. Over R the two representations of the same restriction of F give a unique scheme
   isomorphism by `lem-galois-yoneda-fully-faithful`. The inverse transition represents
   its inverse. This gives the transport datum and the displayed realization identity.
9. Evaluate transport at each source component section. Its target-component preimages
   partition R into clopen pieces, and the map on each is the identity over R. The
   coproduct mapping property assembles these component maps, in both directions.
10. On the triple overlap the transitions are psi_b psi_a^-1, so cancellation gives
    delta_23 delta_12 = delta_13, exactly `Over.DescentDatum.transport_transport`.
    Empty X and empty S obey the same argument and the empty-cover sheaf condition. -/
theorem localSystem_affine_descent_presentation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (S : Type u)
    (F : Sheaf (topology X) (Type (u + 1))) (I : Type i) (U : I → X.ProEt)
    (hcover : Presieve.ofArrows (fun k ↦ (U k).left) (fun k ↦ (U k).hom) ∈
      proetalePrecoverage X)
    (trivializations : ∀ k : I, (Scheme.proEtaleSetRestriction X (U k)).obj F ≅
      (constantSheaf (topology (U k).left) (Type (u + 1))).obj
        (ULift.{u + 1} S)) :
    ∃ (n : ℕ) (A : Fin n → X.ProEt) (α : Fin n → I)
      (_refinement : ∀ j, A j ⟶ U (α j)) (V : X.ProEt)
      (ι : ∀ j, (A j).left ⟶ V.left),
      (∀ j, IsAffine (A j).left) ∧
      (∀ j, ι j ≫ V.hom = (A j).hom) ∧
      Nonempty (IsColimit (Cofan.mk V.left ι)) ∧
      IsAffine V.left ∧ Flat V.hom ∧ Surjective V.hom ∧ QuasiCompact V.hom ∧
      Presieve.singleton V.hom ∈ fpqcPrecoverage X ∧
      Presieve.singleton V.hom ∈ proetalePrecoverage X ∧
      ∃ (ψ : (Scheme.proEtaleSetRestriction X V).obj F ≅
          (constantSheaf (topology V.left) (Type (u + 1))).obj
            (ULift.{u + 1} S))
        (e : ((constantSheaf (topology V.left) (Type (u + 1))).obj
          (ULift.{u + 1} S)).obj ≅ localSystemCopiesHom V.left S),
        Presheaf.IsSheaf (topology V.left) (localSystemCopiesHom V.left S) ∧
        (∀ (W : V.left.ProEt) (s : S),
          e.hom.app (op W)
            ((toSheafify (topology V.left)
              ((Functor.const V.left.ProEtᵒᵖ).obj (ULift.{u + 1} S))).app
                (op W) (ULift.up s)) = ULift.up (localSystemLabel S W.hom s)) ∧
        (∀ W : V.left.ProEt,
          (∀ a : Over.mk W.hom ⟶ localSystemCopies V.left S,
            IsClopenDecomposition W.left S (fun s ↦
              a.left ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ V.left) s).opensRange) ∧
            ∀ s : S,
              (a.left ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ V.left) s).opensRange).ι ≫ a.left =
                ((a.left ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ V.left) s).opensRange).ι ≫ W.hom) ≫
                  Sigma.ι (fun _ : S ↦ V.left) s) ∧
          (∀ P : S → W.left.Opens, IsClopenDecomposition W.left S P →
            ∃! a : Over.mk W.hom ⟶ localSystemCopies V.left S,
              ∀ s, a.left ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ V.left) s).opensRange = P s)) ∧
        ∃ D : Over.DescentDatum V.hom (localSystemCopies V.left S),
          (∀ (W : Scheme.{u}) (f₁ f₂ : W ⟶ V.left)
              [WeaklyEtale f₁] [WeaklyEtale f₂]
              (h : f₁ ≫ V.hom = f₂ ≫ V.hom)
              (a : Over.mk f₁ ⟶ localSystemCopies V.left S),
            HEq (ψ.inv.hom.app (op (ProEt.mk f₂))
                (e.inv.app (op (ProEt.mk f₂))
                  (ULift.up (D.transport f₁ f₂ h a))))
              (ψ.inv.hom.app (op (ProEt.mk f₁))
                (e.inv.app (op (ProEt.mk f₁)) (ULift.up a)))) ∧
          ∃! δ : (Over.pullback (pullback.fst V.hom V.hom)).obj
                (localSystemCopies V.left S) ≅
              (Over.pullback (pullback.snd V.hom V.hom)).obj
                (localSystemCopies V.left S),
            LocalSystemTransitionRealizes D (pullback.fst V.hom V.hom)
              (pullback.snd V.hom V.hom) pullback.condition δ ∧
            LocalSystemTransitionRealizes D (pullback.snd V.hom V.hom)
              (pullback.fst V.hom V.hom) pullback.condition.symm δ.symm ∧
            LocalSystemTransitionClopen S D (pullback.fst V.hom V.hom)
              (pullback.snd V.hom V.hom) pullback.condition ∧
            LocalSystemTransitionClopen S D (pullback.snd V.hom V.hom)
              (pullback.fst V.hom V.hom) pullback.condition.symm := by
  obtain ⟨n, A, α, refinement, V, ι, ha, hi, hc, hv, hf, hs, hq, hfp, hp, ⟨ψ⟩⟩ :=
    finite_affine_coproduct_cover X S F I U hcover trivializations
  obtain ⟨e, he, helabel⟩ := constant_copies_comparison V.left S
  obtain ⟨D, hD⟩ := copies_descentDatum X F V S ψ e
  refine ⟨n, A, α, refinement, V, ι, ha, hi, hc, hv, hf, hs, hq, hfp, hp,
    ψ, e, he, helabel, ?_, D, hD, ?_⟩
  · intro W
    obtain ⟨hsections, hexists, _⟩ := coproductCopiesMorphismsClopen V.left W.left S W.hom
    refine ⟨fun a ↦ hsections a.left (Over.w a), ?_⟩
    intro P hP
    obtain ⟨f, hf, huniq⟩ := hexists P hP
    refine ⟨Over.homMk f hf.1, hf.2, ?_⟩
    intro a ha
    apply Over.OverMorphism.ext
    exact huniq a.left ⟨Over.w a, ha⟩
  · obtain ⟨δ, hδ, huniq⟩ := transition_iso D (pullback.fst V.hom V.hom)
      (pullback.snd V.hom V.hom) pullback.condition
    have clopen {B : Scheme.{u}} (r₁ r₂ : B ⟶ V.left)
        (h : r₁ ≫ V.hom = r₂ ≫ V.hom) : LocalSystemTransitionClopen S D r₁ r₂ h := by
      intro s
      exact (coproductCopiesMorphismsClopen V.left B S r₂).1
        (D.transport r₁ r₂ h (localSystemLabel S r₁ s)).left (Over.w _)
    refine ⟨δ, ⟨hδ.1, hδ.2, clopen _ _ _, clopen _ _ _⟩, ?_⟩
    intro ε hε
    exact huniq ε ⟨hε.1, hε.2.1⟩

end AlgebraicGeometry.Scheme.ProEt
