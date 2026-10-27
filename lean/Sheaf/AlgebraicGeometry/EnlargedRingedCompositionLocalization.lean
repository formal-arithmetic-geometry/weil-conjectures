/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism

/-!
# Composition and localization for normalized enlarged ringed sites

Source: Stacks Project, Properties of Spaces, Tags 03G2(2), 03G8(1), 03LP, 04LY, 04LZ
(blueprint: lem-trf-space-enlarged-ringed-composition-localization).

The ring diagram packages the arbitrary ring extensions and their specified chart maps.
Structural maps are transposed in the category of ring sheaves: these are precisely the
ring-object maps of the ringed topoi. The inverse image on ring objects is the one induced
by the geometric inverse image. Its right adjoint is literal base-change precomposition.
The comparison statements allow any left adjoints with this specified right adjoint.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The projection-preserving comparison of iterated fibre products, constructed from
Mathlib's pullback pasting isomorphism, without using the parent ringed-site theorem.
Source: Stacks, Tag 03G2(2)
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
def enlargedCompositionIso {W X Y : AlgebraicSpace S} (g : W ⟶ X) (f : X ⟶ Y) :
    enlargedBaseChange f ⋙ enlargedBaseChange g ≅ enlargedBaseChange (g ≫ f) :=
  NatIso.ofComponents
    (fun V ↦ ObjectProperty.isoMk _ (Over.isoMk
      (ObjectProperty.isoMk _
        (Limits.pullbackRightPullbackFstIso f.hom V.obj.hom.hom g.hom))
      (by
        apply ObjectProperty.hom_ext
        exact Limits.pullbackRightPullbackFstIso_hom_fst _ _ _)))
    (by
      intro V V' a
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      apply Limits.pullback.hom_ext <;>
        simp [enlargedBaseChange, enlargedFibreProductFst, Category.assoc])

/-- The unit comparison is the projection `X ×_X V → V` of the existing model.
Source: Stacks, Tag 03G2(2)
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
def enlargedIdentityIso (X : AlgebraicSpace S) :
    enlargedBaseChange (𝟙 X) ≅ 𝟭 X.EnlargedEtaleSite :=
  NatIso.ofComponents
    (fun V ↦ ObjectProperty.isoMk _ (Over.isoMk
      (ObjectProperty.isoMk _ (asIso (Limits.pullback.snd (𝟙 X.obj) V.obj.hom.hom)))
      (by
        apply ObjectProperty.hom_ext
        change Limits.pullback.snd (𝟙 X.obj) V.obj.hom.hom ≫ V.obj.hom.hom =
          Limits.pullback.fst (𝟙 X.obj) V.obj.hom.hom
        simpa using (Limits.pullback.condition (f := 𝟙 X.obj)
          (g := V.obj.hom.hom)).symm)))
    (by
      intro V V' a
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      simp [enlargedBaseChange])

/-- Direct-image comparison obtained by applying each sheaf contravariantly to the
projection-preserving fibre-product comparison, with no new choice of a map.
Source: Stacks, Tag 03G2(2)
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
def enlargedDirectCompositionIso {W X Y : AlgebraicSpace S}
    (g : W ⟶ X) (f : X ⟶ Y) (A : Type v) [Category.{w} A] :
    enlargedDirectImage g A ⋙ enlargedDirectImage f A ≅ enlargedDirectImage (g ≫ f) A :=
  Functor.sheafPushforwardContinuousComp' (enlargedCompositionIso g f) A _ _ _

/-- Direct-image unit comparison induced by the projection-preserving unit comparison.
Source: Stacks, Tag 03G2(2)
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
def enlargedDirectIdentityIso (X : AlgebraicSpace S) (A : Type v) [Category.{w} A] :
    enlargedDirectImage (𝟙 X) A ≅ 𝟭 (Sheaf X.enlargedEtaleTopology A) :=
  Functor.sheafPushforwardContinuousId' (enlargedIdentityIso X) A _

/-- The assumptions of the node, for arbitrary ring sheaves with specified identifications
on scheme objects and arbitrary structural maps satisfying the regular-function formula.
No commutativity assumption is added. Source: Stacks, Tag 03G8, proof
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
structure EnlargedNormalizedRingDiagram (S : Scheme.{u}) where
  /-- The chosen extension on every algebraic space. -/
  ring : ∀ X : AlgebraicSpace S, Sheaf X.enlargedEtaleTopology RingCat.{u}
  /-- Its specified restriction to the scheme subsite. -/
  normalization : ∀ X : AlgebraicSpace S,
    (enlargedRestriction X RingCat.{u}).obj (ring X) ≅ X.structureSheaf
  /-- The adjoint form of the structural map of each given ringed morphism. -/
  map : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    ring Y ⟶ (enlargedDirectImage f RingCat.{u}).obj (ring X)
  /-- On every commuting scheme-chart triangle, the map pulls back regular functions. -/
  chart : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : X.EtaleSite) (V : Y.EtaleSite) (q : U.obj.left ⟶ V.obj.left)
    (hq : yoneda.map q ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom),
    (normalization Y).inv.hom.app (op V) ≫
      (map f).hom.app (op ((enlargedSchemeInclusion Y).obj V)) ≫
      (ring X).obj.map (enlargedChartLift f U V q hq).op ≫
      (normalization X).hom.hom.app (op U) =
        (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map q.left.op)

/-- The adjunction-compatible comparison of inverse images. It is the conjugate of
exactly the projection-preserving direct-image comparison above.
Source: Stacks, Tags 03G2(2), 03G8(1); Mathlib `Adjunction.leftAdjointCompIso`
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
def enlargedInverseCompositionIso (A : Type v) [Category.{w} A]
    (L : ∀ (X Y : AlgebraicSpace S), (X ⟶ Y) →
      Sheaf Y.enlargedEtaleTopology A ⥤ Sheaf X.enlargedEtaleTopology A)
    (adj : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y), L X Y f ⊣ enlargedDirectImage f A)
    {W X Y : AlgebraicSpace S} (g : W ⟶ X) (f : X ⟶ Y) :
    L X Y f ⋙ L W X g ≅ L W Y (g ≫ f) :=
  Adjunction.leftAdjointCompIso (adj f) (adj g) (adj (g ≫ f))
    (enlargedDirectCompositionIso g f A)

/-- Projection normalization, associativity and unit laws for the site comparisons.
Source: Stacks, Tag 03G2(2)
(blueprint: lem-trf-space-enlarged-ringed-composition-localization).

Proof (node step 1): the fibre-product universal property gives the two projection
identities. For three maps, both composites preserve all projections and therefore
agree. The same uniqueness identifies the comparisons with identities with the
projection unitors, proving both unit laws. Equality transports in the displayed
heterogeneous equalities only reassociate the underlying algebraic-space arrows. -/
theorem enlargedComposition_projection_coherence :
    (∀ (W X Y : AlgebraicSpace S) (g : W ⟶ X) (f : X ⟶ Y)
      (V : Y.EnlargedEtaleSite),
      ((enlargedCompositionIso g f).hom.app V).hom.left.hom ≫
          Limits.pullback.fst (g ≫ f).hom V.obj.hom.hom =
        Limits.pullback.fst g.hom (enlargedFibreProductFst f V.obj.hom).hom ∧
      ((enlargedCompositionIso g f).hom.app V).hom.left.hom ≫
          Limits.pullback.snd (g ≫ f).hom V.obj.hom.hom =
        Limits.pullback.snd g.hom (enlargedFibreProductFst f V.obj.hom).hom ≫
          Limits.pullback.snd f.hom V.obj.hom.hom) ∧
    (∀ (X : AlgebraicSpace S) (V : X.EnlargedEtaleSite),
      ((enlargedIdentityIso X).hom.app V).hom.left.hom =
        Limits.pullback.snd (𝟙 X : X ⟶ X).hom V.obj.hom.hom) ∧
    (∀ (T W X Y : AlgebraicSpace S) (h : T ⟶ W) (g : W ⟶ X) (f : X ⟶ Y),
      HEq (Functor.isoWhiskerRight (enlargedCompositionIso g f) (enlargedBaseChange h) ≪≫
          enlargedCompositionIso h (g ≫ f))
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (enlargedBaseChange f) (enlargedCompositionIso h g) ≪≫
          enlargedCompositionIso (h ≫ g) f)) ∧
    (∀ (X Y : AlgebraicSpace S) (f : X ⟶ Y),
      HEq (enlargedCompositionIso (𝟙 X) f)
        (Functor.isoWhiskerLeft (enlargedBaseChange f) (enlargedIdentityIso X) ≪≫
          Functor.rightUnitor _) ∧
      HEq (enlargedCompositionIso f (𝟙 Y))
        (Functor.isoWhiskerRight (enlargedIdentityIso Y) (enlargedBaseChange f) ≪≫
          Functor.leftUnitor _)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W X Y g f V
    exact ⟨Limits.pullbackRightPullbackFstIso_hom_fst _ _ _,
      Limits.pullbackRightPullbackFstIso_hom_snd _ _ _⟩
  · intro X V
    rfl
  · intro T W X Y h g f
    apply heq_of_eq
    apply Iso.ext
    apply NatTrans.ext
    funext V
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    let v := V.obj.hom.hom
    let a := Limits.pullbackRightPullbackFstIso f.hom v g.hom
    let b := Limits.pullback.map h.hom
      (Limits.pullback.fst g.hom (Limits.pullback.fst f.hom v))
      h.hom (Limits.pullback.fst (g.hom ≫ f.hom) v)
      (𝟙 _) a.hom (𝟙 _) (by simp) (by simp [a])
    let c := Limits.pullbackRightPullbackFstIso (g.hom ≫ f.hom) v h.hom
    let d := Limits.pullbackRightPullbackFstIso g.hom (Limits.pullback.fst f.hom v) h.hom
    let e := Limits.pullbackRightPullbackFstIso f.hom v (h.hom ≫ g.hom)
    change b ≫ c.hom = d.hom ≫ e.hom
    have hb₁ : b ≫ Limits.pullback.fst h.hom (Limits.pullback.fst (g.hom ≫ f.hom) v) =
        Limits.pullback.fst h.hom
          (Limits.pullback.fst g.hom (Limits.pullback.fst f.hom v)) := by
      dsimp only [b]
      rw [Limits.pullback.lift_fst, Category.comp_id]
    have hb₂ : b ≫ Limits.pullback.snd h.hom (Limits.pullback.fst (g.hom ≫ f.hom) v) =
        Limits.pullback.snd h.hom
          (Limits.pullback.fst g.hom (Limits.pullback.fst f.hom v)) ≫ a.hom := by
      exact Limits.pullback.lift_snd _ _ _
    have hc₁ : c.hom ≫ Limits.pullback.fst (h.hom ≫ g.hom ≫ f.hom) v =
        Limits.pullback.fst h.hom (Limits.pullback.fst (g.hom ≫ f.hom) v) :=
      Limits.pullbackRightPullbackFstIso_hom_fst _ _ _
    have hc₂ : c.hom ≫ Limits.pullback.snd (h.hom ≫ g.hom ≫ f.hom) v =
        Limits.pullback.snd h.hom (Limits.pullback.fst (g.hom ≫ f.hom) v) ≫
          Limits.pullback.snd (g.hom ≫ f.hom) v :=
      Limits.pullbackRightPullbackFstIso_hom_snd _ _ _
    have hd₁ : d.hom ≫ Limits.pullback.fst (h.hom ≫ g.hom)
          (Limits.pullback.fst f.hom v) =
        Limits.pullback.fst h.hom
          (Limits.pullback.fst g.hom (Limits.pullback.fst f.hom v)) :=
      Limits.pullbackRightPullbackFstIso_hom_fst _ _ _
    have hd₂ : d.hom ≫ Limits.pullback.snd (h.hom ≫ g.hom)
          (Limits.pullback.fst f.hom v) =
        Limits.pullback.snd h.hom
            (Limits.pullback.fst g.hom (Limits.pullback.fst f.hom v)) ≫
          Limits.pullback.snd g.hom (Limits.pullback.fst f.hom v) :=
      Limits.pullbackRightPullbackFstIso_hom_snd _ _ _
    have he₁ : e.hom ≫ Limits.pullback.fst (h.hom ≫ g.hom ≫ f.hom) v =
        Limits.pullback.fst (h.hom ≫ g.hom) (Limits.pullback.fst f.hom v) :=
      Limits.pullbackRightPullbackFstIso_hom_fst _ _ _
    have he₂ : e.hom ≫ Limits.pullback.snd (h.hom ≫ g.hom ≫ f.hom) v =
        Limits.pullback.snd (h.hom ≫ g.hom) (Limits.pullback.fst f.hom v) ≫
          Limits.pullback.snd f.hom v :=
      Limits.pullbackRightPullbackFstIso_hom_snd _ _ _
    have ha₂ : a.hom ≫ Limits.pullback.snd (g.hom ≫ f.hom) v =
        Limits.pullback.snd g.hom (Limits.pullback.fst f.hom v) ≫
          Limits.pullback.snd f.hom v :=
      Limits.pullbackRightPullbackFstIso_hom_snd _ _ _
    apply Limits.pullback.hom_ext (f := h.hom ≫ g.hom ≫ f.hom) (g := v)
    · rw [Category.assoc, hc₁, hb₁, Category.assoc, he₁, hd₁]
    · rw [Category.assoc, hc₂, ← Category.assoc, hb₂, Category.assoc, ha₂]
      rw [Category.assoc, he₂, ← Category.assoc d.hom, hd₂, Category.assoc]
  · intro X Y f
    constructor
    · apply heq_of_eq
      apply Iso.ext
      apply NatTrans.ext
      funext V
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change (Limits.pullbackRightPullbackFstIso f.hom V.obj.hom.hom (𝟙 X.obj)).hom =
        Limits.pullback.snd (𝟙 X.obj) (Limits.pullback.fst f.hom V.obj.hom.hom)
      apply Limits.pullback.hom_ext (f := f.hom) (g := V.obj.hom.hom)
      · have hp : (Limits.pullbackRightPullbackFstIso f.hom V.obj.hom.hom (𝟙 X.obj)).hom ≫
            Limits.pullback.fst f.hom V.obj.hom.hom =
          Limits.pullback.fst (𝟙 X.obj) (Limits.pullback.fst f.hom V.obj.hom.hom) :=
          Limits.pullbackRightPullbackFstIso_hom_fst _ _ _
        rw [hp]
        simpa only [Category.comp_id] using
          (Limits.pullback.condition (f := 𝟙 X.obj)
            (g := Limits.pullback.fst f.hom V.obj.hom.hom))
      · exact Limits.pullbackRightPullbackFstIso_hom_snd _ _ _
    · apply heq_of_eq
      apply Iso.ext
      apply NatTrans.ext
      funext V
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change (Limits.pullbackRightPullbackFstIso (𝟙 Y.obj) V.obj.hom.hom f.hom).hom =
        Limits.pullback.map f.hom (Limits.pullback.fst (𝟙 Y.obj) V.obj.hom.hom)
          f.hom V.obj.hom.hom (𝟙 _) (Limits.pullback.snd (𝟙 Y.obj) V.obj.hom.hom)
          (𝟙 _) (by simp) (by
            simpa only [Category.comp_id] using
              (Limits.pullback.condition (f := 𝟙 Y.obj) (g := V.obj.hom.hom)))
      apply Limits.pullback.hom_ext (f := f.hom) (g := V.obj.hom.hom)
      · simp only [Limits.pullback.lift_fst, Category.comp_id]
        exact Limits.pullbackRightPullbackFstIso_hom_fst _ _ _
      · simp only [Limits.pullback.lift_snd]
        exact Limits.pullbackRightPullbackFstIso_hom_snd _ _ _

/-- Coherence of the direct images and of their adjunction-compatible inverse images.
This applies to sheaves of sets in any sufficiently large universe and to ring objects.
Source: Stacks, Tag 03G2(2); Mathlib `Adjunction.leftAdjointCompIso_assoc`
(blueprint: lem-trf-space-enlarged-ringed-composition-localization).

Proof (node steps 1--2): apply each sheaf contravariantly to the site comparison.
Naturality and all coherence diagrams follow from the projection identities.
Use the composite adjunction [def-weil-pbc-composite-adjunction] and the unique
conjugate isomorphism [lem-weil-pbc-conjugate-iso-unit-equation]. Its defining unit
equation makes it adjunction compatible. The direct-image associativity equation
is the hypothesis of [lem-trf-adjoint-composition-coherence], proving inverse-image
associativity. The two identity cases follow by the same uniqueness. -/
theorem enlargedDirectInverse_coherence (A : Type v) [Category.{w} A]
    (L : ∀ (X Y : AlgebraicSpace S), (X ⟶ Y) →
      Sheaf Y.enlargedEtaleTopology A ⥤ Sheaf X.enlargedEtaleTopology A)
    (adj : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y), L X Y f ⊣ enlargedDirectImage f A) :
    (∀ (T W X Y : AlgebraicSpace S) (h : T ⟶ W) (g : W ⟶ X) (f : X ⟶ Y),
      HEq (Functor.isoWhiskerLeft (enlargedDirectImage h A)
            (enlargedDirectCompositionIso g f A) ≪≫
          enlargedDirectCompositionIso h (g ≫ f) A)
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (enlargedDirectCompositionIso h g A)
            (enlargedDirectImage f A) ≪≫ enlargedDirectCompositionIso (h ≫ g) f A)) ∧
    (∀ (T W X Y : AlgebraicSpace S) (h : T ⟶ W) (g : W ⟶ X) (f : X ⟶ Y),
      HEq (Functor.isoWhiskerLeft (L X Y f) (enlargedInverseCompositionIso A L adj h g) ≪≫
          enlargedInverseCompositionIso A L adj (h ≫ g) f)
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (enlargedInverseCompositionIso A L adj g f) (L T W h) ≪≫
          enlargedInverseCompositionIso A L adj h (g ≫ f))) ∧
    (∀ (X Y : AlgebraicSpace S) (f : X ⟶ Y),
      HEq (enlargedDirectCompositionIso (𝟙 X) f A)
        (Functor.isoWhiskerRight (enlargedDirectIdentityIso X A) (enlargedDirectImage f A) ≪≫
          Functor.leftUnitor _) ∧
      HEq (enlargedDirectCompositionIso f (𝟙 Y) A)
        (Functor.isoWhiskerLeft (enlargedDirectImage f A) (enlargedDirectIdentityIso Y A) ≪≫
          Functor.rightUnitor _) ∧
      HEq (enlargedInverseCompositionIso A L adj (𝟙 X) f)
        (Functor.isoWhiskerLeft (L X Y f)
            (Adjunction.leftAdjointIdIso (adj (𝟙 X)) (enlargedDirectIdentityIso X A)) ≪≫
          Functor.rightUnitor _) ∧
      HEq (enlargedInverseCompositionIso A L adj f (𝟙 Y))
        (Functor.isoWhiskerRight
            (Adjunction.leftAdjointIdIso (adj (𝟙 Y)) (enlargedDirectIdentityIso Y A)) (L X Y f) ≪≫
          Functor.leftUnitor _)) := by
  have hassoc : ∀ (T W X Y : AlgebraicSpace S)
      (h : T ⟶ W) (g : W ⟶ X) (f : X ⟶ Y),
      Functor.isoWhiskerLeft (enlargedDirectImage h A)
          (enlargedDirectCompositionIso g f A) ≪≫
        enlargedDirectCompositionIso h (g ≫ f) A =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (enlargedDirectCompositionIso h g A)
          (enlargedDirectImage f A) ≪≫ enlargedDirectCompositionIso (h ≫ g) f A := by
    intro T W X Y h g f
    have hs := congrArg Iso.inv
      (eq_of_heq ((enlargedComposition_projection_coherence (S := S)).2.2.1 T W X Y h g f))
    apply Iso.ext
    apply NatTrans.ext
    funext G
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have hv := congrArg (fun k ↦ G.obj.map (k.app V.unop).op) hs
    simpa [enlargedDirectCompositionIso, enlargedDirectImage,
      ← Functor.map_comp, ← op_comp] using hv
  have hunit : ∀ (X Y : AlgebraicSpace S) (f : X ⟶ Y),
      enlargedDirectCompositionIso (𝟙 X) f A =
        Functor.isoWhiskerRight (enlargedDirectIdentityIso X A) (enlargedDirectImage f A) ≪≫
          Functor.leftUnitor _ ∧
      enlargedDirectCompositionIso f (𝟙 Y) A =
        Functor.isoWhiskerLeft (enlargedDirectImage f A) (enlargedDirectIdentityIso Y A) ≪≫
          Functor.rightUnitor _ := by
    intro X Y f
    obtain ⟨h₁, h₂⟩ := (enlargedComposition_projection_coherence (S := S)).2.2.2 X Y f
    constructor
    · have hs := congrArg Iso.inv (eq_of_heq h₁)
      apply Iso.ext
      apply NatTrans.ext
      funext G
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      have hv := congrArg (fun k ↦ k.app V.unop) hs
      change (enlargedCompositionIso (𝟙 X) f).inv.app V.unop =
        (enlargedIdentityIso X).inv.app ((enlargedBaseChange f).obj V.unop) ≫ 𝟙 _ at hv
      rw [Category.comp_id] at hv
      simpa [enlargedDirectCompositionIso, enlargedDirectIdentityIso,
        enlargedDirectImage] using congrArg (fun k ↦ G.obj.map k.op) hv
    · have hs := congrArg Iso.inv (eq_of_heq h₂)
      apply Iso.ext
      apply NatTrans.ext
      funext G
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      have hv := congrArg (fun k ↦ k.app V.unop) hs
      change (enlargedCompositionIso f (𝟙 Y)).inv.app V.unop =
        𝟙 _ ≫ (enlargedBaseChange f).map ((enlargedIdentityIso Y).inv.app V.unop) at hv
      rw [Category.id_comp] at hv
      simpa [enlargedDirectCompositionIso, enlargedDirectIdentityIso,
        enlargedDirectImage] using congrArg (fun k ↦ G.obj.map k.op) hv
  refine ⟨?_, ?_, ?_⟩
  · intro T W X Y h g f
    exact heq_of_eq (hassoc T W X Y h g f)
  · intro T W X Y h g f
    apply heq_of_eq
    exact Adjunction.leftAdjointCompIso_assoc (adj f) (adj g) (adj h)
      (adj (g ≫ f)) (adj (h ≫ g)) (adj (h ≫ g ≫ f))
      (enlargedDirectCompositionIso g f A) (enlargedDirectCompositionIso h g A)
      (enlargedDirectCompositionIso (h ≫ g) f A)
      (enlargedDirectCompositionIso h (g ≫ f) A) (hassoc T W X Y h g f)
  · intro X Y f
    obtain ⟨h₁, h₂⟩ := hunit X Y f
    refine ⟨heq_of_eq h₁, heq_of_eq h₂, ?_, ?_⟩
    · apply heq_of_eq
      exact Adjunction.leftAdjointCompIso_comp_id (adj f) (adj (𝟙 X)) _ _ h₁
    · apply heq_of_eq
      exact Adjunction.leftAdjointCompIso_id_comp (adj (𝟙 Y)) (adj f) _ _ h₂

/-- Composition and identities for the actual normalized ring maps, in adjoint and
inverse-image form. Source: Stacks, Tag 03G8(1)
(blueprint: lem-trf-space-enlarged-ringed-composition-localization).

Proof (node steps 3--4): pull a function on a scheme V to a scheme atlas U of
X ×_Y V, and then to a scheme atlas T of W ×_X U. Both structural composites pull
it back along T → V. Scheme density and sheaf separatedness extend this equality
to every chart and every enlarged object. Uniqueness of normalized structural maps
[lem-trf-space-enlarged-chart-ringed-morphism] proves the direct-image equality.
Each ring of sections embeds in the commutative ring of an atlas, so the commutative
ring formulation of that dependency applies without an extra hypothesis here.
Transpose through the two adjunctions to obtain the inverse-image equality. For an
identity, the chart formula is the identity. For three maps, both structural
composites are the same three adjoint maps under the preceding coherent comparisons.
Thus the associativity and unit diagrams also commute on the structural ring maps. -/
theorem enlargedNormalizedRing_composition (R : EnlargedNormalizedRingDiagram S)
    (L : ∀ (X Y : AlgebraicSpace S), (X ⟶ Y) →
      Sheaf Y.enlargedEtaleTopology RingCat.{u} ⥤ Sheaf X.enlargedEtaleTopology RingCat.{u})
    (adj : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      L X Y f ⊣ enlargedDirectImage f RingCat.{u}) :
    (∀ (W X Y : AlgebraicSpace S) (g : W ⟶ X) (f : X ⟶ Y),
      R.map f ≫ (enlargedDirectImage f RingCat.{u}).map (R.map g) ≫
          (enlargedDirectCompositionIso g f RingCat.{u}).hom.app (R.ring W) = R.map (g ≫ f)) ∧
    (∀ X : AlgebraicSpace S,
      R.map (𝟙 X) ≫ (enlargedDirectIdentityIso X RingCat.{u}).hom.app (R.ring X) = 𝟙 _) ∧
    (∀ (W X Y : AlgebraicSpace S) (g : W ⟶ X) (f : X ⟶ Y),
      (enlargedInverseCompositionIso RingCat.{u} L adj g f).hom.app (R.ring Y) ≫
          ((adj (g ≫ f)).homEquiv _ _).symm (R.map (g ≫ f)) =
        (L W X g).map (((adj f).homEquiv _ _).symm (R.map f)) ≫
          ((adj g).homEquiv _ _).symm (R.map g)) ∧
    (∀ X : AlgebraicSpace S,
      ((adj (𝟙 X)).homEquiv _ _).symm (R.map (𝟙 X)) =
        (Adjunction.leftAdjointIdIso (adj (𝟙 X))
          (enlargedDirectIdentityIso X RingCat.{u})).hom.app (R.ring X)) := by
  sorry

/-- Étale postcomposition is the site localization, with precisely the same covering
families, and inverse functor the original factorization through the étale space.
Source: Stacks, Tags 03LP and 04LY
(blueprint: lem-trf-space-enlarged-ringed-composition-localization).

Proof (node step 5): composition makes postcomposition well-defined. Conversely,
étale cancellation shows that a factorization of two étale objects is étale
[lem-trf-space-chartwise-etale-permanence]. Forgetting and remembering that
factorization are inverse on objects and arrows. The underlying families of maps
and the condition of joint surjectivity are unchanged. This includes empty families.
The localized topology and covering families are those of
[def-pur-localized-ringed-site]. -/
theorem enlargedLocalization_covering_families {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    ∃ E : X.EnlargedEtaleSite ≌ Over (enlargedEtaleObject f hf),
      E.functor = enlargedLocalization f hf ∧
      (∀ T : Over (enlargedEtaleObject f hf),
        (E.inverse.obj T).obj.left = T.left.obj.left ∧
        HEq (E.inverse.obj T).obj.hom T.hom.hom.left) ∧
      (∀ (T U : Over (enlargedEtaleObject f hf)) (a : T ⟶ U),
        HEq (E.inverse.map a).hom.left a.left.hom.left) ∧
      ∀ (T : X.EnlargedEtaleSite) (P : Presieve T),
        P ∈ X.enlargedEtalePrecoverage T ↔
          Presieve.overEquiv (E.functor.obj T) (P.map E.functor) ∈
            Y.enlargedEtalePrecoverage (E.functor.obj T).left := by
  let F := enlargedLocalization f hf
  let G : Over (enlargedEtaleObject f hf) ⥤ X.EnlargedEtaleSite :=
    { obj := fun T ↦ ⟨Over.mk T.hom.hom.left,
        chartwise_etale_permanence.{u, 0, 0}.2.2.2.2.1 _ _ _ T.left.obj.hom f T.hom.hom.left
          T.left.property hf (Over.w T.hom.hom)⟩
      map := fun a ↦ ObjectProperty.homMk (Over.homMk a.left.hom.left (by
        have h := congrArg (fun k ↦ k.hom.left) (Over.w a)
        exact h))
      map_id := by intro T; rfl
      map_comp := by intro T U V a b; rfl }
  let unit : 𝟭 X.EnlargedEtaleSite ≅ F ⋙ G :=
    NatIso.ofComponents (fun T ↦ Iso.refl _) (by intro T U a; simp; rfl)
  let counit : G ⋙ F ≅ 𝟭 (Over (enlargedEtaleObject f hf)) :=
    NatIso.ofComponents
      (fun T ↦ Over.isoMk (ObjectProperty.isoMk _
        (Over.isoMk (Iso.refl _) (by
          change 𝟙 _ ≫ T.left.obj.hom = T.hom.hom.left ≫ f
          have hw := Over.w T.hom.hom
          change T.hom.hom.left ≫ f = T.left.obj.hom at hw
          simpa only [Category.id_comp] using hw.symm)))
        (by apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext; simp; rfl))
      (by
        intro T U a
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        simp
        rfl)
  let E : X.EnlargedEtaleSite ≌ Over (enlargedEtaleObject f hf) :=
    { functor := F
      inverse := G
      unitIso := unit
      counitIso := counit
      functor_unitIso_comp := by
        intro T
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        simp [unit, counit, F, G]
        rfl }
  refine ⟨E, rfl, ?_, ?_, ?_⟩
  · intro T
    exact ⟨rfl, HEq.rfl⟩
  · intro T U a
    exact HEq.rfl
  · intro T P
    have hP : Presieve.overEquiv (F.obj T) (P.map F) =
        P.map (enlargedPostcompose f hf) := by
      funext U a
      apply propext
      constructor
      · rintro ⟨b⟩
        cases b with
        | of hb => exact Presieve.map.of hb
      · rintro ⟨a⟩
        exact Presieve.map.of (Presieve.map.of a)
    rw [hP]
    change
      ((∀ (U : X.EnlargedEtaleSite) (a : U ⟶ T), P a →
        IsChartwiseEtale a.hom.left) ∧
        IsJointlySurjective (fun a : P.uncurry ↦ a.1.2.hom.left.hom.hom)) ↔
      ((∀ (U : Y.EnlargedEtaleSite) (a : U ⟶ (enlargedPostcompose f hf).obj T),
        P.map (enlargedPostcompose f hf) a → IsChartwiseEtale a.hom.left) ∧
        IsJointlySurjective (fun a : (P.map (enlargedPostcompose f hf)).uncurry ↦
          a.1.2.hom.left.hom.hom))
    constructor
    · rintro ⟨he, hs⟩
      constructor
      · intro U a ha
        cases ha with
        | @of U b hb => exact he U b hb
      · intro K hK s x
        obtain ⟨⟨⟨U, a⟩, ha⟩, L, hL, e, y, hy⟩ := hs K s x
        exact ⟨⟨⟨_, (enlargedPostcompose f hf).map a⟩, Presieve.map.of ha⟩,
          L, hL, e, y, hy⟩
    · rintro ⟨he, hs⟩
      constructor
      · intro U a ha
        exact he _ _ (Presieve.map.of ha)
      · intro K hK s x
        obtain ⟨⟨⟨U, a⟩, ha⟩, L, hL, e, y, hy⟩ := hs K s x
        cases ha with
        | of hb => exact ⟨⟨⟨_, _⟩, hb⟩, L, hL, e, y, hy⟩

/-- The graph of an enlarged object over an étale map, into its pullback after
postcomposition. This is the pair of its structure map and its identity.
Source: Stacks, Sites Tag 03CE, proof; Properties of Spaces Tag 03LP
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
def enlargedLocalizationGraph {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) (T : X.EnlargedEtaleSite) :
    T ⟶ (enlargedBaseChange f).obj ((enlargedPostcompose f hf).obj T) :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
    (Limits.pullback.lift T.obj.hom.hom (𝟙 T.obj.left.obj) (by
      change T.obj.hom.hom ≫ f.hom = 𝟙 _ ≫ (T.obj.hom.hom ≫ f.hom)
      simp only [Category.id_comp])))
    (by
      apply ObjectProperty.hom_ext
      exact Limits.pullback.lift_fst _ _ _))

/-- The localization adjunction is normalized by its actual graph counit, for every
coefficient category. This fixes the Hom bijection rather than merely its adjoints.
Source: Stacks, Sites Tag 03CE, proof; Properties of Spaces Tag 03LP
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
def IsEnlargedLocalizationAdjunction {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) (A : Type v) [Category.{w} A]
    (ar : enlargedEtaleRestriction f hf A ⊣ enlargedDirectImage f A) : Prop :=
  ∀ (G : Sheaf X.enlargedEtaleTopology A) (T : X.EnlargedEtaleSite),
    (ar.counit.app G).hom.app (op T) = G.obj.map (enlargedLocalizationGraph f hf T).op

/-- The normalized ring identification and the localization morphism for arbitrary
ring extensions. The direct-image formula is the actual `enlargedDirectImage`.
Source: Stacks, Tags 03LP, 04LY, 04LZ and Sites Tag 03CE
(blueprint: lem-trf-space-enlarged-ringed-composition-localization).

Proof (node steps 6--8): on every scheme T over X, both rings have sections Γ(T,O_T).
Full faithfulness of ring restriction [lem-trf-space-enlarged-atlas-algebraic-extension]
lifts their identity to a unique ring-sheaf isomorphism. Its sections on any enlarged
object are the identical atlas equalizers. By the preceding site equivalence,
[lem-trf-slice-subtopos-site-presentation] identifies restriction and fibre-product
direct image as adjoints, with left exact restriction. The adjoint of the ring
identification restricts on each scheme chart to pullback along T → V. Uniqueness
of the normalized map makes it R.map f. Uniqueness of left adjoints identifies any
given inverse image with restriction compatibly with these adjunctions, and taking
adjoints identifies its structural ring map with this very ring isomorphism. -/
theorem enlargedNormalizedRing_localization (R : EnlargedNormalizedRingDiagram S)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    (∃ ar : enlargedEtaleRestriction f hf (Type (max (u + 1) w)) ⊣
      enlargedDirectImage f (Type (max (u + 1) w)),
      IsEnlargedLocalizationAdjunction f hf _ ar) ∧
    PreservesFiniteLimits (enlargedEtaleRestriction f hf (Type (max (u + 1) w))) ∧
    (∃! ρ : (enlargedEtaleRestriction f hf RingCat.{u}).obj (R.ring Y) ≅ R.ring X,
      ∀ U : X.EtaleSite,
        (R.normalization Y).inv.hom.app (op ((chartwiseEtaleMap f hf).obj U)) ≫
          (R.ring Y).obj.map ((enlargedPostcomposeSchemeIso f hf).inv.app U).op ≫
          ρ.hom.hom.app (op ((enlargedSchemeInclusion X).obj U)) ≫
          (R.normalization X).hom.hom.app (op U) = 𝟙 _) ∧
    ∃ ar : enlargedEtaleRestriction f hf RingCat.{u} ⊣ enlargedDirectImage f RingCat.{u},
      IsEnlargedLocalizationAdjunction f hf RingCat.{u} ar ∧
      ∃ ρ : (enlargedEtaleRestriction f hf RingCat.{u}).obj (R.ring Y) ≅ R.ring X,
        (∀ U : X.EtaleSite,
          (R.normalization Y).inv.hom.app (op ((chartwiseEtaleMap f hf).obj U)) ≫
            (R.ring Y).obj.map ((enlargedPostcomposeSchemeIso f hf).inv.app U).op ≫
            ρ.hom.hom.app (op ((enlargedSchemeInclusion X).obj U)) ≫
            (R.normalization X).hom.hom.app (op U) = 𝟙 _) ∧
        ar.homEquiv _ _ ρ.hom = R.map f ∧
        ∀ (L : Sheaf Y.enlargedEtaleTopology RingCat.{u} ⥤
            Sheaf X.enlargedEtaleTopology RingCat.{u})
          (adj : L ⊣ enlargedDirectImage f RingCat.{u}),
          ((adj.homEquiv _ _).symm (R.map f)) =
            (Adjunction.leftAdjointUniq adj ar).hom.app (R.ring Y) ≫ ρ.hom := by
  sorry

/-- The underlying ring object, using the dependency's canonical coefficient lift.
Source: Stacks, Tag 03G8
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
abbrev enlargedLiftedUnderlyingRing (X : AlgebraicSpace S)
    (R : Sheaf X.enlargedEtaleTopology CommRingCat.{u}) :=
  (sheafCompose X.enlargedEtaleTopology (forget RingCat.{max (u + 1) w})).obj
    (chartNormalizedLiftedRing.{u, w} X R)

/-- The given ringed morphism has the specified adjoint chart normalization.
This packages the existing `IsChartNormalizedRingMap`, rather than replacing it.
Source: Stacks, Tag 03G8, proof
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
def IsNormalizedEnlargedRingedMorphism {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (RX : Sheaf X.enlargedEtaleTopology CommRingCat.{u})
    (RY : Sheaf Y.enlargedEtaleTopology CommRingCat.{u})
    (eX : (enlargedRestriction X RingCat.{u}).obj (chartNormalizedRing X RX) ≅
      X.structureSheaf)
    (eY : (enlargedRestriction Y RingCat.{u}).obj (chartNormalizedRing Y RY) ≅
      Y.structureSheaf)
    (p : RingedToposMorphismOfUniverses
      (chartNormalizedLiftedRing.{u, w} X RX) (chartNormalizedLiftedRing.{u, w} Y RY))
    (hd : p.direct = enlargedDirectImage f (Type (max (u + 1) w))) : Prop :=
  ∃ α : RY ⟶ (enlargedDirectImage f CommRingCat.{u}).obj RX,
    IsChartNormalizedRingMap f RX RY eX eY α ∧
      p.adj.homEquiv _ _ p.ringMap ≫
        (eqToIso hd).hom.app (enlargedLiftedUnderlyingRing.{u, w} X RX) =
          chartNormalizedUnderlyingMap.{u, w} f α

/-- The structural maps of the given ringed-topos morphisms compose under the
projection-preserving direct comparison and its specified adjunction mate.
Source: Stacks, Tags 03G2(2) and 03G8(1)
(blueprint: lem-trf-space-enlarged-ringed-composition-localization).

Proof (node steps 1--4): use the projection comparison on set sheaves, transporting
only the displayed equalities of direct functors. Its conjugate is the unique
adjunction-compatible inverse comparison. The chart calculation in
`enlargedNormalizedRing_composition` identifies the adjoint structural maps;
faithful sectionwise coefficient lifting preserves that equality. Transpose through
the composite adjunction to get the displayed equation for the actual given ring
maps. The preceding direct/inverse coherence and the same transpose prove all
associativity and unit diagrams, including their structural maps. -/
theorem enlargedRingedMorphism_composition {W X Y : AlgebraicSpace S}
    (g : W ⟶ X) (f : X ⟶ Y)
    (RW : Sheaf W.enlargedEtaleTopology CommRingCat.{u})
    (RX : Sheaf X.enlargedEtaleTopology CommRingCat.{u})
    (RY : Sheaf Y.enlargedEtaleTopology CommRingCat.{u})
    (eW : (enlargedRestriction W RingCat.{u}).obj (chartNormalizedRing W RW) ≅
      W.structureSheaf)
    (eX : (enlargedRestriction X RingCat.{u}).obj (chartNormalizedRing X RX) ≅
      X.structureSheaf)
    (eY : (enlargedRestriction Y RingCat.{u}).obj (chartNormalizedRing Y RY) ≅
      Y.structureSheaf)
    (p : RingedToposMorphismOfUniverses
      (chartNormalizedLiftedRing.{u, w} X RX) (chartNormalizedLiftedRing.{u, w} Y RY))
    (q : RingedToposMorphismOfUniverses
      (chartNormalizedLiftedRing.{u, w} W RW) (chartNormalizedLiftedRing.{u, w} X RX))
    (r : RingedToposMorphismOfUniverses
      (chartNormalizedLiftedRing.{u, w} W RW) (chartNormalizedLiftedRing.{u, w} Y RY))
    (hdf : p.direct = enlargedDirectImage f (Type (max (u + 1) w)))
    (hdg : q.direct = enlargedDirectImage g (Type (max (u + 1) w)))
    (hdgf : r.direct = enlargedDirectImage (g ≫ f) (Type (max (u + 1) w)))
    (hp : IsNormalizedEnlargedRingedMorphism f RX RY eX eY p hdf)
    (hq : IsNormalizedEnlargedRingedMorphism g RW RX eW eX q hdg)
    (hr : IsNormalizedEnlargedRingedMorphism (g ≫ f) RW RY eW eY r hdgf) :
    ∃ d : r.direct ≅ q.direct ⋙ p.direct,
      d = eqToIso hdgf ≪≫
        (enlargedDirectCompositionIso g f (Type (max (u + 1) w))).symm ≪≫
        (Functor.isoWhiskerRight (eqToIso hdg) p.direct ≪≫
          Functor.isoWhiskerLeft (enlargedDirectImage g (Type (max (u + 1) w)))
            (eqToIso hdf)).symm ∧
      ∃ a : p.inverse ⋙ q.inverse ≅ r.inverse,
        a = (conjugateIsoEquiv r.adj (p.adj.comp q.adj)).symm d ∧
        a.hom.app (enlargedLiftedUnderlyingRing.{u, w} Y RY) ≫ r.ringMap =
          q.inverse.map p.ringMap ≫ q.ringMap := by
  sorry

/-- Lift the localization ring identification using the same sectionwise coefficient
transport as the given ringed morphisms. No arbitrary comparison is chosen.
Source: Stacks, Tag 04LZ
(blueprint: lem-trf-space-enlarged-ringed-composition-localization). -/
def enlargedLiftedLocalizationRingIso {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f)
    (RX : Sheaf X.enlargedEtaleTopology CommRingCat.{u})
    (RY : Sheaf Y.enlargedEtaleTopology CommRingCat.{u})
    (ρ : (enlargedEtaleRestriction f hf CommRingCat.{u}).obj RY ≅ RX) :
    (enlargedEtaleRestriction f hf (Type (max (u + 1) w))).obj
        (enlargedLiftedUnderlyingRing.{u, w} Y RY) ≅
      enlargedLiftedUnderlyingRing.{u, w} X RX :=
  (sheafCompose X.enlargedEtaleTopology (forget RingCat.{max (u + 1) w})).mapIso
    ((sheafCompose X.enlargedEtaleTopology
      (forget₂ CommRingCat.{max (u + 1) w} RingCat.{max (u + 1) w})).mapIso
      ((sheafCompose X.enlargedEtaleTopology
        (SheafOfModules.CochainUniverseTransport.ringFunctor.{u, u + 1, w})).mapIso ρ))

/-- The actual given ringed morphism of an étale map is localization, including its
structural map and its comparison of inverse images.
Source: Stacks, Tags 03LP, 04LY, 04LZ; Sites Tag 03CE
(blueprint: lem-trf-space-enlarged-ringed-composition-localization).

Proof (node steps 5--8): identify the sites by postcomposition and cancellation.
The unique normalized ring isomorphism lifts the identity on all scheme sections
by full faithfulness of restriction. The slice localization adjunction has inverse
image restriction and direct image fibre-product evaluation. Its structural map
has the required scheme-chart formula, hence equals the given normalized map.
Take the unique adjunction-compatible inverse-image comparison and transpose this
equality. Sectionwise ULift preserves the ring identification and its normalization. -/
theorem enlargedRingedMorphism_localization {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f)
    (RX : Sheaf X.enlargedEtaleTopology CommRingCat.{u})
    (RY : Sheaf Y.enlargedEtaleTopology CommRingCat.{u})
    (eX : (enlargedRestriction X RingCat.{u}).obj (chartNormalizedRing X RX) ≅
      X.structureSheaf)
    (eY : (enlargedRestriction Y RingCat.{u}).obj (chartNormalizedRing Y RY) ≅
      Y.structureSheaf)
    (p : RingedToposMorphismOfUniverses
      (chartNormalizedLiftedRing.{u, w} X RX) (chartNormalizedLiftedRing.{u, w} Y RY))
    (hd : p.direct = enlargedDirectImage f (Type (max (u + 1) w)))
    (hp : IsNormalizedEnlargedRingedMorphism f RX RY eX eY p hd) :
    ∃ (ar : enlargedEtaleRestriction f hf (Type (max (u + 1) w)) ⊣
        enlargedDirectImage f (Type (max (u + 1) w)))
      (ρ : (enlargedEtaleRestriction f hf CommRingCat.{u}).obj RY ≅ RX),
      IsEnlargedLocalizationAdjunction f hf _ ar ∧
      (∀ U : X.EtaleSite,
        eY.inv.hom.app (op ((chartwiseEtaleMap f hf).obj U)) ≫
          (chartNormalizedRing Y RY).obj.map
            ((enlargedPostcomposeSchemeIso f hf).inv.app U).op ≫
          (forget₂ CommRingCat.{u} RingCat.{u}).map
            (ρ.hom.hom.app (op ((enlargedSchemeInclusion X).obj U))) ≫
          eX.hom.hom.app (op U) = 𝟙 _) ∧
      ∃ c : p.inverse ≅ enlargedEtaleRestriction f hf (Type (max (u + 1) w)),
        c = ((conjugateIsoEquiv p.adj ar).symm (eqToIso hd)).symm ∧
        p.ringMap = c.hom.app (enlargedLiftedUnderlyingRing.{u, w} Y RY) ≫
          (enlargedLiftedLocalizationRingIso.{u, w} f hf RX RY ρ).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
