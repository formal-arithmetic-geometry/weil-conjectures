/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedSubspace
public import WeilConjectures.AlgebraicGeometry.IntersectionSectionsFlatBaseChange
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.AlgebraicGeometry.InvariantIntersectionAffineDescent
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding
import WeilConjectures.Topology.InverseImageStalk
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Equivariance of the canonical open image in an intersection affinization

Source: Stacks Project, Tag 0APK, `lemma-ind-quasi-affine`, final diagram.
(blueprint: lem-a1-invariant-open-affinization-equivariance)
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

/-- Restriction from an intersection to an ambient open contained in it. The sheaf map
is the inverse-image adjoint of the open inclusion's actual structure-sheaf map.
Source: Stacks Project, Tag 0APK, restriction of the canonical embedding.
(blueprint: lem-a1-invariant-open-affinization-equivariance). -/
def intersectionOpenRestriction {V : Scheme.{u}} {I : Type v} (U : I → V.Opens)
    (W : V.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    intersectionSections V U ⟶ Γ(W.toScheme, ⊤) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion V U)).homEquiv _ _).symm
      (⟨W.ι.c⟩ : V.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat (intersectionInclusion V U)).obj
          ((TopCat.Sheaf.pushforward CommRingCat
            (TopCat.ofHom ⟨fun x : W ↦ ⟨x.val, hW x⟩,
              continuous_subtype_val.subtype_mk _⟩)).obj W.toScheme.sheaf))).hom.app
                (op ⊤) ≫ W.toScheme.presheaf.map (homOfLE (fun _ _ ↦ trivial)).op

/-- The restriction of the canonical locally ringed map to the spectrum of sections,
constructed by affine adjunction from the restriction homomorphism.
Source: Stacks Project, Tag 0APK, the map `j|W`.
(blueprint: lem-a1-invariant-open-affinization-equivariance). -/
def intersectionOpenAffinization {V : Scheme.{u}} {I : Type v} (U : I → V.Opens)
    (W : V.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    W.toScheme ⟶ Spec (intersectionSections V U) :=
  ΓSpec.adjunction.homEquiv _ _ (intersectionOpenRestriction U W hW).op

/-- The left inclusion into the actual scalar tensor product of section rings.
Source: Stacks Project, Tag 0APK, canonical affine pullback square.
(blueprint: lem-a1-invariant-open-affinization-equivariance). -/
def intersectionTensorLeft {R T : CommRingCat.{u}} (r : R ⟶ T)
    (C : CommAlgCat.{u} R) :
    CommRingCat.of C ⟶
      CommRingCat.of (intersectionScalarTensor r C) := by
  letI := r.hom.toAlgebra
  exact CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

/-- Sections of an ambient open with the scalar action from its given structure map.
Source: Stacks Project, Tag 0APK, the affine chart ring D = Gamma(L, O_L).
(blueprint: lem-a1-invariant-open-affinization-equivariance). -/
def intersectionOpenAlgebra {R : CommRingCat.{u}} {V : Scheme.{u}}
    (f : V ⟶ Spec R) (L : V.Opens) : CommAlgCat.{u} R :=
  letI := ((ΓSpecIso R).inv ≫ (L.ι ≫ f).appTop).hom.toAlgebra
  CommAlgCat.of R Γ(L.toScheme, ⊤)

/-- The canonical restricted map on W times Spec T, in C tensor T coordinates.
Source: Stacks Project, Tag 0APK, the left side of its final diagram.
(blueprint: lem-a1-invariant-open-affinization-equivariance). -/
def intersectionOpenRightMap {R T : CommRingCat.{u}} (r : R ⟶ T)
    {V : Scheme.{u}} (f : V ⟶ Spec R) {I : Type v} (U : I → V.Opens)
    (W : V.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    (pullback.fst f (Spec.map r) ⁻¹ᵁ W).toScheme ⟶
      Spec (CommRingCat.of (intersectionTensorSource r f U)) :=
  intersectionOpenAffinization (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)
    (pullback.fst f (Spec.map r) ⁻¹ᵁ W)
    (fun x i ↦ hW ⟨pullback.fst f (Spec.map r) x.val, x.property⟩ i) ≫
      Spec.map (CommRingCat.ofHom (intersectionBaseChangeMap r f U).hom.toRingHom)

/-- The canonical restricted map on Spec T times W, in T tensor C coordinates.
Source: Stacks Project, Tag 0APK, the right side of its final diagram.
(blueprint: lem-a1-invariant-open-affinization-equivariance). -/
def intersectionOpenLeftMap {R T : CommRingCat.{u}} (r : R ⟶ T)
    {V : Scheme.{u}} (f : V ⟶ Spec R) {I : Type v} (U : I → V.Opens)
    (W : V.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    (pullback.snd (Spec.map r) f ⁻¹ᵁ W).toScheme ⟶
      Spec (intersectionLeftTensor r f U) :=
  intersectionOpenAffinization (fun i ↦ pullback.snd (Spec.map r) f ⁻¹ᵁ U i)
    (pullback.snd (Spec.map r) f ⁻¹ᵁ W)
    (fun x i ↦ hW ⟨pullback.snd (Spec.map r) f x.val, x.property⟩ i) ≫
      Spec.map (intersectionLeftComparison r f U)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

private def intersectionRinged (Y : Scheme.{u}) {I : Type v} (U : I → Y.Opens) :
    SheafedSpace CommRingCat.{u} :=
  LocallyRingedSpace.ringedSubspace Y.toLocallyRingedSpace {x | ∀ i, x ∈ U i}

private def intersectionRingedι (Y : Scheme.{u}) {I : Type v} (U : I → Y.Opens) :
    intersectionRinged Y U ⟶ Y.toSheafedSpace :=
  LocallyRingedSpace.ringedSubspaceι Y.toLocallyRingedSpace {x | ∀ i, x ∈ U i}

private theorem intersectionRingedι_mono (Y : Scheme.{u}) {I : Type v}
    (U : I → Y.Opens) : Mono (intersectionRingedι Y U) := by
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact Subtype.val_injective
  · intro x
    obtain ⟨c, hc, -⟩ := TopCat.Sheaf.exists_inverseImage_stalk_iso_commRing
      (Scheme.intersectionInclusion Y U) x
    have he : (intersectionRingedι Y U).hom.stalkMap x = (c.app Y.sheaf).hom := by
      apply TopCat.Presheaf.stalk_hom_ext
      intro Q hx
      erw [PresheafedSpace.stalkMap_germ]
      apply ConcreteCategory.hom_ext
      intro s
      exact (hc Y.sheaf Q hx s).symm
    rw [he]
    infer_instance

private def intersectionOpenRinged {Y : Scheme.{u}} {I : Type v}
    (U : I → Y.Opens) (W : Y.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    W.toScheme.toSheafedSpace ⟶ intersectionRinged Y U :=
  InducedCategory.homMk
    { base := TopCat.ofHom ⟨fun x : W ↦ ⟨x.val, hW x⟩,
        continuous_subtype_val.subtype_mk _⟩
      c := (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
        (Scheme.intersectionInclusion Y U)).homEquiv Y.sheaf
          ((TopCat.Sheaf.pushforward CommRingCat
            (TopCat.ofHom ⟨fun x : W ↦ ⟨x.val, hW x⟩,
              continuous_subtype_val.subtype_mk _⟩)).obj W.toScheme.sheaf)).symm
                ⟨W.ι.c⟩).hom }

private theorem intersectionOpenRinged_comp {Y : Scheme.{u}} {I : Type v}
    (U : I → Y.Opens) (W : Y.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    intersectionOpenRinged U W hW ≫ intersectionRingedι Y U = W.ι.toLRSHom.toShHom := by
  apply InducedCategory.hom_ext
  apply PresheafedSpace.hext _ _ (by ext x; rfl)
  let k : TopCat.of W ⟶ TopCat.of {x : Y // ∀ i, x ∈ U i} :=
    TopCat.ofHom ⟨fun x ↦ ⟨x.val, hW x⟩, continuous_subtype_val.subtype_mk _⟩
  let c : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat
      (Scheme.intersectionInclusion Y U)).obj
        ((TopCat.Sheaf.pushforward CommRingCat k).obj W.toScheme.sheaf) := ⟨W.ι.c⟩
  have hc := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (Scheme.intersectionInclusion Y U)).homEquiv _ _ |>.apply_symm_apply c
  exact heq_of_eq (congrArg (fun m ↦ m.hom) hc)

private def intersectionRingedMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type v} (U : I → Y.Opens) (Q : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ Q j) → ∀ i, g x ∈ U i) :
    intersectionRinged X Q ⟶ intersectionRinged Y U :=
  InducedCategory.homMk
    { base := Scheme.intersectionSubsetMap g U Q h
      c := (Scheme.intersectionSheafMap g U Q h).hom }

private theorem intersectionRingedMap_comp {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type v} (U : I → Y.Opens) (Q : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ Q j) → ∀ i, g x ∈ U i) :
    intersectionRingedMap g U Q h ≫ intersectionRingedι Y U =
      intersectionRingedι X Q ≫ g.toLRSHom.toShHom := by
  apply InducedCategory.hom_ext
  apply PresheafedSpace.hext _ _ (by ext x; rfl)
  let c : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat
      (Scheme.intersectionInclusion Y U)).obj
        ((TopCat.Sheaf.pushforward CommRingCat
          (Scheme.intersectionSubsetMap g U Q h)).obj
            (Scheme.intersectionStructureSheaf X Q)) :=
    ⟨g.c ≫ Functor.whiskerLeft (Opens.map g.base).op
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
        (Scheme.intersectionInclusion X Q)).unit.app X.sheaf).hom⟩
  have hc := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (Scheme.intersectionInclusion Y U)).homEquiv _ _ |>.apply_symm_apply c
  exact heq_of_eq (congrArg (fun m ↦ m.hom) hc)

private theorem intersection_restriction_naturality
    {X Y : Scheme.{u}} (g : X ⟶ Y) {I J : Type v}
    (U : I → Y.Opens) (Q : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ Q j) → ∀ i, g x ∈ U i)
    (W : Y.Opens) (L : X.Opens)
    (hW : ∀ x : W, ∀ i, x.val ∈ U i)
    (hL : ∀ x : L, ∀ j, x.val ∈ Q j) (hle : L ≤ g ⁻¹ᵁ W) :
    Scheme.intersectionSectionsMap g U Q h ≫
        Scheme.intersectionOpenRestriction Q L hL =
      Scheme.intersectionOpenRestriction U W hW ≫ (g.resLE W L hle).appTop := by
  have : Mono (intersectionRingedι Y U) := intersectionRingedι_mono Y U
  have he : intersectionOpenRinged Q L hL ≫ intersectionRingedMap g U Q h =
      (g.resLE W L hle).toLRSHom.toShHom ≫ intersectionOpenRinged U W hW := by
    apply (cancel_mono (intersectionRingedι Y U)).mp
    rw [Category.assoc, Category.assoc, intersectionRingedMap_comp,
      ← Category.assoc, intersectionOpenRinged_comp, intersectionOpenRinged_comp]
    exact congrArg
      (fun k : L.toScheme ⟶ Y ↦ k.toLRSHom.toShHom)
      (g.resLE_comp_ι hle).symm
  have hc := congrArg (fun k ↦ SheafedSpace.Γ.map k.op) he
  simp only [op_comp, Functor.map_comp] at hc
  unfold Scheme.intersectionSectionsMap Scheme.intersectionOpenRestriction
  change (_ ≫ _) ≫ _ ≫ L.toScheme.presheaf.map (𝟙 (op ⊤)) =
    (_ ≫ W.toScheme.presheaf.map (𝟙 (op ⊤))) ≫ _
  erw [L.toScheme.presheaf.map_id, W.toScheme.presheaf.map_id,
    (Scheme.intersectionStructureSheaf X Q).obj.map_id]
  simp only [Category.comp_id]
  exact hc

private theorem intersection_openRestriction_unit
    {Y : Scheme.{u}} {I : Type v} (U : I → Y.Opens)
    (W : Y.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    Scheme.intersectionRestriction Y U ⊤ (fun _ _ ↦ trivial) ≫
        Scheme.intersectionOpenRestriction U W hW = W.ι.appTop := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (Scheme.intersectionInclusion Y U)
  let k : TopCat.of W ⟶ TopCat.of {x : Y // ∀ i, x ∈ U i} :=
    TopCat.ofHom ⟨fun x ↦ ⟨x.val, hW x⟩, continuous_subtype_val.subtype_mk _⟩
  let c : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat
      (Scheme.intersectionInclusion Y U)).obj
        ((TopCat.Sheaf.pushforward CommRingCat k).obj W.toScheme.sheaf) := ⟨W.ι.c⟩
  have hc := (adj.homEquiv _ _).apply_symm_apply c
  have hc' : (adj.unit.app Y.sheaf).hom.app (op ⊤) ≫
      ((adj.homEquiv _ _).symm c).hom.app (op ⊤) = W.ι.c.app (op ⊤) :=
    congrArg (fun m ↦ m.hom.app (op ⊤)) hc
  unfold Scheme.intersectionRestriction Scheme.intersectionOpenRestriction
  change (_ ≫ _) ≫ _ ≫ W.toScheme.presheaf.map (𝟙 (op ⊤)) = _
  erw [W.toScheme.presheaf.map_id, Category.comp_id]
  erw [(Scheme.intersectionStructureSheaf Y U).obj.map_id, Category.comp_id]
  exact hc'

private theorem intersection_openRestriction_scalars
    {R : CommRingCat.{u}} {Y : Scheme.{u}} (f : Y ⟶ Spec R)
    {I : Type v} (U : I → Y.Opens) (W : Y.Opens)
    (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    Scheme.intersectionScalars f U ≫ Scheme.intersectionOpenRestriction U W hW =
      (Scheme.ΓSpecIso R).inv ≫ (W.ι ≫ f).appTop := by
  unfold Scheme.intersectionScalars
  rw [Category.assoc, Category.assoc, intersection_openRestriction_unit,
    Scheme.Hom.comp_appTop]

private theorem intersection_openAffinization_appTop
    {Y : Scheme.{u}} {I : Type v} (U : I → Y.Opens) (W : Y.Opens)
    (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    (Scheme.ΓSpecIso (Scheme.intersectionSections Y U)).inv ≫
        (Scheme.intersectionOpenAffinization U W hW).appTop =
      Scheme.intersectionOpenRestriction U W hW :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

private theorem intersection_openAffinization_over
    {R : CommRingCat.{u}} {Y : Scheme.{u}} (f : Y ⟶ Spec R)
    {I : Type v} (U : I → Y.Opens) (W : Y.Opens)
    (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    Scheme.intersectionOpenAffinization U W hW ≫
        Spec.map (Scheme.intersectionScalars f U) = W.ι ≫ f := by
  apply ext_to_Spec
  change (Scheme.ΓSpecIso R).inv ≫
    (Scheme.intersectionOpenAffinization U W hW ≫
      Spec.map (Scheme.intersectionScalars f U)).appTop =
        (Scheme.ΓSpecIso R).inv ≫ (W.ι ≫ f).appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    intersection_openAffinization_appTop, intersection_openRestriction_scalars]

private theorem intersection_openAffinization_naturality
    {X Y : Scheme.{u}} (g : X ⟶ Y) {I J : Type v}
    (U : I → Y.Opens) (Q : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ Q j) → ∀ i, g x ∈ U i)
    (W : Y.Opens) (L : X.Opens)
    (hW : ∀ x : W, ∀ i, x.val ∈ U i)
    (hL : ∀ x : L, ∀ j, x.val ∈ Q j) (hle : L ≤ g ⁻¹ᵁ W) :
    Scheme.intersectionOpenAffinization Q L hL ≫
        Spec.map (Scheme.intersectionSectionsMap g U Q h) =
      g.resLE W L hle ≫ Scheme.intersectionOpenAffinization U W hW := by
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (Scheme.intersectionSections Y U)).inv ≫
    (Scheme.intersectionOpenAffinization Q L hL ≫
        Spec.map (Scheme.intersectionSectionsMap g U Q h)).appTop =
    (Scheme.ΓSpecIso (Scheme.intersectionSections Y U)).inv ≫
      (g.resLE W L hle ≫ Scheme.intersectionOpenAffinization U W hW).appTop
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    intersection_openAffinization_appTop, ← Category.assoc,
    intersection_openAffinization_appTop]
  exact intersection_restriction_naturality g U Q h W L hW hL hle

set_option backward.isDefEq.respectTransparency false in
private theorem intersection_open_isOpenImmersion
    {V : Scheme.{u}}
    (hV : ∀ Q : V.Opens, IsCompact (Q : Set V) → Scheme.IsQuasiAffine Q.toScheme)
    {I : Type v} (U : I → V.Opens) (hI : Nonempty I)
    (hqc : ∀ i, IsCompact (U i : Set V))
    (W : V.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    IsOpenImmersion (Scheme.intersectionOpenAffinization U W hW) := by
  let E : Set V := {x | ∀ i, x ∈ U i}
  have hE : E = ⋂ i, (U i : Set V) := by ext x; simp [E]
  have : Nonempty I := hI
  obtain ⟨hl, j, hj, hjuniq, hjimage, hopen, hnatural⟩ :=
    intersection_canonical_affine_embedding V hV I U hqc E hE
  obtain ⟨l, hlbase, hlc, hlj, hlopen⟩ := hopen W (fun x hx ↦ hW ⟨x, hx⟩)
  have hb : l.base = TopCat.ofHom
      ⟨fun x : W ↦ (⟨x.val, hW x⟩ : E),
        continuous_subtype_val.subtype_mk _⟩ := by
    ext x
    exact hlbase x
  have hr : LocallyRingedSpace.Γ.map l.op = Scheme.intersectionOpenRestriction U W hW := by
    cases l with
    | mk l lp =>
      cases l with
      | mk b c =>
        dsimp at hb
        subst b
        have hc : (⟨c⟩ : Scheme.intersectionStructureSheaf V U ⟶
            (TopCat.Sheaf.pushforward CommRingCat
              (TopCat.ofHom ⟨fun x : W ↦ (⟨x.val, hW x⟩ : E),
                continuous_subtype_val.subtype_mk _⟩)).obj W.toScheme.sheaf) =
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
              (Scheme.intersectionInclusion V U)).homEquiv _ _).symm ⟨W.ι.c⟩ := by
          apply (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
            (Scheme.intersectionInclusion V U)).homEquiv _ _ |>.injective
          rw [Equiv.apply_symm_apply]
          apply ObjectProperty.hom_ext
          have hc0 := congrArg InducedCategory.Hom.hom hlc
          injection hc0 with hb0 hc0
        have hc' := congrArg (fun k ↦ k.hom.app (op ⊤)) hc
        change c.app (op ⊤) = _
        dsimp only [Scheme.intersectionOpenRestriction]
        rw [← hc']
        change c.app (op ⊤) = c.app (op ⊤) ≫ W.toScheme.presheaf.map (𝟙 (op ⊤))
        erw [W.toScheme.presheaf.map_id, Category.comp_id]
  have heq : Scheme.Hom.mk (l ≫ j) = Scheme.intersectionOpenAffinization U W hW := by
    rw [hlj, hr]
    rfl
  exact heq ▸ hlopen

private theorem intersection_tensor_inl
    {R T : CommRingCat.{u}} (r : R ⟶ T) {V : Scheme.{u}}
    (f : V ⟶ Spec R) {I : Type v} (U : I → V.Opens) :
    Scheme.intersectionTensorLeft r (Scheme.intersectionAlgebraSections f U) ≫
        CommRingCat.ofHom (Scheme.intersectionBaseChangeMap r f U).hom.toRingHom =
      Scheme.intersectionSectionsMap (pullback.fst f (Spec.map r)) U
        (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) (fun _ hx ↦ hx) := by
  let := r.hom.toAlgebra
  let B := Scheme.intersectionAlgebraSections (pullback.snd f (Spec.map r))
    (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)
  let : Algebra R B := (r ≫ Scheme.intersectionScalars (pullback.snd f (Spec.map r))
    (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)).hom.toAlgebra
  ext c
  dsimp only [Scheme.intersectionTensorLeft, Scheme.intersectionBaseChangeMap,
    Scheme.intersectionTensorMap, CommRingCat.hom_comp, CommRingCat.ofHom_hom,
    CommAlgCat.ofHom_hom]
  exact Algebra.TensorProduct.productMap_left_apply _ _ c

private theorem intersection_tensor_inr
    {R T : CommRingCat.{u}} (r : R ⟶ T) {V : Scheme.{u}}
    (f : V ⟶ Spec R) {I : Type v} (U : I → V.Opens) :
    letI := r.hom.toAlgebra
    CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R)
          (A := Scheme.intersectionAlgebraSections f U) (B := T)).toRingHom ≫
        CommRingCat.ofHom (Scheme.intersectionBaseChangeMap r f U).hom.toRingHom =
      Scheme.intersectionScalars (pullback.snd f (Spec.map r))
        (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) := by
  let := r.hom.toAlgebra
  let B := Scheme.intersectionAlgebraSections (pullback.snd f (Spec.map r))
    (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)
  let : Algebra R B := (r ≫ Scheme.intersectionScalars (pullback.snd f (Spec.map r))
    (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)).hom.toAlgebra
  ext t
  dsimp only [Scheme.intersectionBaseChangeMap, Scheme.intersectionTensorMap,
    CommRingCat.hom_comp, CommRingCat.ofHom_hom, CommAlgCat.ofHom_hom]
  exact Algebra.TensorProduct.productMap_right_apply _ _ t

private theorem intersection_open_baseChange_square
    {R T : CommRingCat.{u}} (r : R ⟶ T) {V : Scheme.{u}}
    (f : V ⟶ Spec R) {I : Type v} (U : I → V.Opens)
    (W : V.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    IsPullback (Scheme.intersectionOpenRightMap r f U W hW)
      ((pullback.fst f (Spec.map r)).resLE W _ le_rfl)
      (Spec.map (Scheme.intersectionTensorLeft r (Scheme.intersectionAlgebraSections f U)))
      (Scheme.intersectionOpenAffinization U W hW) := by
  let := r.hom.toAlgebra
  let C := Scheme.intersectionAlgebraSections f U
  let inr : T ⟶ CommRingCat.of (Scheme.intersectionTensorSource r f U) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have ht := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R C T)
  have hp : IsPullback
      ((pullback.fst f (Spec.map r)).resLE W _ le_rfl)
      ((pullback.fst f (Spec.map r) ⁻¹ᵁ W).ι ≫ pullback.snd f (Spec.map r))
      (W.ι ≫ f) (Spec.map r) := by
    simpa [Scheme.Hom.resLE_eq_morphismRestrict] using
      ((isPullback_morphismRestrict (pullback.fst f (Spec.map r)) W).flip.paste_horiz
        (IsPullback.of_hasPullback f (Spec.map r)).flip).flip
  have hf : Scheme.intersectionOpenAffinization U W hW ≫
      Spec.map (Scheme.intersectionScalars f U) = W.ι ≫ f :=
    intersection_openAffinization_over f U W hW
  have hleft : Scheme.intersectionOpenRightMap r f U W hW ≫
      Spec.map (Scheme.intersectionTensorLeft r C) =
        (pullback.fst f (Spec.map r)).resLE W _ le_rfl ≫
          Scheme.intersectionOpenAffinization U W hW := by
    unfold Scheme.intersectionOpenRightMap
    rw [Category.assoc, ← Spec.map_comp, intersection_tensor_inl]
    exact intersection_openAffinization_naturality _ _ _ _ _ _ _ _ le_rfl
  have hright : Scheme.intersectionOpenRightMap r f U W hW ≫ Spec.map inr =
      (pullback.fst f (Spec.map r) ⁻¹ᵁ W).ι ≫ pullback.snd f (Spec.map r) := by
    unfold Scheme.intersectionOpenRightMap
    rw [Category.assoc, ← Spec.map_comp, intersection_tensor_inr]
    exact intersection_openAffinization_over _ _ _ _
  apply IsPullback.of_right (h₁₂ := Spec.map inr) (h₂₂ := Spec.map
    (Scheme.intersectionScalars f U)) _ hleft ht.flip
  rw [hright, hf]
  exact hp.flip

private theorem intersection_open_right_over
    {R T : CommRingCat.{u}} (r : R ⟶ T) {V : Scheme.{u}}
    (f : V ⟶ Spec R) {I : Type v} (U : I → V.Opens)
    (W : V.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    letI := r.hom.toAlgebra
    Scheme.intersectionOpenRightMap r f U W hW ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R) (A := Scheme.intersectionAlgebraSections f U) (B := T)).toRingHom) =
      (pullback.fst f (Spec.map r) ⁻¹ᵁ W).ι ≫ pullback.snd f (Spec.map r) := by
  unfold Scheme.intersectionOpenRightMap
  rw [Category.assoc, ← Spec.map_comp, intersection_tensor_inr]
  exact intersection_openAffinization_over _ _ _ _

private theorem intersection_tensor_pushout
    {R T : CommRingCat.{u}} (r : R ⟶ T) {C D : CommAlgCat.{u} R}
    (a : C ⟶ D) :
    IsPushout (CommRingCat.ofHom a.hom.toRingHom)
      (Scheme.intersectionTensorLeft r C) (Scheme.intersectionTensorLeft r D)
      (CommRingCat.ofHom (Scheme.intersectionScalarTensorMap r a).hom.toRingHom) := by
  let := r.hom.toAlgebra
  let m := CommRingCat.ofHom (Scheme.intersectionScalarTensorMap r a).hom.toRingHom
  let iC : T ⟶ CommRingCat.of (Scheme.intersectionScalarTensor r C) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let iD : T ⟶ CommRingCat.of (Scheme.intersectionScalarTensor r D) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have ha : CommRingCat.ofHom (algebraMap R C) ≫
      CommRingCat.ofHom a.hom.toRingHom = CommRingCat.ofHom (algebraMap R D) := by
    ext x
    exact a.hom.commutes x
  have hi : iC ≫ m = iD := by
    ext t
    change Algebra.TensorProduct.map a.hom (AlgHom.id R T) (1 ⊗ₜ[R] t) = 1 ⊗ₜ[R] t
    simp
  have hm : CommRingCat.ofHom a.hom.toRingHom ≫ Scheme.intersectionTensorLeft r D =
      Scheme.intersectionTensorLeft r C ≫ m := by
    ext c
    change a.hom c ⊗ₜ[R] (1 : T) =
      Algebra.TensorProduct.map a.hom (AlgHom.id R T) (c ⊗ₜ[R] 1)
    simp
  apply IsPushout.of_left (h₁₁ := CommRingCat.ofHom (algebraMap R C))
    (v₁₁ := r) _ hm (CommRingCat.isPushout_tensorProduct R C T)
  rw [ha, hi]
  exact CommRingCat.isPushout_tensorProduct R D T

set_option backward.isDefEq.respectTransparency false in
private theorem intersection_open_chart
    {R T : CommRingCat.{u}} (r : R ⟶ T) {V : Scheme.{u}}
    (f : V ⟶ Spec R) {I : Type v} (U : I → V.Opens)
    (L : V.Opens) (hL : IsAffineOpen L) (hLU : ∀ x : L, ∀ i, x.val ∈ U i) :
    ∃ μ : CommRingCat.of (Scheme.intersectionTensorSource r f U) ⟶
        CommRingCat.of (Scheme.intersectionScalarTensor r (Scheme.intersectionOpenAlgebra f L)),
      (∀ (c : Scheme.intersectionAlgebraSections f U) (t : T),
        μ (Scheme.intersectionScalarTensorPure r (Scheme.intersectionAlgebraSections f U) c t) =
          Scheme.intersectionScalarTensorPure r (Scheme.intersectionOpenAlgebra f L)
            (Scheme.intersectionOpenRestriction U L hLU c) t) ∧
      IsPushout (Scheme.intersectionOpenRestriction U L hLU)
        (Scheme.intersectionTensorLeft r (Scheme.intersectionAlgebraSections f U))
        (Scheme.intersectionTensorLeft r (Scheme.intersectionOpenAlgebra f L)) μ ∧
      ∃ δ : CommRingCat.of (Scheme.intersectionScalarTensor r
          (Scheme.intersectionOpenAlgebra f L)) ≅
          Γ((pullback.fst f (Spec.map r) ⁻¹ᵁ L).toScheme, ⊤),
        (∀ (d : Scheme.intersectionOpenAlgebra f L) (t : T),
          δ.hom (Scheme.intersectionScalarTensorPure r (Scheme.intersectionOpenAlgebra f L) d t) =
            ((pullback.fst f (Spec.map r)).resLE L _ le_rfl).appTop d *
              ((Scheme.ΓSpecIso T).inv ≫
                ((pullback.fst f (Spec.map r) ⁻¹ᵁ L).ι ≫ pullback.snd f (Spec.map r)).appTop) t) ∧
        (pullback.fst f (Spec.map r) ⁻¹ᵁ L).toScheme.toSpecΓ ≫
            Spec.map δ.hom ≫ Spec.map μ = Scheme.intersectionOpenRightMap r f U L hLU := by
  let := r.hom.toAlgebra
  let C := Scheme.intersectionAlgebraSections f U
  let D := Scheme.intersectionOpenAlgebra f L
  let : Algebra R (Scheme.intersectionSections V U) :=
    (Scheme.intersectionScalars f U).hom.toAlgebra
  let : Algebra R Γ(L.toScheme, ⊤) :=
    ((Scheme.ΓSpecIso R).inv ≫ (L.ι ≫ f).appTop).hom.toAlgebra
  let a : C ⟶ D := CommAlgCat.ofHom
    { toRingHom := show C →+* D from (Scheme.intersectionOpenRestriction U L hLU).hom
      commutes' := by
        intro x
        exact congrArg (fun k : R ⟶ Γ(L.toScheme, ⊤) ↦ k x)
          (intersection_openRestriction_scalars f U L hLU) }
  let μ := CommRingCat.ofHom (Scheme.intersectionScalarTensorMap r a).hom.toRingHom
  have hμ := intersection_tensor_pushout r a
  refine ⟨μ, ?_, hμ, ?_⟩
  · intro c t
    change Algebra.TensorProduct.map a.hom (AlgHom.id R T) (c ⊗ₜ[R] t) = _
    change Algebra.TensorProduct.map a.hom (AlgHom.id R T) (c ⊗ₜ[R] t) =
      a.hom c ⊗ₜ[R] t
    simp
  have hs := intersection_open_baseChange_square r f U L hLU
  have : IsAffine L.toScheme := hL
  have : IsAffine (pullback.fst f (Spec.map r) ⁻¹ᵁ L).toScheme :=
    IsAffine.of_isPullback hs.flip
  have hp := isPushout_appTop_of_isPullback hs.flip
  have hp' : IsPushout (Scheme.intersectionOpenRestriction U L hLU)
      (Scheme.intersectionTensorLeft r C)
      ((pullback.fst f (Spec.map r)).resLE L _ le_rfl).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Scheme.intersectionTensorSource r f U))).inv ≫
        (Scheme.intersectionOpenRightMap r f U L hLU).appTop) := by
    apply hp.of_iso
      (Scheme.ΓSpecIso (Scheme.intersectionSections V U)) (Iso.refl _)
      (Scheme.ΓSpecIso (CommRingCat.of (Scheme.intersectionTensorSource r f U)))
      (Iso.refl _)
    · simp only [Iso.refl_hom, Category.comp_id]
      exact ΓSpec_adjunction_homEquiv_eq _
    · exact Scheme.ΓSpecIso_naturality _
    · simp
    · simp
  let δ := hμ.isoIsPushout _ _ hp'
  refine ⟨δ, ?_, ?_⟩
  · intro d t
    let iC : T ⟶ CommRingCat.of (Scheme.intersectionScalarTensor r C) :=
      CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
    let iD : T ⟶ CommRingCat.of (Scheme.intersectionScalarTensor r D) :=
      CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
    have hdl : Scheme.intersectionTensorLeft r D ≫ δ.hom =
        ((pullback.fst f (Spec.map r)).resLE L _ le_rfl).appTop :=
      hμ.inl_isoIsPushout_hom _ _ hp'
    have hdr : μ ≫ δ.hom =
        (Scheme.ΓSpecIso (CommRingCat.of (Scheme.intersectionTensorSource r f U))).inv ≫
          (Scheme.intersectionOpenRightMap r f U L hLU).appTop :=
      hμ.inr_isoIsPushout_hom _ _ hp'
    have hi : iC ≫ μ = iD := by
      ext t
      change Algebra.TensorProduct.map a.hom (AlgHom.id R T) (1 ⊗ₜ[R] t) = 1 ⊗ₜ[R] t
      simp
    have hdi : iD ≫ δ.hom = (Scheme.ΓSpecIso T).inv ≫
        ((pullback.fst f (Spec.map r) ⁻¹ᵁ L).ι ≫ pullback.snd f (Spec.map r)).appTop := by
      rw [← hi, Category.assoc, hdr]
      change iC ≫ (Scheme.ΓSpecIso (CommRingCat.of (Scheme.intersectionScalarTensor r C))).inv ≫
        (Scheme.intersectionOpenRightMap r f U L hLU).appTop = _
      rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality iC, Category.assoc,
        ← Scheme.Hom.comp_appTop]
      exact congrArg (fun k : (pullback.fst f (Spec.map r) ⁻¹ᵁ L).toScheme ⟶ Spec T ↦
        (Scheme.ΓSpecIso T).inv ≫ k.appTop)
        (intersection_open_right_over r f U L hLU)
    have hdl' := ConcreteCategory.congr_hom hdl d
    have hdi' := ConcreteCategory.congr_hom hdi t
    change δ.hom (d ⊗ₜ[R] t) = _
    rw [show d ⊗ₜ[R] t = (d ⊗ₜ[R] (1 : T)) * ((1 : D) ⊗ₜ[R] t) by simp,
      map_mul]
    exact congrArg₂ (· * ·) hdl' hdi'
  · have he : μ ≫ δ.hom =
        (Scheme.ΓSpecIso (CommRingCat.of (Scheme.intersectionTensorSource r f U))).inv ≫
          (Scheme.intersectionOpenRightMap r f U L hLU).appTop :=
      hμ.inr_isoIsPushout_hom _ _ hp'
    rw [← Spec.map_comp, he, Spec.map_comp, ← Category.assoc,
      ← Scheme.toSpecΓ_naturality]
    rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Flat affine comparison for the canonical open map, including its open image and
all affine-chart ring pushouts. The comparison is fixed by the canonical tensor map.

Source: Stacks Project, Tag 0APK, `lemma-ind-quasi-affine`, final diagram.
(blueprint: lem-a1-invariant-open-affinization-equivariance).

Proof:
1. Inverse-image stalks identify the intersection's local rings with ambient stalks
   (lem-weil-pbc-topological-inverse-image-stalk). The inverse-image adjunction restricts
   the inclusion to any open contained in the intersection.
2. The canonical intersection embedding is open on W
   (lem-a1-intersection-canonical-affine-embedding). The flat section comparison is the
   isomorphism alpha, with formula c tensor t maps to g-sharp(c)t
   (lem-a1-intersection-sections-flat-base-change).
3. Affine adjunction and the tensor universal property identify Spec(C tensor T) with
   Spec C times_S Spec T. Restrict the ambient pullback square to W and cancel the
   tensor-spectrum square to obtain the asserted pullback square
   (lem-a1-locally-ringed-space-affine-adjunction,
   lem-weil-pbc-algebra-tensor-pushout-universal-property).
4. Both restricted maps induce the same section map on pure tensors; tensor uniqueness
   and affine adjunction identify them. Their open images are therefore inverse images.
5. On an affine chart, the map is restriction tensor identity. Compatible maps out of
   D and C tensor T extend uniquely from D tensor T by d tensor t maps to u(d)v(1 tensor t).
   This is exactly the asserted pushout (the same tensor universal property). -/
theorem invariant_open_affinization_flat_comparison
    {R T : CommRingCat.{u}} (r : R ⟶ T) {V : Scheme.{u}}
    (f : V ⟶ Spec R) [QuasiSeparatedSpace V] [Flat (Spec.map r)]
    (hV : ∀ Q : V.Opens, IsCompact (Q : Set V) → Scheme.IsQuasiAffine Q.toScheme)
    {I : Type v} (U : I → V.Opens) (hI : Nonempty I)
    (hqc : ∀ i, IsCompact (U i : Set V))
    (W : V.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    IsOpenImmersion (Scheme.intersectionOpenAffinization U W hW) ∧
    ∃ α : CommRingCat.of (Scheme.intersectionTensorSource r f U) ≅
        Scheme.intersectionSections (pullback f (Spec.map r))
          (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i),
      α.hom = CommRingCat.ofHom (Scheme.intersectionBaseChangeMap r f U).hom.toRingHom ∧
      IsPullback
        (Scheme.intersectionOpenAffinization
          (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)
          (pullback.fst f (Spec.map r) ⁻¹ᵁ W)
          (fun x i ↦ hW ⟨pullback.fst f (Spec.map r) x.val, x.property⟩ i) ≫
            Spec.map α.hom)
        ((pullback.fst f (Spec.map r)).resLE W _ le_rfl)
        (Spec.map (Scheme.intersectionTensorLeft r
          (Scheme.intersectionAlgebraSections f U)))
        (Scheme.intersectionOpenAffinization U W hW) ∧
      Set.range
        (Scheme.intersectionOpenAffinization
          (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)
          (pullback.fst f (Spec.map r) ⁻¹ᵁ W)
          (fun x i ↦ hW ⟨pullback.fst f (Spec.map r) x.val, x.property⟩ i) ≫
            Spec.map α.hom) =
        (Spec.map (Scheme.intersectionTensorLeft r
          (Scheme.intersectionAlgebraSections f U))) ⁻¹'
            Set.range (Scheme.intersectionOpenAffinization U W hW) ∧
      (∀ (L : V.Opens) (_hL : IsAffineOpen L) (hLW : L ≤ W),
        ∃ μ : CommRingCat.of (Scheme.intersectionTensorSource r f U) ⟶
            CommRingCat.of (Scheme.intersectionScalarTensor r
              (Scheme.intersectionOpenAlgebra f L)),
          (∀ (c : Scheme.intersectionAlgebraSections f U) (t : T),
            μ (Scheme.intersectionScalarTensorPure r
              (Scheme.intersectionAlgebraSections f U) c t) =
            Scheme.intersectionScalarTensorPure r (Scheme.intersectionOpenAlgebra f L)
              (Scheme.intersectionOpenRestriction U L
                (fun x i ↦ hW ⟨x.val, hLW x.property⟩ i) c) t) ∧
          IsPushout
            (Scheme.intersectionOpenRestriction U L
              (fun x i ↦ hW ⟨x.val, hLW x.property⟩ i))
            (Scheme.intersectionTensorLeft r (Scheme.intersectionAlgebraSections f U))
            (Scheme.intersectionTensorLeft r (Scheme.intersectionOpenAlgebra f L)) μ ∧
          ∃ δ : CommRingCat.of (Scheme.intersectionScalarTensor r
                (Scheme.intersectionOpenAlgebra f L)) ≅
              Γ((pullback.fst f (Spec.map r) ⁻¹ᵁ L).toScheme, ⊤),
            (∀ (d : Scheme.intersectionOpenAlgebra f L) (t : T),
              δ.hom (Scheme.intersectionScalarTensorPure r
                (Scheme.intersectionOpenAlgebra f L) d t) =
              ((pullback.fst f (Spec.map r)).resLE L _ le_rfl).appTop d *
                ((Scheme.ΓSpecIso T).inv ≫
                  ((pullback.fst f (Spec.map r) ⁻¹ᵁ L).ι ≫
                    pullback.snd f (Spec.map r)).appTop) t) ∧
            (pullback.fst f (Spec.map r) ⁻¹ᵁ L).toScheme.toSpecΓ ≫
                Spec.map δ.hom ≫ Spec.map μ =
              Scheme.intersectionOpenAffinization
                (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)
                (pullback.fst f (Spec.map r) ⁻¹ᵁ L)
                (fun x i ↦ hW ⟨pullback.fst f (Spec.map r) x.val,
                  hLW x.property⟩ i) ≫ Spec.map α.hom) := by
  have hopen := intersection_open_isOpenImmersion hV U hI hqc W hW
  have hb := (flat_affine_intersection_sections_base_change.{u, v, v} r f U hI hqc).1
  let α := (RingEquiv.ofBijective
    (Scheme.intersectionBaseChangeMap r f U).hom.toRingHom hb).toCommRingCatIso
  have hα : α.hom =
      CommRingCat.ofHom (Scheme.intersectionBaseChangeMap r f U).hom.toRingHom := rfl
  have hs := intersection_open_baseChange_square r f U W hW
  refine ⟨hopen, α, hα, hs, ?_, ?_⟩
  · change Set.range (Scheme.intersectionOpenRightMap r f U W hW) = _
    rw [← hs.isoPullback_hom_fst]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr ((inferInstance : Surjective hs.isoPullback.hom).surj), Set.image_univ]
    exact Scheme.Pullback.range_fst _ _
  · intro L hL hLW
    obtain ⟨μ, hμ, hp, δ, hδ, he⟩ := intersection_open_chart r f U L hL
      (fun x i ↦ hW ⟨x.val, hLW x.property⟩ i)
    exact ⟨μ, hμ, hp, δ, hδ, he⟩


private theorem intersection_left_naturality
    {R T : CommRingCat.{u}} (r : R ⟶ T) {V : Scheme.{u}}
    (f : V ⟶ Spec R) {I : Type v} (U : I → V.Opens)
    (W : V.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    Scheme.intersectionOpenLeftMap r f U W hW =
      ((pullbackSymmetry (Spec.map r) f).hom.resLE
        (pullback.fst f (Spec.map r) ⁻¹ᵁ W)
        (pullback.snd (Spec.map r) f ⁻¹ᵁ W) (by
          intro x hx
          simpa only [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
            pullbackSymmetry_hom_comp_fst] using hx)) ≫
        Scheme.intersectionOpenRightMap r f U W hW ≫
          Spec.map (Scheme.intersectionTensorSwap r f U) := by
  have hn := intersection_openAffinization_naturality
    (pullbackSymmetry (Spec.map r) f).hom
    (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)
    (fun i ↦ pullback.snd (Spec.map r) f ⁻¹ᵁ U i)
    (by intro x hx i; simpa only [Scheme.Hom.mem_preimage,
          ← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst] using hx i)
    (pullback.fst f (Spec.map r) ⁻¹ᵁ W)
    (pullback.snd (Spec.map r) f ⁻¹ᵁ W)
    (fun x i ↦ hW ⟨pullback.fst f (Spec.map r) x.val, x.property⟩ i)
    (fun x i ↦ hW ⟨pullback.snd (Spec.map r) f x.val, x.property⟩ i)
    (by intro x hx; simpa only [Scheme.Hom.mem_preimage,
          ← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst] using hx)
  unfold Scheme.intersectionOpenLeftMap Scheme.intersectionOpenRightMap
    Scheme.intersectionLeftComparison
  simpa only [Spec.map_comp, Category.assoc, Scheme.intersectionTensorSwap] using
    congrArg (fun q ↦ q ≫
      Spec.map (CommRingCat.ofHom (Scheme.intersectionBaseChangeMap r f U).hom.toRingHom) ≫
      Spec.map (Scheme.intersectionTensorSwap r f U)) hn

private theorem descent_transport_cancel
    {R A : CommRingCat.{u}} (r : R ⟶ A) (V : Over (Spec A))
    (D : Over.DescentDatum (Spec.map r) V) {H : Scheme.{u}}
    (a b : H ⟶ Spec A) (hab : a ≫ Spec.map r = b ≫ Spec.map r)
    (v : Over.mk a ⟶ V) :
    pullback.lift (D.transport a b hab v).left a (by
      rw [← Category.assoc, Over.w]; exact hab.symm) ≫ D.toHom = v.left := by
  rw [← D.transport_left_eq_lift_toHom b a hab.symm]
  rw [D.transport_transport, D.transport_self]

private theorem descent_overlap_iso
    {R A : CommRingCat.{u}} (r : R ⟶ A) (V : Over (Spec A))
    (D : Over.DescentDatum (Spec.map r) V) :
    IsIso (Scheme.invariantIntersectionOverlap r V D) := by
  let P := pullback (V.hom ≫ Spec.map r) (Spec.map r)
  let a : P ⟶ Spec A := pullback.fst _ _ ≫ V.hom
  let b : P ⟶ Spec A := pullback.snd _ _
  have hab : a ≫ Spec.map r = b ≫ Spec.map r := by
    dsimp [a, b]
    rw [Category.assoc, pullback.condition]
  let v : Over.mk a ⟶ V := Over.DescentDatum.universalPoint
  let w : Over.mk b ⟶ V := D.transport a b hab v
  have hw : w.left = D.toHom := rfl
  let Q := pullback (Spec.map r) (V.hom ≫ Spec.map r)
  let q : Q ⟶ Spec A := pullback.fst _ _
  let z : Over.mk (pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) ≫ V.hom) ⟶ V :=
    Over.homMk (pullback.snd _ _) rfl
  have hz : (pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) ≫ V.hom) ≫ Spec.map r =
      q ≫ Spec.map r := by
    rw [Category.assoc, ← pullback.condition]
  let t := D.transport _ q hz z
  let inv : Q ⟶ P := pullback.lift t.left (pullback.snd _ _ ≫ V.hom) (by
    rw [← Category.assoc, Over.w t]
    exact (pullback.condition (f := Spec.map r) (g := V.hom ≫ Spec.map r)))
  have hback : inv ≫ D.toHom = z.left :=
    descent_transport_cancel r V D _ _ hz z
  have hinv : inv ≫ Scheme.invariantIntersectionOverlap r V D = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Scheme.invariantIntersectionOverlap, pullback.lift_fst,
        Category.id_comp]
      change inv ≫ pullback.fst _ _ ≫ V.hom = q
      dsimp [inv]
      rw [pullback.lift_fst_assoc, Over.w t]
      rfl
    · simpa only [Category.assoc, Scheme.invariantIntersectionOverlap, pullback.lift_snd,
        Category.id_comp, z, Over.homMk_left] using hback
  have hc : Scheme.invariantIntersectionOverlap r V D ≫
      pullback.lift z.left q (by
        rw [← Category.assoc, Over.w z]; exact hz) =
      pullback.lift D.toHom a (by
        change w.left ≫ (V.hom ≫ Spec.map r) = a ≫ Spec.map r
        rw [← Category.assoc, Over.w w]; exact hab.symm) := by
    apply pullback.hom_ext <;>
      simp [Category.assoc, Scheme.invariantIntersectionOverlap, z, q, a]
  have hhom : Scheme.invariantIntersectionOverlap r V D ≫ inv = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, inv, pullback.lift_fst, Category.id_comp]
      change Scheme.invariantIntersectionOverlap r V D ≫ t.left = v.left
      rw [D.transport_left_eq_lift_toHom, ← Category.assoc, hc]
      exact descent_transport_cancel r V D a b hab v
    · simp only [Category.assoc, inv, pullback.lift_snd, Category.id_comp]
      change Scheme.invariantIntersectionOverlap r V D ≫
        pullback.snd _ _ ≫ V.hom = b
      simp only [Scheme.invariantIntersectionOverlap, pullback.lift_snd_assoc]
      exact Over.w w
  exact ⟨⟨inv, hhom, hinv⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem intersection_affineOverlap_fst
    {R A : CommRingCat.{u}} (r : R ⟶ A) (V : Over (Spec A))
    {I : Type v} (U : I → V.left.Opens) :
    (Scheme.intersectionAffineOverlapIso r V U).hom ≫
      Spec.map (Scheme.intersectionTensorLeft r
        (Scheme.intersectionAlgebraSections (V.hom ≫ Spec.map r) U)) =
      pullback.fst ((Scheme.intersectionAffineModel V U).hom ≫ Spec.map r)
        (Spec.map r) := by
  unfold Scheme.intersectionAffineOverlapIso Scheme.intersectionTensorLeft
  simp only [Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst,
    pullback.congrHom_hom, pullback.map, Category.comp_id]
  erw [pullback.lift_fst]

set_option backward.isDefEq.respectTransparency false in
private theorem intersection_affineOverlap_snd
    {R A : CommRingCat.{u}} (r : R ⟶ A) (V : Over (Spec A))
    {I : Type v} (U : I → V.left.Opens) :
    letI := r.hom.toAlgebra
    (Scheme.intersectionAffineOverlapIso r V U).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := Scheme.intersectionAlgebraSections (V.hom ≫ Spec.map r) U)
        (B := A)).toRingHom) =
      pullback.snd ((Scheme.intersectionAffineModel V U).hom ≫ Spec.map r)
        (Spec.map r) := by
  let := r.hom.toAlgebra
  unfold Scheme.intersectionAffineOverlapIso
  simp only [Iso.trans_hom, Category.assoc]
  erw [pullbackSpecIso_hom_snd R
    (Scheme.intersectionAlgebraSections (V.hom ≫ Spec.map r) U) A]
  simp only [pullback.congrHom_hom, pullback.map, Category.comp_id]
  exact pullback.lift_snd _ _ _

private theorem intersection_right_coordinates
    {R A : CommRingCat.{u}} (r : R ⟶ A) (V : Over (Spec A))
    {I : Type v} (U : I → V.left.Opens)
    (W : V.left.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    Scheme.intersectionOpenRightMap r (V.hom ≫ Spec.map r) U W hW ≫
      (Scheme.intersectionAffineOverlapIso r V U).inv ≫
      pullback.fst _ _ =
    (pullback.fst (V.hom ≫ Spec.map r) (Spec.map r)).resLE W _ le_rfl ≫
      Scheme.intersectionOpenAffinization U W hW := by
  have he := intersection_affineOverlap_fst r V U
  rw [← he, Iso.inv_hom_id_assoc]
  exact (intersection_open_baseChange_square r (V.hom ≫ Spec.map r) U W hW).w

private theorem intersection_right_coordinates_snd
    {R A : CommRingCat.{u}} (r : R ⟶ A) (V : Over (Spec A))
    {I : Type v} (U : I → V.left.Opens)
    (W : V.left.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i) :
    Scheme.intersectionOpenRightMap r (V.hom ≫ Spec.map r) U W hW ≫
      (Scheme.intersectionAffineOverlapIso r V U).inv ≫ pullback.snd _ _ =
      (pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ W).ι ≫
        pullback.snd (V.hom ≫ Spec.map r) (Spec.map r) := by
  let := r.hom.toAlgebra
  have he := intersection_affineOverlap_snd r V U
  rw [← he, Iso.inv_hom_id_assoc]
  exact intersection_open_right_over r (V.hom ≫ Spec.map r) U W hW

private theorem restrict_iso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (S : X.Opens) (T : Y.Opens) (h : S = f ⁻¹ᵁ T) :
    ∃ k : S.toScheme ≅ T.toScheme, k.hom ≫ T.ι = S.ι ≫ f := by
  subst S
  exact ⟨asIso (f ∣_ T), morphismRestrict_ι _ _⟩

set_option backward.isDefEq.respectTransparency false in
/-- Equivariance of the canonical open image for the given descent datum. The section
isomorphism psi is characterized using the actual overlap comorphism, and F is the
corresponding affine scheme datum. The final transport equations express compatibility
of the restricted descent data through the displayed isomorphism W = J.

Source: Stacks Project, Tag 0APK, `lemma-ind-quasi-affine`, final canonical diagram and
its invariant-open-image assertion.
(blueprint: lem-a1-invariant-open-affinization-equivariance).

Proof:
1. Obtain the canonical section comparisons, psi and F from
   lem-a1-invariant-intersection-affine-descent. The canonical restricted maps are
   intersectionOpenRightMap and intersectionOpenLeftMap, related by pullback and
   tensor symmetry.
2. Restrict the overlap to the inverse-image ringed subspaces. Inverse-image adjunction
   units make this restriction canonical and compatible with composition. On sections,
   conjugate its comorphism by the two flat comparisons to obtain psi, as in
   lem-a1-invariant-intersection-affine-descent. This also gives the affine datum F.
3. Both composites in the asserted equivariance equation induce this same section map.
   Tensor uniqueness and affine adjunction identify the morphisms
   (lem-weil-pbc-algebra-tensor-pushout-universal-property and
   lem-a1-locally-ringed-space-affine-adjunction).
4. Invariance of W restricts the overlap isomorphism to k. Taking images in the equation
   gives Spec(psi)(J times X) = X times J. The flat comparison identifies these images
   with the open base changes of J, including their restricted structure sheaves.
5. The open immersion W to Spec C identifies W with its image J. The same equivariance
   equation on test-scheme points identifies the restricted transport maps. Conjugating
   the cocycle through this isomorphism cancels the adjacent inverse pairs, so it
   intertwines the restricted descent data. -/
theorem invariant_open_affinization_equivariance
    {R A : CommRingCat.{u}} (r : R ⟶ A)
    [Flat (Spec.map r)] [Surjective (Spec.map r)]
    (V : Over (Spec A)) [QuasiSeparatedSpace V.left]
    (hV : ∀ Q : V.left.Opens, IsCompact (Q : Set V.left) →
      Scheme.IsQuasiAffine Q.toScheme)
    (D : Over.DescentDatum (Spec.map r) V)
    {I : Type v} (U : I → V.left.Opens) (hI : Nonempty I)
    (hqc : ∀ i, IsCompact (U i : Set V.left))
    (W : V.left.Opens) (hW : ∀ x : W, ∀ i, x.val ∈ U i)
    (hEinv : ∀ x : ↥(pullback (V.hom ≫ Spec.map r) (Spec.map r) : Scheme.{u}),
      (∀ i, pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) x ∈ U i) ↔
        ∀ i, D.toHom x ∈ U i)
    (hWinv : pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ W =
      D.toHom ⁻¹ᵁ W) :
    ∃ ψ : Scheme.intersectionLeftTensor r (V.hom ≫ Spec.map r) U ≅
        CommRingCat.of (Scheme.intersectionTensorSource r (V.hom ≫ Spec.map r) U),
      ψ.hom ≫ CommRingCat.ofHom
          (Scheme.intersectionBaseChangeMap r (V.hom ≫ Spec.map r) U).hom.toRingHom =
        Scheme.intersectionLeftComparison r (V.hom ≫ Spec.map r) U ≫
          Scheme.intersectionSectionsMap (Scheme.invariantIntersectionOverlap r V D)
            (fun i ↦ pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) ⁻¹ᵁ U i)
            (fun i ↦ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ U i)
            (fun x hx i ↦ by
              change ((Scheme.invariantIntersectionOverlap r V D ≫
                pullback.snd (Spec.map r) (V.hom ≫ Spec.map r)) x) ∈ U i
              simpa only [Scheme.invariantIntersectionOverlap, pullback.lift_snd,
                Scheme.Hom.mem_preimage] using (hEinv x).mp hx i) ∧
      (∃ k : (pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ W).toScheme ≅
            (pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) ⁻¹ᵁ W).toScheme,
        k.hom ≫ (pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) ⁻¹ᵁ W).ι =
          (pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ W).ι ≫
            Scheme.invariantIntersectionOverlap r V D ∧
        Scheme.intersectionOpenRightMap r (V.hom ≫ Spec.map r) U W hW ≫
            Spec.map ψ.hom =
          k.hom ≫ Scheme.intersectionOpenLeftMap r (V.hom ≫ Spec.map r) U W hW) ∧
      Spec.map ψ.hom ''
          Set.range (Scheme.intersectionOpenRightMap r (V.hom ≫ Spec.map r) U W hW) =
        Set.range (Scheme.intersectionOpenLeftMap r (V.hom ≫ Spec.map r) U W hW) ∧
      ∃ F : Over.DescentDatum (Spec.map r) (Scheme.intersectionAffineModel V U),
        Scheme.invariantIntersectionOverlap r (Scheme.intersectionAffineModel V U) F ≫
            (pullbackSymmetry (Spec.map r)
              ((Scheme.intersectionAffineModel V U).hom ≫ Spec.map r)).hom ≫
            (Scheme.intersectionAffineOverlapIso r V U).hom ≫
            Spec.map (Scheme.intersectionTensorSwap r (V.hom ≫ Spec.map r) U) =
          (Scheme.intersectionAffineOverlapIso r V U).hom ≫ Spec.map ψ.hom ∧
        ∃ (J : (Spec (Scheme.intersectionSections V.left U)).Opens)
          (e : W.toScheme ≅ J.toScheme),
          e.hom ≫ J.ι = Scheme.intersectionOpenAffinization U W hW ∧
          (J : Set (Spec (Scheme.intersectionSections V.left U))) =
            Set.range (Scheme.intersectionOpenAffinization U W hW) ∧
          ∃ hhA : Scheme.intersectionOpenAffinization U W hW ≫
                (Scheme.intersectionAffineModel V U).hom = W.ι ≫ V.hom,
            ∀ (H : Scheme.{u}) (a b : H ⟶ Spec A) (hab : a ≫ Spec.map r = b ≫ Spec.map r)
              (vW : Over.mk a ⟶ Over.mk (W.ι ≫ V.hom)),
              ∃ vW' : Over.mk b ⟶ Over.mk (W.ι ≫ V.hom),
                vW'.left ≫ W.ι =
                  (D.transport a b hab (Over.homMk (vW.left ≫ W.ι)
                    (by
                      change (vW.left ≫ W.ι) ≫ V.hom = a
                      exact (Category.assoc _ _ _).trans (Over.w vW)))).left ∧
                vW'.left ≫ Scheme.intersectionOpenAffinization U W hW =
                  (F.transport a b hab
                    (Over.homMk (vW.left ≫ Scheme.intersectionOpenAffinization U W hW)
                      (by
                        rw [Category.assoc, hhA]
                        exact Over.w vW))).left := by
  obtain ⟨α0, α1, ψ, hα0, hα1, hψ, _, _, _, F, _, hF⟩ :=
    invariant_intersection_affine_descent r V D U hI hqc hEinv
  rw [hα0, hα1] at hψ
  let d := Scheme.invariantIntersectionOverlap r V D
  let S := pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ W
  let T := pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) ⁻¹ᵁ W
  have hd : IsIso d := descent_overlap_iso r V D
  have hST : S = d ⁻¹ᵁ T := by
    change _ = (d ≫ pullback.snd _ _) ⁻¹ᵁ W
    simpa only [d, Scheme.invariantIntersectionOverlap, pullback.lift_snd] using hWinv
  obtain ⟨k, hk⟩ := restrict_iso d S T hST
  have hkres : k.hom = d.resLE T S (le_of_eq hST) := by
    apply (cancel_mono T.ι).mp
    rw [hk, Scheme.Hom.resLE_comp_ι]
  have heq : Scheme.intersectionOpenRightMap r (V.hom ≫ Spec.map r) U W hW ≫
      Spec.map ψ.hom = k.hom ≫
        Scheme.intersectionOpenLeftMap r (V.hom ≫ Spec.map r) U W hW := by
    unfold Scheme.intersectionOpenRightMap Scheme.intersectionOpenLeftMap
    simp only [← Spec.map_comp, Category.assoc]
    rw [hψ, Spec.map_comp]
    have hn := intersection_openAffinization_naturality d
      (fun i ↦ pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) ⁻¹ᵁ U i)
      (fun i ↦ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ U i)
      (by intro x hx i; change (d ≫ pullback.snd (Spec.map r) (V.hom ≫ Spec.map r)) x ∈ U i
          simpa only [d, Scheme.invariantIntersectionOverlap, pullback.lift_snd]
            using (hEinv x).mp hx i)
      T S (fun x i ↦ hW ⟨pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) x.val, x.property⟩ i)
      (fun x i ↦ hW ⟨pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) x.val, x.property⟩ i)
      (le_of_eq hST)
    rw [← Category.assoc, hn, hkres, Category.assoc]
  refine ⟨ψ, hψ, ⟨k, hk, heq⟩, ?_, F, hF, ?_⟩
  · have hr := congrArg (fun q ↦ Set.range (q : S.toScheme ⟶
        Spec (Scheme.intersectionLeftTensor r (V.hom ≫ Spec.map r) U))) heq
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr ((inferInstance : Surjective k.hom).surj), Set.image_univ]
      using hr
  have hopen := intersection_open_isOpenImmersion hV U hI hqc W hW
  let j := Scheme.intersectionOpenAffinization U W hW
  let J := j.opensRange
  let e := j.isoOpensRange
  have hhA : j ≫ (Scheme.intersectionAffineModel V U).hom = W.ι ≫ V.hom :=
    intersection_openAffinization_over V.hom U W hW
  refine ⟨J, e, ?_, rfl, hhA, ?_⟩
  · exact j.isoOpensRange_hom_ι
  intro H a b hab vW
  have hv : vW.left ≫ (W.ι ≫ V.hom) = a := Over.w vW
  let v : Over.mk a ⟶ V := Over.homMk (vW.left ≫ W.ι)
    ((Category.assoc _ _ _).trans hv)
  let y : Over.mk b ⟶ V := D.transport a b hab v
  let g : H ⟶ pullback (V.hom ≫ Spec.map r) (Spec.map r) :=
    pullback.lift (vW.left ≫ W.ι) b (by
      calc
        (vW.left ≫ W.ι) ≫ (V.hom ≫ Spec.map r) =
            (vW.left ≫ (W.ι ≫ V.hom)) ≫ Spec.map r := by simp only [Category.assoc]
        _ = b ≫ Spec.map r := by rw [hv]; exact hab)
  have hgy : g ≫ D.toHom = y.left :=
    (D.transport_left_eq_lift_toHom a b hab v).symm
  have hyW : Set.range y.left ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change y.left x ∈ W
    rw [← hgy]
    have hx : g x ∈ S := by
      change (g ≫ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r)) x ∈ W
      simp only [g, pullback.lift_fst]
      exact (vW.left x).property
    change g x ∈ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ W at hx
    rw [hWinv] at hx
    exact hx
  let t : H ⟶ W.toScheme := IsOpenImmersion.lift W.ι y.left hyW
  have ht : t ≫ W.ι = y.left := IsOpenImmersion.lift_fac _ _ _
  let vW' : Over.mk b ⟶ Over.mk (W.ι ≫ V.hom) := Over.homMk t (by
    change t ≫ (W.ι ≫ V.hom) = b
    rw [← Category.assoc, ht]; exact Over.w y)
  refine ⟨vW', ht, ?_⟩
  let s : H ⟶ S.toScheme := IsOpenImmersion.lift S.ι g (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (g ≫ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r)) x ∈ W
    simp only [g, pullback.lift_fst]
    exact (vW.left x).property)
  have hs : s ≫ S.ι = g := IsOpenImmersion.lift_fac _ _ _
  let m := (pullback.snd (Spec.map r) (V.hom ≫ Spec.map r)).resLE W T le_rfl
  have hm : m ≫ W.ι = T.ι ≫
      pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) := Scheme.Hom.resLE_comp_ι _ _
  have htm : t = s ≫ k.hom ≫ m := by
    apply (cancel_mono W.ι).mp
    rw [ht]
    calc
      y.left = g ≫ D.toHom := hgy.symm
      _ = s ≫ (S.ι ≫ d) ≫ pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) := by
        rw [← hs]
        simp only [Category.assoc, d, Scheme.invariantIntersectionOverlap, pullback.lift_snd]
      _ = s ≫ (k.hom ≫ T.ι) ≫ pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) := by
        rw [hk]
      _ = (s ≫ k.hom ≫ m) ≫ W.ι := by
        simp only [Category.assoc]
        rw [hm]
  let β := Scheme.intersectionAffineOverlapIso r V U
  let ρ := Scheme.intersectionOpenRightMap r (V.hom ≫ Spec.map r) U W hW
  let σ := Scheme.intersectionTensorSwap r (V.hom ≫ Spec.map r) U
  have hσ : IsIso σ := by
    let := r.hom.toAlgebra
    exact (Algebra.TensorProduct.comm R A
      (Scheme.intersectionAlgebraSections (V.hom ≫ Spec.map r) U)).toCommRingCatIso.isIso_hom
  let sym := (pullbackSymmetry (Spec.map r) (V.hom ≫ Spec.map r)).hom
  let l := sym.resLE S T (by
    intro x hx
    change (sym ≫ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r)) x ∈ W
    rw [pullbackSymmetry_hom_comp_fst]
    exact hx)
  have hlm : l ≫ (pullback.fst (V.hom ≫ Spec.map r) (Spec.map r)).resLE W S le_rfl = m := by
    apply (cancel_mono W.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    simp only [sym, pullbackSymmetry_hom_comp_fst]
    exact (Scheme.Hom.resLE_comp_ι _ _).symm
  have hcoord : ρ ≫ β.inv ≫ F.toHom = k.hom ≫ m ≫ j := by
    have h := congrArg (fun q ↦ ρ ≫ β.inv ≫ q) hF
    have he : ρ ≫ Spec.map ψ.hom =
        k.hom ≫ l ≫ ρ ≫ Spec.map σ := by
      simpa only [intersection_left_naturality, Category.assoc] using heq
    change ρ ≫ β.inv ≫
      Scheme.invariantIntersectionOverlap r (Scheme.intersectionAffineModel V U) F ≫
      (pullbackSymmetry (Spec.map r)
        ((Scheme.intersectionAffineModel V U).hom ≫ Spec.map r)).hom ≫ β.hom ≫ Spec.map σ =
      ρ ≫ β.inv ≫ β.hom ≫ Spec.map ψ.hom at h
    rw [Iso.inv_hom_id_assoc, he] at h
    have h' : ρ ≫ β.inv ≫
        Scheme.invariantIntersectionOverlap r (Scheme.intersectionAffineModel V U) F ≫
        (pullbackSymmetry (Spec.map r)
          ((Scheme.intersectionAffineModel V U).hom ≫ Spec.map r)).hom ≫ β.hom =
        k.hom ≫ l ≫ ρ := by
      apply (cancel_mono (Spec.map σ)).mp
      simpa only [Category.assoc] using h
    have h'' := congrArg (fun q ↦ q ≫ β.inv ≫ pullback.fst _ _) h'
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      pullbackSymmetry_hom_comp_fst, Scheme.invariantIntersectionOverlap,
      pullback.lift_snd] at h''
    rw [intersection_right_coordinates, ← Category.assoc l, hlm] at h''
    exact h''
  have hsρ : s ≫ ρ ≫ β.inv = pullback.lift (vW.left ≫ j) b (by
      calc
        (vW.left ≫ j) ≫ ((Scheme.intersectionAffineModel V U).hom ≫ Spec.map r) =
            (vW.left ≫ (j ≫ (Scheme.intersectionAffineModel V U).hom)) ≫ Spec.map r := by
          simp only [Category.assoc]
        _ = b ≫ Spec.map r := by rw [hhA, hv]; exact hab) := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [intersection_right_coordinates r V U W hW]
      rw [← Category.assoc]
      have hsf : s ≫ (pullback.fst (V.hom ≫ Spec.map r) (Spec.map r)).resLE W S le_rfl =
          vW.left := by
        apply (cancel_mono W.ι).mp
        rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hs]
        simp only [g, pullback.lift_fst]
      rw [hsf, pullback.lift_fst]
    · simp only [Category.assoc]
      rw [intersection_right_coordinates_snd r V U W hW, pullback.lift_snd]
      rw [← Category.assoc, hs]
      simp only [g, pullback.lift_snd]
  change t ≫ j = _
  rw [F.transport_left_eq_lift_toHom]
  change t ≫ j = pullback.lift (vW.left ≫ j) b _ ≫ F.toHom
  rw [← hsρ]
  simp only [Category.assoc]
  rw [hcoord, htm]
  simp only [Category.assoc]

end AlgebraicGeometry
