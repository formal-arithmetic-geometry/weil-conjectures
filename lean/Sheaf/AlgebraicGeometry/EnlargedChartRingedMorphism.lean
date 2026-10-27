/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Paper.SequenceSiteCompletionProjection
public import Sheaf.CategoryTheory.CochainCoefficientUniverseTransport
import all Sheaf.CategoryTheory.RingedPullbackPresentationOnSites
import Sheaf.AlgebraicGeometry.EnlargedSiteSchemeDensity
import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Chart-normalized ringed morphisms on enlarged étale sites

Source: Stacks Project, Properties of Spaces, Tags 03G2(1),(3), 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism).

The rings and their normalization isomorphisms are arbitrary. The ringed-topos datum
uses sectionwise ULift in the sheaf universe; the structural map is specified before
this faithful size transport, on the original rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Forget commutativity without changing any section or restriction.
Source: Stacks, Tag 03G8
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
abbrev chartNormalizedRing (X : AlgebraicSpace S)
    (R : Sheaf X.enlargedEtaleTopology CommRingCat.{u}) :
    Sheaf X.enlargedEtaleTopology RingCat.{u} :=
  (sheafCompose X.enlargedEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- The same ring sheaf in the ambient sheaf universe, with sectionwise ULift data.
Source: Stacks, Tags 03G8 and 03DA
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
abbrev chartNormalizedLiftedRing (X : AlgebraicSpace S)
    (R : Sheaf X.enlargedEtaleTopology CommRingCat.{u}) :
    Sheaf X.enlargedEtaleTopology RingCat.{max (u + 1) w} :=
  (sheafCompose X.enlargedEtaleTopology
    (forget₂ CommRingCat.{max (u + 1) w} RingCat.{max (u + 1) w})).obj
    (SheafOfModules.CochainUniverseTransport.ring.{u + 1, u + 1, u, u + 1, w} R)

/-- The lifted underlying direct-image ring map. Precomposition and coefficient transport
commute definitionally, so this retains the actual map rather than choosing a comparison.
Source: Stacks, Tags 03G8 and 00YV
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
def chartNormalizedUnderlyingMap (f : X ⟶ Y)
    {RX : Sheaf X.enlargedEtaleTopology CommRingCat.{u}}
    {RY : Sheaf Y.enlargedEtaleTopology CommRingCat.{u}}
    (α : RY ⟶ (enlargedDirectImage f CommRingCat.{u}).obj RX) :
    (sheafCompose Y.enlargedEtaleTopology (forget RingCat.{max (u + 1) w})).obj
        (chartNormalizedLiftedRing.{u, w} Y RY) ⟶
      (enlargedDirectImage f (Type (max (u + 1) w))).obj
        ((sheafCompose X.enlargedEtaleTopology (forget RingCat.{max (u + 1) w})).obj
          (chartNormalizedLiftedRing.{u, w} X RX)) :=
  (sheafCompose Y.enlargedEtaleTopology (forget RingCat.{max (u + 1) w})).map
    ((sheafCompose Y.enlargedEtaleTopology
      (forget₂ CommRingCat.{max (u + 1) w} RingCat.{max (u + 1) w})).map
      ((sheafCompose Y.enlargedEtaleTopology
        (SheafOfModules.CochainUniverseTransport.ringFunctor.{u, u + 1, w})).map α))

/-- The all-scheme-chart formula for the specified normalizations. In particular it
applies to every surjective representable étale atlas of the fibre product. Quantifying
all commuting chart triangles is precisely the f-map formulation in Stacks 03G8.
Source: Stacks, Tag 03G8, proof
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
def IsChartNormalizedRingMap (f : X ⟶ Y)
    (RX : Sheaf X.enlargedEtaleTopology CommRingCat.{u})
    (RY : Sheaf Y.enlargedEtaleTopology CommRingCat.{u})
    (eX : (enlargedRestriction X RingCat.{u}).obj (chartNormalizedRing X RX) ≅
      X.structureSheaf)
    (eY : (enlargedRestriction Y RingCat.{u}).obj (chartNormalizedRing Y RY) ≅
      Y.structureSheaf)
    (α : RY ⟶ (enlargedDirectImage f CommRingCat.{u}).obj RX) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (q : U.obj.left ⟶ V.obj.left)
    (hq : yoneda.map q ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom),
    eY.inv.hom.app (op V) ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        (α.hom.app (op ((enlargedSchemeInclusion Y).obj V))) ≫
      (chartNormalizedRing X RX).obj.map (enlargedChartLift f U V q hq).op ≫
      eX.hom.hom.app (op U) =
        (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map q.left.op)

/-- Lift the specified normalization through fully faithful ring-sheaf restriction.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private def normalizedRingIso (A : AlgebraicSpace S)
    (R : Sheaf A.enlargedEtaleTopology CommRingCat.{u})
    (e : (enlargedRestriction A RingCat.{u}).obj (chartNormalizedRing A R) ≅
      A.structureSheaf) : chartNormalizedRing A R ≅ A.enlargedStructureSheaf :=
  (enlargedRingEquivalence A).fullyFaithfulFunctor.preimageIso
    (e ≪≫ (enlargedStructureRestriction A).symm)

/-- The lifted normalization agrees with its specified map on scheme charts.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private theorem normalizedRingIso_hom (A : AlgebraicSpace S)
    (R : Sheaf A.enlargedEtaleTopology CommRingCat.{u})
    (e : (enlargedRestriction A RingCat.{u}).obj (chartNormalizedRing A R) ≅
      A.structureSheaf) (U : A.EtaleSite) :
    (normalizedRingIso A R e).hom.hom.app (op ((enlargedSchemeInclusion A).obj U)) ≫
      (enlargedStructureRestriction A).hom.hom.app (op U) = e.hom.hom.app (op U) := by
  have h : (enlargedRestriction A RingCat.{u}).map (normalizedRingIso A R e).hom ≫
      (enlargedStructureRestriction A).hom = e.hom := by
    change (enlargedRingEquivalence A).functor.map
      ((enlargedRingEquivalence A).fullyFaithfulFunctor.preimage
        (e ≪≫ (enlargedStructureRestriction A).symm).hom) ≫ _ = _
    rw [(enlargedRingEquivalence A).fullyFaithfulFunctor.map_preimage]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  exact congrArg (fun k ↦ k.hom.app (op U)) h

/-- The inverse lifted normalization agrees on scheme charts.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private theorem normalizedRingIso_inv (A : AlgebraicSpace S)
    (R : Sheaf A.enlargedEtaleTopology CommRingCat.{u})
    (e : (enlargedRestriction A RingCat.{u}).obj (chartNormalizedRing A R) ≅
      A.structureSheaf) (U : A.EtaleSite) :
    (enlargedStructureRestriction A).inv.hom.app (op U) ≫
      (normalizedRingIso A R e).inv.hom.app (op ((enlargedSchemeInclusion A).obj U)) =
        e.inv.hom.app (op U) := by
  have h : (enlargedStructureRestriction A).inv ≫
      (enlargedRestriction A RingCat.{u}).map (normalizedRingIso A R e).inv = e.inv := by
    change _ ≫ (enlargedRingEquivalence A).functor.map
      ((enlargedRingEquivalence A).fullyFaithfulFunctor.preimage
        (e ≪≫ (enlargedStructureRestriction A).symm).inv) = _
    rw [(enlargedRingEquivalence A).fullyFaithfulFunctor.map_preimage]
    simp only [Iso.trans_inv, Iso.symm_inv, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  exact congrArg (fun k ↦ k.hom.app (op U)) h

/-- Conjugation by the lifted normalizations identifies the two chart formulas.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private theorem normalized_ring_map_iff (f : X ⟶ Y)
    (RX : Sheaf X.enlargedEtaleTopology CommRingCat.{u})
    (RY : Sheaf Y.enlargedEtaleTopology CommRingCat.{u})
    (eX : (enlargedRestriction X RingCat.{u}).obj (chartNormalizedRing X RX) ≅
      X.structureSheaf)
    (eY : (enlargedRestriction Y RingCat.{u}).obj (chartNormalizedRing Y RY) ≅
      Y.structureSheaf)
    (α : RY ⟶ (enlargedDirectImage f CommRingCat.{u}).obj RX) :
    IsChartNormalizedRingMap f RX RY eX eY α ↔
      IsEnlargedStructuralMap f
        ((normalizedRingIso Y RY eY).inv ≫
          (sheafCompose Y.enlargedEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).map α ≫
          (enlargedDirectImage f RingCat.{u}).map (normalizedRingIso X RX eX).hom) := by
  have heq (U : X.EtaleSite) (V : Y.EtaleSite) (q : U.obj.left ⟶ V.obj.left)
      (hq : yoneda.map q ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom) :
      (enlargedStructureRestriction Y).inv.hom.app (op V) ≫
        ((normalizedRingIso Y RY eY).inv ≫
          (sheafCompose Y.enlargedEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).map α ≫
          (enlargedDirectImage f RingCat.{u}).map (normalizedRingIso X RX eX).hom).hom.app
            (op ((enlargedSchemeInclusion Y).obj V)) ≫
        X.enlargedStructureSheaf.obj.map (enlargedChartLift f U V q hq).op ≫
        (enlargedStructureRestriction X).hom.hom.app (op U) =
      eY.inv.hom.app (op V) ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map
          (α.hom.app (op ((enlargedSchemeInclusion Y).obj V))) ≫
        (chartNormalizedRing X RX).obj.map (enlargedChartLift f U V q hq).op ≫
        eX.hom.hom.app (op U) := by
    change (enlargedStructureRestriction Y).inv.hom.app (op V) ≫
      (normalizedRingIso Y RY eY).inv.hom.app _ ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map (α.hom.app _) ≫
      (normalizedRingIso X RX eX).hom.hom.app _ ≫
      X.enlargedStructureSheaf.obj.map (enlargedChartLift f U V q hq).op ≫
      (enlargedStructureRestriction X).hom.hom.app (op U) = _
    dsimp [enlargedRestriction, Functor.sheafPushforwardContinuous]
    rw [← (normalizedRingIso X RX eX).hom.hom.naturality_assoc]
    simp only [← Category.assoc, normalizedRingIso_inv]
    simp only [Category.assoc, normalizedRingIso_hom]
  constructor
  · intro h U V q hq
    rw [heq]
    exact h U V q hq
  · intro h U V q hq
    rw [← heq]
    exact h U V q hq

/-- Transport the canonical structural map and its uniqueness to arbitrary normalizations.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private theorem chart_normalized_existsUnique (f : X ⟶ Y)
    (RX : Sheaf X.enlargedEtaleTopology CommRingCat.{u})
    (RY : Sheaf Y.enlargedEtaleTopology CommRingCat.{u})
    (eX : (enlargedRestriction X RingCat.{u}).obj (chartNormalizedRing X RX) ≅
      X.structureSheaf)
    (eY : (enlargedRestriction Y RingCat.{u}).obj (chartNormalizedRing Y RY) ≅
      Y.structureSheaf) :
    ∃! α : RY ⟶ (enlargedDirectImage f CommRingCat.{u}).obj RX,
      IsChartNormalizedRingMap f RX RY eX eY α := by
  let F := sheafCompose Y.enlargedEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})
  let dX := normalizedRingIso X RX eX
  let dY := normalizedRingIso Y RY eY
  let D := enlargedDirectImage f RingCat.{u}
  obtain ⟨r, hr, hu⟩ := enlargedStructuralMap_existsUnique f
  let α : RY ⟶ (enlargedDirectImage f CommRingCat.{u}).obj RX :=
    F.preimage (dY.hom ≫ r ≫ D.map dX.inv)
  have hα : dY.inv ≫ F.map α ≫ D.map dX.hom = r := by
    rw [show F.map α = dY.hom ≫ r ≫ D.map dX.inv from F.map_preimage _]
    simp only [← Category.assoc]
    rw [dY.inv_hom_id, Category.id_comp, Category.assoc, ← D.map_comp,
      dX.inv_hom_id, D.map_id, Category.comp_id]
  refine ⟨α, (normalized_ring_map_iff f RX RY eX eY α).mpr ?_, ?_⟩
  · change IsEnlargedStructuralMap f (dY.inv ≫ F.map α ≫ D.map dX.hom)
    rw [hα]
    exact hr
  · intro β hβ
    apply F.map_injective
    have hβ' := hu _ ((normalized_ring_map_iff f RX RY eX eY β).mp hβ)
    change dY.inv ≫ F.map β ≫ D.map dX.hom = r at hβ'
    have h := congrArg (fun k ↦ dY.hom ≫ k ≫ D.map dX.inv) (hβ'.trans hα.symm)
    simp only [← Category.assoc, dY.hom_inv_id_assoc] at h
    simp only [Category.assoc, ← D.map_comp] at h
    simp only [dX.hom_inv_id, D.map_id] at h
    change F.map β ≫ 𝟙 _ = F.map α ≫ 𝟙 _ at h
    simpa only [Category.comp_id] using h

/-- The fully faithful inclusion into the slice category of ambient sheaves.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private abbrev enlargedOver (A : AlgebraicSpace S) : A.EnlargedEtaleSite ⥤ Over A.obj :=
  ObjectProperty.ι _ ⋙ Over.post (ObjectProperty.ι _)

/-- Density identifies terminal objects and pullbacks with their ambient sheaf limits.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private theorem enlargedOver_preserves (A : AlgebraicSpace S) :
    PreservesFiniteLimits (enlargedOver A) := by
  have density := enlargedSite_scheme_density.{u, 0, 0} A
  let _ : HasFiniteLimits A.EnlargedEtaleSite := density.2.2.2.1.some
  obtain ⟨T, hT, ht⟩ := density.2.1
  have hterm : IsTerminal ((enlargedOver A).obj T) := by
    change IsTerminal ((Over.post (ObjectProperty.ι _)).obj T.obj)
    rw [hT]
    exact Over.mkIdTerminal
  let _ : PreservesLimit (Functor.empty.{0} A.EnlargedEtaleSite) (enlargedOver A) :=
    preservesLimit_of_preserves_limit_cone ht.some
      ((isLimitMapConeEmptyConeEquiv (enlargedOver A) T).symm hterm)
  let _ : PreservesLimitsOfShape (Discrete.{0} PEmpty) (enlargedOver A) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  let _ : PreservesLimitsOfShape WalkingCospan (enlargedOver A) := by
    apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
    intro U V W a b _
    obtain ⟨P, p, q, hp, hs⟩ := density.2.2.1 U V W a b
    refine ⟨P, p, q, hp, ?_⟩
    exact IsPullback.of_map_of_faithful (Over.forget A.obj) hs
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- Ambient slice pullback preserves limits, which the fully faithful inclusion reflects.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private theorem enlargedBaseChange_preserves (f : X ⟶ Y) :
    PreservesFiniteLimits (enlargedBaseChange f) := by
  let _ := enlargedOver_preserves Y
  let e : enlargedBaseChange f ⋙ enlargedOver X ≅
      enlargedOver Y ⋙ Over.pullback f.hom :=
    NatIso.ofComponents (fun T ↦ Over.isoMk
      (pullbackSymmetry f.hom T.obj.hom.hom) (by
        change (pullbackSymmetry f.hom T.obj.hom.hom).hom ≫
          Limits.pullback.snd T.obj.hom.hom f.hom =
            Limits.pullback.fst f.hom T.obj.hom.hom
        simp)) (by
        intro T U a
        apply Over.OverMorphism.ext
        dsimp [enlargedOver, Over.post, enlargedBaseChange, Over.pullback]
        apply Limits.pullback.hom_ext <;> simp [Category.assoc])
  let _ : PreservesFiniteLimits (enlargedBaseChange f ⋙ enlargedOver X) :=
    preservesFiniteLimits_of_natIso e.symm
  let _ : (enlargedOver X).Full :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (Functor.FullyFaithful.over X (ObjectProperty.ι IsAlgebraicSpace)
        (ObjectProperty.fullyFaithfulι IsAlgebraicSpace))).full
  let _ : (enlargedOver X).Faithful :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (Functor.FullyFaithful.over X (ObjectProperty.ι IsAlgebraicSpace)
        (ObjectProperty.fullyFaithfulι IsAlgebraicSpace))).faithful
  let _ : ReflectsLimitsOfSize.{0, 0} (enlargedOver X) :=
    fullyFaithful_reflectsLimits _
  exact preservesFiniteLimits_of_reflects_of_preserves (enlargedBaseChange f) (enlargedOver X)

/-- A base-changed arrow is a pullback of the original arrow in ambient sheaves.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private theorem baseChange_arrow_pullback (f : X ⟶ Y)
    {U V : Y.EnlargedEtaleSite} (a : U ⟶ V) :
    IsPullback ((enlargedBaseChange f).map a).hom.left.hom
      (pullback.snd f.hom U.obj.hom.hom)
      (pullback.snd f.hom V.obj.hom.hom) a.hom.left.hom := by
  have h : a.hom.left.hom ≫ V.obj.hom.hom = U.obj.hom.hom :=
    congrArg InducedCategory.Hom.hom (Over.w a.hom)
  have hfst : ((enlargedBaseChange f).map a).hom.left.hom ≫
      Limits.pullback.fst f.hom V.obj.hom.hom =
        Limits.pullback.fst f.hom U.obj.hom.hom := by
    simp [enlargedBaseChange]
  apply IsPullback.of_right (h₁₂ := Limits.pullback.fst f.hom V.obj.hom.hom)
    (h₂₂ := V.obj.hom.hom) (v₁₃ := f.hom)
  · rw [hfst, h]
    exact IsPullback.of_hasPullback f.hom U.obj.hom.hom
  · simp [enlargedBaseChange]
  · exact IsPullback.of_hasPullback f.hom V.obj.hom.hom

/-- Lift a covering witness across the ambient sheaf pullback after a field extension.
Source: Stacks, Tags 03G2, 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism). -/
private theorem enlargedBaseChange_covers (f : X ⟶ Y)
    (V : Y.EnlargedEtaleSite) (P : Presieve V)
    (hP : P ∈ Y.enlargedEtalePrecoverage V) :
    P.map (enlargedBaseChange f) ∈
      X.enlargedEtalePrecoverage ((enlargedBaseChange f).obj V) := by
  refine ⟨?_, ?_⟩
  · intro U a ha
    exact (chartwise_etale_permanence.{u, 0, 0} (S := S)).2.2.2.2.1 _ _ _ _ _ a.hom.left
      U.property ((enlargedBaseChange f).obj V).property (Over.w a.hom)
  · intro K _ s x
    obtain ⟨i, L, hL, e, y, hy⟩ := hP.2 K s ((pullback.snd f.hom V.obj.hom.hom).hom.app _ x)
    let a := i.1.2
    have sq := ((sheafToPresheaf _ _).map_isPullback
      (baseChange_arrow_pullback f a)).app
        (op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))
    let t : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ Over.mk s :=
      Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
    have heq : (pullback.snd f.hom V.obj.hom.hom).hom.app _
        (((enlargedBaseChange f).obj V).obj.left.obj.obj.map t.op x) =
          a.hom.left.hom.hom.app _ y := by
      rw [hy]
      exact ConcreteCategory.congr_hom
        ((pullback.snd f.hom V.obj.hom.hom).hom.naturality t.op) x
    obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback sq _ _ heq
    exact ⟨⟨⟨_, (enlargedBaseChange f).map a⟩, Presieve.map_map i.2⟩,
      L, hL, e, z, hz⟩

/-- Base change gives the geometric morphism and its unique chart-normalized ring map
for arbitrary normalized extensions of the two structure sheaves.
Source: Stacks, Tags 03G2(1),(3), 03G8 and 03H7
(blueprint: lem-trf-space-enlarged-chart-ringed-morphism).

Proof: Identify the enlarged site with a full subcategory of the ambient sheaf slice.
The terminal-object and pullback clauses of scheme density prove that this inclusion
preserves finite limits. Base change agrees, up to pullback symmetry, with the ambient
slice pullback functor, so it preserves finite limits. Covering preservation follows
by lifting field-valued sections across its sheaf pullback squares; chartwise étale
permanence supplies étaleness. Continuity is the existing enlarged-site theorem.

Lift the specified normalization isomorphisms through fully faithful ring restriction.
Conjugation identifies the stated chart formula with IsEnlargedStructuralMap. Transport
the canonical unique structural map through these isomorphisms, and lift back through
the fully faithful forgetful functor from commutative rings to rings. This proves
existence and uniqueness for the arbitrary normalized extensions.

The flat-functor theorem makes the actual sheaf pullback left exact. After the existing
sectionwise coefficient ULift, the continuous ringed-topos construction transposes this
very ring map under the sheaf adjunction. Its structural transpose is the specified
underlying map by the inverse laws of homEquiv. Compose the geometric adjunction with
the two scheme-restriction equivalences to obtain the small-site geometric morphism. -/
theorem enlarged_chart_ringed_morphism (f : X ⟶ Y)
    (RX : Sheaf X.enlargedEtaleTopology CommRingCat.{u})
    (RY : Sheaf Y.enlargedEtaleTopology CommRingCat.{u})
    (eX : (enlargedRestriction X RingCat.{u}).obj (chartNormalizedRing X RX) ≅
      X.structureSheaf)
    (eY : (enlargedRestriction Y RingCat.{u}).obj (chartNormalizedRing Y RY) ≅
      Y.structureSheaf) :
    PreservesFiniteLimits (enlargedBaseChange f) ∧
    (∀ (V : Y.EnlargedEtaleSite) (P : Presieve V),
      P ∈ Y.enlargedEtalePrecoverage V →
        P.map (enlargedBaseChange f) ∈
          X.enlargedEtalePrecoverage ((enlargedBaseChange f).obj V)) ∧
    (enlargedBaseChange f).IsContinuous Y.enlargedEtaleTopology X.enlargedEtaleTopology ∧
    (∃! α : RY ⟶ (enlargedDirectImage f CommRingCat.{u}).obj RX,
      IsChartNormalizedRingMap f RX RY eX eY α) ∧
    (∀ α : RY ⟶ (enlargedDirectImage f CommRingCat.{u}).obj RX,
      IsChartNormalizedRingMap f RX RY eX eY α →
      ∃ (g : RingedToposMorphismOfUniverses
          (chartNormalizedLiftedRing.{u, w} X RX) (chartNormalizedLiftedRing.{u, w} Y RY))
        (hd : g.direct = enlargedDirectImage f (Type (max (u + 1) w))),
        g.adj.homEquiv _ _ g.ringMap ≫
          eqToHom (congrArg (fun F ↦ F.obj
            ((sheafCompose X.enlargedEtaleTopology (forget RingCat.{max (u + 1) w})).obj
              (chartNormalizedLiftedRing.{u, w} X RX))) hd) =
          chartNormalizedUnderlyingMap.{u, w} f α ∧
        ∃ h : GeometricMorphism (Sheaf X.etaleTopology (Type (max (u + 1) w)))
            (Sheaf Y.etaleTopology (Type (max (u + 1) w))),
          h.direct = (enlargedSetEquivalence X).inverse ⋙ g.direct ⋙
            (enlargedSetEquivalence Y).functor) := by
  refine ⟨?_, ?_, enlargedBaseChange_continuous f,
    chart_normalized_existsUnique f RX RY eX eY, ?_⟩
  · exact enlargedBaseChange_preserves f
  · exact enlargedBaseChange_covers f
  · intro α _hα
    let _ : HasFiniteLimits Y.EnlargedEtaleSite :=
      (enlargedSite_scheme_density.{u, 0, 0} Y).2.2.2.1.some
    let _ := enlargedBaseChange_preserves f
    let _ : RepresentablyFlat (enlargedBaseChange f) :=
      flat_of_preservesFiniteLimits _
    have : AB5OfSize.{u + 1, u + 1} (Type (max (u + 1) w)) :=
      AB5OfSize_shrink.{u + 1, u + 1, max (u + 1) w, max (u + 1) w} _
    let L := (enlargedBaseChange f).sheafPullback (Type (max (u + 1) w))
      Y.enlargedEtaleTopology X.enlargedEtaleTopology
    let adj := (enlargedBaseChange f).sheafAdjunctionContinuous
      (Type (max (u + 1) w)) Y.enlargedEtaleTopology X.enlargedEtaleTopology
    let _ : PreservesFiniteLimits L := by
      dsimp [L]
      infer_instance
    let φ := (sheafCompose Y.enlargedEtaleTopology
      (SheafOfModules.CochainUniverseTransport.ringFunctor.{u, u + 1, w})).map α
    let g := SheafOfModules.RingedPresentationOnSites.siteContinuousRingedTopos
      (enlargedBaseChange f) L adj
      (SheafOfModules.CochainUniverseTransport.ring.{u + 1, u + 1, u, u + 1, w} RX)
      (SheafOfModules.CochainUniverseTransport.ring.{u + 1, u + 1, u, u + 1, w} RY) φ
    refine ⟨g, rfl, ?_, ?_⟩
    · change adj.homEquiv _ _ ((adj.homEquiv _ _).symm _) ≫ 𝟙 _ = _
      rw [Equiv.apply_symm_apply, Category.comp_id]
      rfl
    · let eX := enlargedSetEquivalence.{u, w} X
      let eY := enlargedSetEquivalence.{u, w} Y
      let h : GeometricMorphism (Sheaf X.etaleTopology (Type (max (u + 1) w)))
          (Sheaf Y.etaleTopology (Type (max (u + 1) w))) := {
        inverse := eY.inverse ⋙ g.inverse ⋙ eX.functor
        direct := eX.inverse ⋙ g.direct ⋙ eY.functor
        adj := eY.symm.toAdjunction.comp (g.adj.comp eX.toAdjunction)
        leftExact := by
          have := g.leftExact
          infer_instance }
      exact ⟨h, rfl⟩

end AlgebraicGeometry.AlgebraicSpace
