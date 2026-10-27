/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.EtalePresentedRecoveryData
import Sheaf.AlgebraicGeometry.EtalePresentedLocalCokernels
import Sheaf.AlgebraicGeometry.EtalePresentedDescentGluing

/-! # Effective recovery from étale presentations

Source: Stacks Project, Descent, Tag 03DX, proof of (2)
(blueprint: lem-trf-etale-presented-module-effective-recovery).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- The complete effective recovery datum for a specified family of free presentations.
The overlap isomorphisms are tested on arbitrary étale objects W over T with maps to
both charts. Taking W to be a pairwise fibre product gives phi_ij; taking W to be a
triple fibre product gives the stated cocycle, with all composition transports explicit.
`localMap` characterizes their images on every étale object A over W, so it records
exactly the restrictions of b_j inverse composed with b_i, and their unique lifts.

Source: Stacks Project, Descent, Tag 03DX, proof of (2)
(blueprint: lem-trf-etale-presented-module-effective-recovery). -/
structure EtalePresentedRecovery
    (c : ∀ X : Scheme.{u}, ZariskiEtaleModuleContext X)
    (T : Scheme.{u}) (G : SmallEtaleModules T) (I : Type w) (U : I → T.Etale)
    (K J : I → Type u)
    (d : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (K i) ⟶
      SheafOfModules.free (J i))
    (q : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (J i) ⟶
      (presentedEtaleRestriction (U i)).obj G) where
  /-- Canonical free comparisons, normalized by their adjoints on free generators. -/
  freeIso : ∀ (i : I) (A : Type u),
    (c (U i).left).extension.obj
      (SheafOfModules.free (R := (U i).left.ringCatSheaf) A) ≅
        SheafOfModules.free (R := smallEtaleModuleRing (U i).left) A
  freeIso_hom : ∀ (i : I) (A : Type u),
    (freeIso i A).hom = presentedEtaleFreeMap (c (U i).left) A
  /-- The unique lifted presentation matrices. -/
  lift : ∀ i, SheafOfModules.free (R := (U i).left.ringCatSheaf) (K i) ⟶
    SheafOfModules.free (J i)
  lift_image : ∀ i, (c (U i).left).extension.map (lift i) ≫ (freeIso i (J i)).hom =
    (freeIso i (K i)).hom ≫ d i
  lift_unique : ∀ i (h : SheafOfModules.free (R := (U i).left.ringCatSheaf) (K i) ⟶
      SheafOfModules.free (J i)),
    (c (U i).left).extension.map h ≫ (freeIso i (J i)).hom =
      (freeIso i (K i)).hom ≫ d i → h = lift i
  /-- The cokernel object and projection, with their full universal property. -/
  localModule : ∀ i, (U i).left.Modules
  localQuotient : ∀ i, SheafOfModules.free (R := (U i).left.ringCatSheaf) (J i) ⟶
    localModule i
  localZero : ∀ i, lift i ≫ localQuotient i = 0
  localCokernel : ∀ i, Nonempty (IsColimit (CokernelCofork.ofπ
    (localQuotient i) (localZero i)))
  localQC : ∀ i, (localModule i).IsQuasicoherent
  localIso : ∀ i, (c (U i).left).extension.obj (localModule i) ≅
    (presentedEtaleRestriction (U i)).obj G
  local_projection : ∀ i,
    (c (U i).left).extension.map (localQuotient i) ≫ (localIso i).hom =
      (freeIso i (J i)).hom ≫ q i
  /-- Tensor coordinates for the local comparisons, fixed by the unit on opens. -/
  localTensor : ∀ i,
    (SheafOfModules.toSheaf (smallEtaleModuleRing (U i).left)).obj
      ((c (U i).left).extension.obj (localModule i)) ≅
        @etaleTensorSectionsSheaf (U i).left (localModule i) (localQC i)
  local_linear : ∀ (i : I) (A : (U i).left.Etale) (r : Γ(A.left, ⊤))
    (s : ((c (U i).left).extension.obj (localModule i)).val.obj (op A)),
    (localTensor i).hom.hom.app (op A) (r • s) =
      r • (@id (Γ((tensorPullback A.hom).obj (localModule i), ⊤))
        ((localTensor i).hom.hom.app (op A) s))
  local_unit : ∀ (i : I) (W : (U i).left.Opens),
    ((c (U i).left).adjunction.unit.app (localModule i)).app W ≫
      (localTensor i).hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale (U i).left).obj W)) ≫
        (tensorOpenSectionIso (U i).left (localModule i) W).hom = 𝟙 _
  /-- The unique overlap lifts; the two target section groups are canonically the same. -/
  overlap : ∀ (W : T.Etale) (i j : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) [Etale f] [Etale g]
    (_hf : f ≫ (U i).hom = W.hom) (_hg : g ≫ (U j).hom = W.hom),
    (tensorPullback f).obj (localModule i) ≅
      (tensorPullback g).obj (localModule j)
  overlap_image : ∀ (W : T.Etale) (i j : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) [Etale f] [Etale g]
    (hf : f ≫ (U i).hom = W.hom) (hg : g ≫ (U j).hom = W.hom) (A : W.left.Etale),
    ∀ s : Γ((tensorPullback A.hom).obj
      ((tensorPullback f).obj (localModule i)), ⊤),
      @presentedEtaleLocalMap T c G (U j) (localModule j) (localQC j)
        (localTensor j) (localIso j) W g _ hg A
        (((tensorPullback A.hom).map (overlap W i j f g hf hg).hom).app ⊤ s) =
      @presentedEtaleLocalMap T c G (U i) (localModule i) (localQC i)
        (localTensor i) (localIso i) W f _ hf A s
  overlap_unique : ∀ (W : T.Etale) (i j : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) [Etale f] [Etale g]
    (hf : f ≫ (U i).hom = W.hom) (hg : g ≫ (U j).hom = W.hom)
    (p : (tensorPullback f).obj (localModule i) ≅
      (tensorPullback g).obj (localModule j)),
    (∀ (A : W.left.Etale)
      (s : Γ((tensorPullback A.hom).obj ((tensorPullback f).obj (localModule i)), ⊤)),
      @presentedEtaleLocalMap T c G (U j) (localModule j) (localQC j)
        (localTensor j) (localIso j) W g _ hg A
        (((tensorPullback A.hom).map p.hom).app ⊤ s) =
      @presentedEtaleLocalMap T c G (U i) (localModule i) (localQC i)
        (localTensor i) (localIso i) W f _ hf A s) → p = overlap W i j f g hf hg
  cocycle : ∀ (W : T.Etale) (i j k : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) (h : W.left ⟶ (U k).left)
    [Etale f] [Etale g] [Etale h]
    (hf : f ≫ (U i).hom = W.hom) (hg : g ≫ (U j).hom = W.hom)
    (hh : h ≫ (U k).hom = W.hom),
    overlap W i j f g hf hg ≪≫ overlap W j k g h hg hh = overlap W i k f h hf hh
  /-- The effective Zariski module and its specified descent identifications. -/
  globalModule : T.Modules
  globalQC : globalModule.IsQuasicoherent
  chartIso : ∀ i, (tensorPullback (U i).hom).obj globalModule ≅ localModule i
  effective : ∀ (W : T.Etale) (i j : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) [Etale f] [Etale g]
    (hf : f ≫ (U i).hom = W.hom) (hg : g ≫ (U j).hom = W.hom),
    (tensorPullback f).mapIso (chartIso i) ≪≫ overlap W i j f g hf hg =
      presentedTensorOverlap globalModule (U i) (U j) W f g hf hg ≪≫
        (tensorPullback g).mapIso (chartIso j)
  /-- Tensor coordinates for the global module. -/
  globalTensor : (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj
    ((c T).extension.obj globalModule) ≅ @etaleTensorSectionsSheaf T globalModule globalQC
  global_linear : ∀ (A : T.Etale) (r : Γ(A.left, ⊤))
    (s : ((c T).extension.obj globalModule).val.obj (op A)),
    globalTensor.hom.hom.app (op A) (r • s) =
      r • (@id (Γ((tensorPullback A.hom).obj globalModule, ⊤))
        (globalTensor.hom.hom.app (op A) s))
  global_unit : ∀ W : T.Opens,
    ((c T).adjunction.unit.app globalModule).app W ≫
      globalTensor.hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
        (tensorOpenSectionIso T globalModule W).hom = 𝟙 _
  /-- The uniquely glued isomorphism, specified at every object over a cover member. -/
  gluedIso : (c T).extension.obj globalModule ≅ G
  glued_local : ∀ (i : I) (A : (U i).left.Etale),
    globalTensor.inv.hom.app (op (Scheme.Etale.mk (A.hom ≫ (U i).hom))) ≫
      ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map gluedIso.hom).hom.app
        (op (Scheme.Etale.mk (A.hom ≫ (U i).hom))) =
      ((tensorSectionsComp A.hom (U i).hom).inv.app globalModule).app ⊤ ≫
        ((tensorPullback A.hom).map (chartIso i).hom).app ⊤ ≫
          (localTensor i).inv.hom.app (op A) ≫
            ((SheafOfModules.toSheaf (smallEtaleModuleRing (U i).left)).map
              (localIso i).hom).hom.app (op A)
  glued_unique : ∀ b : (c T).extension.obj globalModule ⟶ G,
    (∀ (i : I) (A : (U i).left.Etale),
      b.val.app (op (Scheme.Etale.mk (A.hom ≫ (U i).hom))) =
        gluedIso.hom.val.app (op (Scheme.Etale.mk (A.hom ≫ (U i).hom)))) → b = gluedIso.hom
  /-- Restricting b and composing with the canonical unit identifies F with R G. -/
  restrictionIso : globalModule ≅ (c T).restriction.obj G
  restriction_hom : restrictionIso.hom =
    (c T).adjunction.unit.app globalModule ≫ (c T).restriction.map gluedIso.hom
  restrictionQC : ((c T).restriction.obj G).IsQuasicoherent
  counitIso : IsIso ((c T).adjunction.counit.app G)
  /-- The counit is identity in the ordinary open-section coordinates. -/
  restrictionTensor : (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj
    ((c T).extension.obj ((c T).restriction.obj G)) ≅
      @etaleTensorSectionsSheaf T ((c T).restriction.obj G) restrictionQC
  restriction_linear : ∀ (A : T.Etale) (r : Γ(A.left, ⊤))
    (s : ((c T).extension.obj ((c T).restriction.obj G)).val.obj (op A)),
    restrictionTensor.hom.hom.app (op A) (r • s) =
      r • (@id (Γ((tensorPullback A.hom).obj ((c T).restriction.obj G), ⊤))
        (restrictionTensor.hom.hom.app (op A) s))
  restriction_unit : ∀ W : T.Opens,
    ((c T).adjunction.unit.app ((c T).restriction.obj G)).app W ≫
      restrictionTensor.hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
        (tensorOpenSectionIso T ((c T).restriction.obj G) W).hom = 𝟙 _
  counit_open : ∀ W : T.Opens,
    (tensorOpenSectionIso T ((c T).restriction.obj G) W).inv ≫
      restrictionTensor.inv.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
        ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
          ((c T).adjunction.counit.app G)).hom.app
            (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) = 𝟙 _

private theorem presentedUnit_isIso {T : Scheme.{u}}
    (c : ZariskiEtaleModuleContext T) (F : T.Modules) [F.IsQuasicoherent]
    (e : (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj (c.extension.obj F) ≅
      etaleTensorSectionsSheaf F)
    (h : ∀ W : T.Opens, (c.adjunction.unit.app F).app W ≫
      e.hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
        (tensorOpenSectionIso T F W).hom = 𝟙 _) :
    IsIso (c.adjunction.unit.app F) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro W
  exact isIso_of_comp_hom_eq_id
    (e.hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
      (tensorOpenSectionIso T F W).hom) (h W)

private theorem presentedRestrictionCoordinates
    (c : ∀ X : Scheme.{u}, ZariskiEtaleModuleContext X)
    (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent] :
    ∃ e : (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj ((c T).extension.obj F) ≅
        etaleTensorSectionsSheaf F,
      (∀ (A : T.Etale) (r : Γ(A.left, ⊤))
          (s : ((c T).extension.obj F).val.obj (op A)),
        e.hom.hom.app (op A) (r • s) =
          r • (@id (Γ((tensorPullback A.hom).obj F, ⊤))
            (e.hom.hom.app (op A) s))) ∧
      (∀ W : T.Opens, ((c T).adjunction.unit.app F).app W ≫
        e.hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
          (tensorOpenSectionIso T F W).hom = 𝟙 _) := by
  obtain ⟨c', _, _, _, _, e, hlin, _, hunit, _⟩ :=
    etaleExtension_free_presentations_hom.{u, u, u}
  have hc : c' = c := by
    funext X
    cases c' X
    cases c X
    rfl
  subst c'
  exact ⟨e T F, hlin T F, hunit T F⟩

/-- Effective recovery of an étale module from the specified local free presentations.
Source: Stacks Project, Descent, Tag 03DX, proof of (2)
(blueprint: lem-trf-etale-presented-module-effective-recovery).

Proof, following the eight DAG steps:
1. The structure module is quasi-coherent by the rank-one affine tilde calculation
   (lem-weil-pbc-spec-tilde-free-module). Coproduct closure makes both free terms
   quasi-coherent (lem-weil-pbc-quasi-coherent-module-coproduct-closure).
2. Tensor extension preserves free modules and cokernels, and is fully faithful on
   quasi-coherent modules (lem-trf-etale-extension-free-presentations-hom). Lift each
   d uniquely to h. Its cokernel is quasi-coherent by
   lem-weil-pbc-quasi-coherent-module-cokernel-closure; uniqueness of cokernels gives
   localIso, compatible with q.
3. On overlaps tensor pullback preserves quasi-coherence
   (lem-weil-pbc-module-pullback-quasi-coherent). Restriction compatibility and full
   faithfulness uniquely lift localIso_j inverse composed with localIso_i. Lifting
   the inverse and applying faithfulness proves these lifts invertible.
4. On a triple product, the images of the two composites coincide. Faithfulness
   gives the cocycle. On the small diagonal the resulting invertible idempotent
   is the identity, so the descent datum is normalized.
5. The étale family is fpqc without requiring its members quasi-compact
   (lem-weil-pbc-fpqc-finer-than-etale). Effective fpqc descent (lem-pc-fpqc-descent)
   gives globalModule, globalQC and chartIso inducing these overlap maps.
6. The local extension maps agree on overlaps. Glue them and their inverses using
   lem-pur-sheaf-hom-cover-gluing, whose uniqueness also proves glued_unique.
7. Restrict gluedIso and precompose with the unit to obtain restrictionIso. Its
   target is quasi-coherent. The adjunction transpose formula identifies gluedIso
   with the counit composed with the extension of restrictionIso; hence the
   canonical counit is invertible, not merely isomorphic to an invertible map.
8. The unit is identity on opens by lem-trf-etale-extension-free-presentations-hom.
   The triangle equation makes the counit identity in the same coordinates. -/
theorem etalePresentedModule_effectiveRecovery
    (c : ∀ X : Scheme.{u}, ZariskiEtaleModuleContext X)
    (T : Scheme.{u}) (G : SmallEtaleModules T) [G.IsQuasicoherent]
    (I : Type w) (U : I → T.Etale)
    (cover : ∀ x : T, ∃ (i : I) (y : (U i).left), (U i).hom.base y = x)
    (K J : I → Type u)
    (d : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (K i) ⟶
      SheafOfModules.free (J i))
    (q : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (J i) ⟶
      (presentedEtaleRestriction (U i)).obj G)
    (zero : ∀ i, d i ≫ q i = 0)
    (presentation : ∀ i, Nonempty (IsColimit (CokernelCofork.ofπ (q i) (zero i)))) :
    Nonempty (EtalePresentedRecovery c T G I U K J d q) := by
  classical
  obtain ⟨L⟩ := etalePresented_localCokernels c T G I U K J d q zero presentation
  obtain ⟨D⟩ := etalePresented_descentGluing c T G I U K J d q cover L
  have hF : D.globalModule.IsQuasicoherent := D.globalQC
  have hη := presentedUnit_isIso (c T) D.globalModule D.globalTensor D.global_unit
  let a : D.globalModule ≅ (c T).restriction.obj G :=
    asIso ((c T).adjunction.unit.app D.globalModule) ≪≫
      (c T).restriction.mapIso D.gluedIso
  have hRG : ((c T).restriction.obj G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso a hF
  have hb : (c T).extension.map a.hom ≫ (c T).adjunction.counit.app G =
      D.gluedIso.hom := by
    exact ((c T).adjunction.homEquiv _ _).symm_apply_apply D.gluedIso.hom
  have hε : IsIso ((c T).adjunction.counit.app G) := IsIso.of_isIso_fac_left hb
  obtain ⟨e, hlin, hunit⟩ := presentedRestrictionCoordinates c T ((c T).restriction.obj G)
  refine ⟨{
    freeIso := L.freeIso
    freeIso_hom := L.freeIso_hom
    lift := L.lift
    lift_image := L.lift_image
    lift_unique := L.lift_unique
    localModule := L.localModule
    localQuotient := L.localQuotient
    localZero := L.localZero
    localCokernel := L.localCokernel
    localQC := L.localQC
    localIso := L.localIso
    local_projection := L.local_projection
    localTensor := L.localTensor
    local_linear := L.local_linear
    local_unit := L.local_unit
    overlap := D.overlap
    overlap_image := D.overlap_image
    overlap_unique := D.overlap_unique
    cocycle := D.cocycle
    globalModule := D.globalModule
    globalQC := D.globalQC
    chartIso := D.chartIso
    effective := D.effective
    globalTensor := D.globalTensor
    global_linear := D.global_linear
    global_unit := D.global_unit
    gluedIso := D.gluedIso
    glued_local := D.glued_local
    glued_unique := D.glued_unique
    restrictionIso := a
    restriction_hom := rfl
    restrictionQC := hRG
    counitIso := hε
    restrictionTensor := e
    restriction_linear := hlin
    restriction_unit := hunit
    counit_open := ?_ }⟩
  intro W
  let A := (AlgebraicGeometry.gabberOpenEtale T).obj W
  have he : e.inv.hom.app (op A) ≫ e.hom.hom.app (op A) = 𝟙 _ := by
    simp
  have hu : ((c T).adjunction.unit.app ((c T).restriction.obj G)).app W =
      (tensorOpenSectionIso T ((c T).restriction.obj G) W).inv ≫
        e.inv.hom.app (op A) := by
    apply (cancel_mono
      (e.hom.hom.app (op A) ≫
        (tensorOpenSectionIso T ((c T).restriction.obj G) W).hom)).mp
    simpa only [Category.assoc, ← Category.assoc (e.inv.hom.app (op A)), he,
      Category.id_comp, Iso.inv_hom_id] using hunit W
  have ht := congrArg (fun f ↦ f.app W) ((c T).adjunction.right_triangle_components G)
  change ((c T).adjunction.unit.app ((c T).restriction.obj G)).app W ≫
    ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
      ((c T).adjunction.counit.app G)).hom.app (op A) = 𝟙 _ at ht
  rw [hu] at ht
  exact ht

end
end AlgebraicGeometry.Scheme.Modules
