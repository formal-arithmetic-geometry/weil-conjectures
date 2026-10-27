/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q58, C9
-/
module

public import Sheaf.AlgebraicGeometry.RingedSubspace
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.IntersectionStructureSections
import Sheaf.AlgebraicGeometry.QuasiAffineChartLimitTopology
import Sheaf.AlgebraicGeometry.AffinizationLocalizationStalkCriterion
import WeilConjectures.Topology.InverseImageStalk

/-!
# Canonical affine embedding of an intersection of quasi-compact opens

Source: Stacks Project, Tag 0API, `lemma-sits-in-functions`, including its final assertion.
(blueprint: lem-a1-intersection-canonical-affine-embedding)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

open LocallyRingedSpace

private theorem subspace_stalk_iso (X : LocallyRingedSpace.{u}) (S : Set X) (x : S) :
    IsIso ((ringedSubspaceι X S).hom.stalkMap x) := by
  obtain ⟨c, hc, _⟩ := TopCat.Sheaf.exists_inverseImage_stalk_iso_commRing
    (subspaceInclusion X S) x
  have he : (ringedSubspaceι X S).hom.stalkMap x = (c.app X.sheaf).hom := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hx
    rw [PresheafedSpace.stalkMap_germ]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (hc X.sheaf V hx a).symm
  rw [he]
  infer_instance

private theorem subspace_local (X : LocallyRingedSpace.{u}) (S : Set X) :
    ∀ x : S, IsLocalRing ((ringedSubspace X S).presheaf.stalk x) := by
  intro x
  have := subspace_stalk_iso X S x
  exact (asIso ((ringedSubspaceι X S).hom.stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing

private noncomputable def subspace_ι (X : LocallyRingedSpace.{u}) (S : Set X)
    (h : ∀ x : S, IsLocalRing ((ringedSubspace X S).presheaf.stalk x)) :
    locallyRingedSubspace X S h ⟶ X :=
  LocallyRingedSpace.homMk (ringedSubspaceι X S) (fun x ↦ by
    have := subspace_stalk_iso X S x
    infer_instance)

private noncomputable def subspace_lift_sheaf {Z X : LocallyRingedSpace.{u}}
    (S : Set X) (f : Z ⟶ X) (g : Z.toTopCat ⟶ TopCat.of S)
    (hg : g ≫ subspaceInclusion X S = f.base) :
    Z.toSheafedSpace ⟶ ringedSubspace X S := by
  let a : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat
      (subspaceInclusion X S)).obj ((TopCat.Sheaf.pushforward CommRingCat g).obj Z.sheaf) :=
    ⟨f.c ≫ (TopCat.Presheaf.pushforwardEq hg.symm Z.presheaf).hom⟩
  let b := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (subspaceInclusion X S)).homEquiv X.sheaf
      ((TopCat.Sheaf.pushforward CommRingCat g).obj Z.sheaf) |>.symm a
  exact InducedCategory.homMk ⟨g, b.hom⟩

private theorem subspace_lift_sheaf_fac {Z X : LocallyRingedSpace.{u}}
    (S : Set X) (f : Z ⟶ X) (g : Z.toTopCat ⟶ TopCat.of S)
    (hg : g ≫ subspaceInclusion X S = f.base) :
    subspace_lift_sheaf S f g hg ≫ ringedSubspaceι X S = f.toShHom := by
  apply SheafedSpace.ext _ _ hg
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (subspaceInclusion X S)).homEquiv _ _ |>.apply_symm_apply
      (⟨f.c ≫ (TopCat.Presheaf.pushforwardEq hg.symm Z.presheaf).hom⟩ :
        X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat
          (subspaceInclusion X S)).obj
            ((TopCat.Sheaf.pushforward CommRingCat g).obj Z.sheaf))
  have hc := congrArg (fun q ↦ q.hom) h
  change (subspace_lift_sheaf S f g hg ≫ ringedSubspaceι X S).hom.c =
    f.c ≫ (TopCat.Presheaf.pushforwardEq hg.symm Z.presheaf).hom at hc
  rw [hc]
  apply NatTrans.ext
  funext V
  simp [Category.assoc, ← Z.presheaf.map_comp]

private noncomputable def subspace_lift {Z X : LocallyRingedSpace.{u}}
    (S : Set X) (h : ∀ x : S, IsLocalRing ((ringedSubspace X S).presheaf.stalk x))
    (f : Z ⟶ X) (g : Z.toTopCat ⟶ TopCat.of S)
    (hg : g ≫ subspaceInclusion X S = f.base) : Z ⟶ locallyRingedSubspace X S h := by
  let l := subspace_lift_sheaf S f g hg
  refine LocallyRingedSpace.homMk l ?_
  intro x
  have he := PresheafedSpace.stalkMap.congr_hom _ _
    (congrArg InducedCategory.Hom.hom (subspace_lift_sheaf_fac S f g hg)) x
  change (l.hom ≫ (ringedSubspaceι X S).hom).stalkMap x = _ at he
  rw [PresheafedSpace.stalkMap.comp] at he
  have hi := subspace_stalk_iso X S (l.hom.base x)
  have hl : IsLocalHom
      (((ringedSubspaceι X S).hom.stalkMap (l.hom.base x) ≫ l.hom.stalkMap x).hom) := by
    rw [he]
    let e : X.presheaf.stalk ((l ≫ ringedSubspaceι X S).hom.base x) ≅
        X.presheaf.stalk (f.base x) := eqToIso
          (congrArg X.presheaf.stalk (ConcreteCategory.congr_hom hg x))
    have : IsLocalHom e.hom.hom := by
      exact ⟨fun a ha ↦ by
        have hi := ha.map e.inv.hom
        simpa only [← CommRingCat.comp_apply, e.hom_inv_id, CommRingCat.id_apply] using hi⟩
    change IsLocalHom ((f.stalkMap x).hom.comp e.hom.hom)
    infer_instance
  have hh : l.hom.stalkMap x =
      inv ((ringedSubspaceι X S).hom.stalkMap (l.hom.base x)) ≫
        ((ringedSubspaceι X S).hom.stalkMap (l.hom.base x) ≫ l.hom.stalkMap x) := by
    simp
  rw [hh]
  infer_instance

private theorem subspace_lift_fac {Z X : LocallyRingedSpace.{u}}
    (S : Set X) (h : ∀ x : S, IsLocalRing ((ringedSubspace X S).presheaf.stalk x))
    (f : Z ⟶ X) (g : Z.toTopCat ⟶ TopCat.of S)
    (hg : g ≫ subspaceInclusion X S = f.base) :
    subspace_lift S h f g hg ≫ subspace_ι X S h = f := by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  change subspace_lift_sheaf S f g hg ≫ ringedSubspaceι X S = f.toShHom
  exact subspace_lift_sheaf_fac S f g hg

private theorem subspace_mono (X : LocallyRingedSpace.{u}) (S : Set X)
    (h : ∀ x : S, IsLocalRing ((ringedSubspace X S).presheaf.stalk x)) :
    Mono (subspace_ι X S h) := by
  have : Mono (ringedSubspaceι X S) :=
    SheafedSpace.mono_of_base_injective_of_stalk_epi _ Subtype.val_injective (fun x ↦ by
      have := subspace_stalk_iso X S x
      infer_instance)
  apply LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map
  exact this

private theorem compact_opens_inter (Y : Scheme.{u})
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → Scheme.IsQuasiAffine U.toScheme)
    (P Q : Y.Opens) (hP : IsCompact (P : Set Y)) (hQ : IsCompact (Q : Set Y)) :
    IsCompact ((P ⊓ Q : Y.Opens) : Set Y) := by
  let R := P ⊔ Q
  have : R.toScheme.IsQuasiAffine := hY R (hP.union hQ)
  have : QuasiSeparatedSpace R.toScheme := inferInstance
  have hqs : IsQuasiSeparated ((P ⊔ Q : Y.Opens) : Set Y) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (P ⊔ Q).isOpen).mpr
      (inferInstanceAs (QuasiSeparatedSpace R.toScheme))
  exact hqs P Q (fun _ hx ↦ Or.inl hx) P.isOpen hP
    (fun _ hx ↦ Or.inr hx) Q.isOpen hQ

private theorem ind_quasi_separated (Y : Scheme.{u})
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → Scheme.IsQuasiAffine U.toScheme) :
    QuasiSeparatedSpace Y := by
  apply quasiSeparatedSpace_iff_forall_affineOpens.mpr
  intro P Q
  exact compact_opens_inter Y hY P.val Q.val P.property.isCompact Q.property.isCompact

private theorem subspace_stalk_lift_iso {Z X : LocallyRingedSpace.{u}}
    (S : Set X) (h : ∀ x : S, IsLocalRing ((ringedSubspace X S).presheaf.stalk x))
    (f : Z ⟶ X) (g : Z.toTopCat ⟶ TopCat.of S)
    (hg : g ≫ subspaceInclusion X S = f.base) (x : Z)
    [IsIso (f.stalkMap x)] : IsIso ((subspace_lift S h f g hg).stalkMap x) := by
  let l := subspace_lift S h f g hg
  have he := PresheafedSpace.stalkMap.congr_hom _ _
    (congrArg InducedCategory.Hom.hom (subspace_lift_sheaf_fac S f g hg)) x
  change ((subspace_lift_sheaf S f g hg).hom ≫ (ringedSubspaceι X S).hom).stalkMap x = _
    at he
  rw [PresheafedSpace.stalkMap.comp] at he
  have : IsIso ((subspace_ι X S h).stalkMap (l.base x)) :=
    subspace_stalk_iso X S (l.base x)
  have : IsIso ((subspace_ι X S h).stalkMap (l.base x) ≫ l.stalkMap x) := by
    change IsIso ((ringedSubspaceι X S).hom.stalkMap
      ((subspace_lift_sheaf S f g hg).hom.base x) ≫
        (subspace_lift_sheaf S f g hg).hom.stalkMap x)
    rw [he]
    change IsIso (_ ≫ f.stalkMap x)
    infer_instance
  exact IsIso.of_isIso_comp_left ((subspace_ι X S h).stalkMap (l.base x)) _

private theorem chart_sections_colimit (Y : Scheme.{u}) [QuasiSeparatedSpace Y]
    {J : Type u} [PartialOrder J] [Nonempty J]
    (V : J → Y.Opens) (hV : ∀ j, IsCompact (V j : Set Y))
    (hanti : Antitone V) (hreflect : ∀ i j, V j ≤ V i → i ≤ j)
    (hdir : ∀ i j, ∃ k, V k ≤ V i ⊓ V j) :
    ∃ r : Scheme.quasiAffineChartSectionDiagram Y V hanti ⟶
        (Functor.const J).obj (Scheme.intersectionSections Y V),
      (∀ j, r.app j = (V j).topIso.hom ≫
        Scheme.intersectionRestriction Y V (V j) (fun _ hx ↦ hx j)) ∧
      Nonempty (CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.Cocone.mk (Scheme.intersectionSections Y V) r)) := by
  classical
  open CategoryTheory.Limits in
  obtain ⟨_, _, ⟨r, hr, ⟨hc⟩, _⟩, _⟩ :=
    Scheme.sections_intersection_structure_colimit Y V hV hdir
  let T : J ⥤ {W : Y.Opens // W ∈ Set.range V}ᵒᵖ :=
    { obj := fun j ↦ op ⟨V j, ⟨j, rfl⟩⟩
      map := fun f ↦ (homOfLE (hanti f.le)).op }
  let ff : T.FullyFaithful :=
    { preimage := fun {i j} f ↦ homOfLE (hreflect i j (leOfHom f.unop)) }
  have : T.Full := ff.full
  have : T.Faithful := ff.faithful
  have : T.EssSurj := ⟨fun W ↦ by
    obtain ⟨j, hj⟩ := W.unop.property
    exact ⟨j, ⟨eqToIso (by apply unop_injective; exact Subtype.ext hj)⟩⟩⟩
  have : T.IsEquivalence := {}
  let r' := (Cocone.mk _ r).whisker T
  have hc' : IsColimit r' := hc.whiskerEquivalence T.asEquivalence
  let e : Scheme.quasiAffineChartSectionDiagram Y V hanti ≅
      T ⋙ Scheme.intersectionOpenDiagram Y V :=
    NatIso.ofComponents (fun j ↦ (V j).topIso) (by
      intro i j f
      change (Y.homOfLE (hanti f.le)).appTop ≫ (V j).topIso.hom =
        (V i).topIso.hom ≫ Y.presheaf.map (homOfLE (hanti f.le)).op
      simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom,
        ← Y.presheaf.map_comp]
      congr 1)
  let c := (Cocone.precompose e.hom).obj r'
  refine ⟨c.ι, ?_, ⟨(IsColimit.precomposeHomEquiv e r').symm hc'⟩⟩
  intro j
  change (V j).topIso.hom ≫ r.app (op ⟨V j, ⟨j, rfl⟩⟩) = _
  rw [hr]

private theorem subspace_transport (X Y : LocallyRingedSpace.{u})
    (S : Set X) (T : Set Y)
    (hS : ∀ x : S, IsLocalRing ((ringedSubspace X S).presheaf.stalk x))
    (hT : ∀ x : T, IsLocalRing ((ringedSubspace Y T).presheaf.stalk x))
    (e : X ≅ Y) (he : e.hom.base '' S = T) :
    ∃ a : locallyRingedSubspace X S hS ≅ locallyRingedSubspace Y T hT,
      (∀ x : S, (a.hom.base x).val = e.hom.base x.val) ∧
      a.hom.toShHom ≫ ringedSubspaceι Y T =
        ringedSubspaceι X S ≫ e.hom.toShHom := by
  classical
  have hf : ∀ x : S, e.hom.base x.val ∈ T := fun x ↦ he ▸ ⟨x.val, x.property, rfl⟩
  have hi : ∀ y : T, e.inv.base y.val ∈ S := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (show y.val ∈ e.hom.base '' S from he.symm ▸ y.property)
    have hinv : e.inv.base y.val = x := by
      have := ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.base) e.hom_inv_id) x
      change e.inv.base (e.hom.base x) = x at this
      rwa [hxy] at this
    exact hinv ▸ hx
  let g : (locallyRingedSubspace X S hS).toTopCat ⟶ TopCat.of T :=
    TopCat.ofHom ⟨fun x ↦ ⟨e.hom.base x.val, hf x⟩,
      (e.hom.base.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let k : (locallyRingedSubspace Y T hT).toTopCat ⟶ TopCat.of S :=
    TopCat.ofHom ⟨fun y ↦ ⟨e.inv.base y.val, hi y⟩,
      (e.inv.base.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let a := subspace_lift T hT (subspace_ι X S hS ≫ e.hom) g rfl
  let b := subspace_lift S hS (subspace_ι Y T hT ≫ e.inv) k rfl
  have ha : a ≫ subspace_ι Y T hT = subspace_ι X S hS ≫ e.hom :=
    subspace_lift_fac _ _ _ _ _
  have hb : b ≫ subspace_ι X S hS = subspace_ι Y T hT ≫ e.inv :=
    subspace_lift_fac _ _ _ _ _
  have : Mono (subspace_ι X S hS) := subspace_mono X S hS
  have : Mono (subspace_ι Y T hT) := subspace_mono Y T hT
  let i : locallyRingedSubspace X S hS ≅ locallyRingedSubspace Y T hT :=
    { hom := a
      inv := b
      hom_inv_id := by
        rw [← cancel_mono (subspace_ι X S hS), Category.assoc, hb, ← Category.assoc,
          ha, Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono (subspace_ι Y T hT), Category.assoc, ha, ← Category.assoc,
          hb, Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp] }
  refine ⟨i, fun _ ↦ rfl, ?_⟩
  exact congrArg (fun f ↦ LocallyRingedSpace.forgetToSheafedSpace.map f) ha

private theorem stage_localization (Z T : LocallyRingedSpace.{u})
    (f : Z ⟶ T) (z : Z)
    [LocallyRingedSpace.IsOpenImmersion T.toΓSpec] [IsIso (f.stalkMap z)] :
    ∃ θ : CommRingCat.of (Localization.AtPrime
        ((Z.toΓSpecFun z).comap (Γ.map f.op).hom).asIdeal) ⟶ Z.presheaf.stalk z,
      CommRingCat.ofHom (algebraMap (Γ.obj (op T)) (Localization.AtPrime
          ((Z.toΓSpecFun z).comap (Γ.map f.op).hom).asIdeal)) ≫ θ =
        Γ.map f.op ≫ Z.presheaf.Γgerm z ∧ IsIso θ := by
  have hp : (Z.toΓSpecFun z).comap (Γ.map f.op).hom = T.toΓSpecFun (f.base z) := by
    have hn := identityToΓSpec.naturality f
    exact (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.base) hn) z).symm
  let θ := CommRingCat.ofHom
    (StructureSheaf.stalkIso (Γ.obj (op T)) (T.toΓSpecFun (f.base z))).toRingHom ≫
      T.toΓSpec.stalkMap (f.base z) ≫ f.stalkMap z
  have ht : CommRingCat.ofHom
      (algebraMap (Γ.obj (op T)) (Localization.AtPrime
        (T.toΓSpecFun (f.base z)).asIdeal)) ≫ θ =
        Γ.map f.op ≫ Z.presheaf.Γgerm z := by
    dsimp only [θ]
    rw [← Category.assoc, ← Category.assoc]
    have ha : CommRingCat.ofHom (algebraMap (Γ.obj (op T)) _) ≫
        CommRingCat.ofHom (StructureSheaf.stalkIso _ _).toRingHom =
          StructureSheaf.toStalk (Γ.obj (op T)) (T.toΓSpecFun (f.base z)) := by
      ext a
      exact (StructureSheaf.stalkIso _ _).commutes a
    rw [ha]
    change (StructureSheaf.toStalk _ _ ≫ T.toΓSpecSheafedSpace.hom.stalkMap _) ≫ _ = _
    rw [T.toStalk_stalkMap_toΓSpec]
    exact LocallyRingedSpace.stalkMap_germ f ⊤ z trivial
  have : IsIso (CommRingCat.ofHom
      (StructureSheaf.stalkIso (Γ.obj (op T)) (T.toΓSpecFun (f.base z))).toRingHom) :=
    (StructureSheaf.stalkIso _ _).toRingEquiv.toCommRingCatIso.isIso_hom
  have hθ : IsIso θ := inferInstance
  rw [hp]
  exact ⟨θ, ht, hθ⟩

-- Preserve the named proof binder `he` of the original public statement.
set_option linter.unusedVariables false in
/-- The canonical map of a nonempty intersection of quasi-compact opens of an
ind-quasi-affine scheme identifies it, with its inverse-image structure sheaf, with an
intersection of quasi-compact opens of the spectrum of its sections. Its restriction to
any ambient open inside the intersection is an open immersion, and the construction is
natural under scheme isomorphisms preserving the subsets.

Source: Stacks Project, Tag 0API, `lemma-sits-in-functions`.
(blueprint: lem-a1-intersection-canonical-affine-embedding)

Proof:
1. Quasi-affineness of compact open unions gives compact open intersections, hence
   quasi-separatedness of Y. Index all compact open neighborhoods of E by reverse
   inclusion. This is a small nonempty directed family with intersection E.
2. The intersection-sections colimit theorem gives the colimit of the chart rings.
   Reindex its distinct-open diagram and identify its maps with pullback along the
   locally ringed chart inclusions using the inverse-image adjunction.
3. Inverse image preserves stalks, giving the local rings of E. The affine adjunction
   gives the canonical normalized map and proves its uniqueness.
4. The chart-limit topology theorem identifies that map with a homeomorphism onto
   an intersection of compact opens. Each chart localization maps isomorphically to
   the corresponding stalk of E; the localization-stalk criterion upgrades the
   homeomorphism to an isomorphism of locally ringed subspaces.
5. An ambient open W inside E lifts to the subspace. The chart-limit theorem makes
   its affine image open, and the stalk identifications make its map an open immersion.
6. Restrict an ambient isomorphism using the inverse-image adjunction. Its inverse
   restricts too, and monicity of the subspace inclusions proves the inverse laws.
   Naturality of the affine adjunction proves the final compatibility. -/
theorem intersection_canonical_affine_embedding
    (Y : Scheme.{u})
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → Scheme.IsQuasiAffine U.toScheme)
    (I : Type v) [Nonempty I] (U : I → Y.Opens)
    (hU : ∀ i : I, IsCompact (U i : Set Y))
    (E : Set Y) (hE : E = ⋂ i : I, (U i : Set Y)) :
    ∃ hlocal : ∀ x : E,
      IsLocalRing ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.stalk x),
    ∃ j : locallyRingedSubspace Y.toLocallyRingedSpace E hlocal ⟶
      (Spec ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace,
      (toSpecΓ ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤)) ≫
        j.c.app (op ⊤) = 𝟙 _) ∧
      (∀ j' : locallyRingedSubspace Y.toLocallyRingedSpace E hlocal ⟶
        (Spec ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace,
        toSpecΓ ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤)) ≫
          j'.c.app (op ⊤) = 𝟙 _ → j' = j) ∧
      (∃ (V : Set (Spec
          ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).Opens),
        V.Nonempty ∧ (∀ W ∈ V, IsCompact (W : Set (Spec
          ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))))) ∧
        ∃ hF : ∀ x : (⋂₀ (SetLike.coe '' V) : Set (Spec
            ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤)))),
          IsLocalRing ((ringedSubspace
            (Spec
              ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace
            (⋂₀ (SetLike.coe '' V))).presheaf.stalk x),
        ∃ e : locallyRingedSubspace Y.toLocallyRingedSpace E hlocal ≅
          locallyRingedSubspace
            (Spec
              ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace
            (⋂₀ (SetLike.coe '' V)) hF,
          e.hom.toShHom ≫ ringedSubspaceι
            (Spec
              ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace
            (⋂₀ (SetLike.coe '' V)) = j.toShHom) ∧
      (∀ (W : Y.Opens) (hW : (W : Set Y) ⊆ E),
        ∃ l : W.toScheme.toLocallyRingedSpace ⟶
          locallyRingedSubspace Y.toLocallyRingedSpace E hlocal,
          (∀ x : W, l.base x = ⟨x.val, hW x.property⟩) ∧
          (l.toShHom ≫ ringedSubspaceι Y.toLocallyRingedSpace E = W.ι.toLRSHom.toShHom) ∧
          (l ≫ j = ΓSpec.locallyRingedSpaceAdjunction.homEquiv _ _
            (LocallyRingedSpace.Γ.map l.op).op) ∧
          IsOpenImmersion (Scheme.Hom.mk (l ≫ j))) ∧
      (∀ (Y' : Scheme.{u}) (E' : Set Y')
          (hlocal' : ∀ x : E',
            IsLocalRing ((ringedSubspace Y'.toLocallyRingedSpace E').presheaf.stalk x))
          (e : Y ≅ Y') (he : e.hom '' E = E'),
        ∃ a : locallyRingedSubspace Y.toLocallyRingedSpace E hlocal ≅
          locallyRingedSubspace Y'.toLocallyRingedSpace E' hlocal',
          (∀ x : E, (a.hom.base x).val = e.hom x.val) ∧
          (a.hom.toShHom ≫ ringedSubspaceι Y'.toLocallyRingedSpace E' =
            ringedSubspaceι Y.toLocallyRingedSpace E ≫ e.hom.toLRSHom.toShHom) ∧
          a.hom ≫ (locallyRingedSubspace Y'.toLocallyRingedSpace E' hlocal').toΓSpec =
            j ≫ Spec.locallyRingedSpaceMap (LocallyRingedSpace.Γ.map a.hom.op)) := by
  classical
  have : QuasiSeparatedSpace Y := ind_quasi_separated Y hY
  let J := OrderDual {V : Y.Opens // IsCompact (V : Set Y) ∧ E ⊆ V}
  let V : J → Y.Opens := fun j ↦ j.val
  have hV : ∀ j, IsCompact (V j : Set Y) := fun j ↦ j.property.1
  have hVE : ∀ j, E ⊆ V j := fun j ↦ j.property.2
  have hUV : ∀ i, E ⊆ U i := by
    intro i x hx
    exact Set.mem_iInter.mp (hE ▸ hx) i
  have : Nonempty J := ⟨⟨U (Classical.arbitrary I), hU _, hUV _⟩⟩
  have hdir : Directed (· ≤ ·) (id : J → J) := by
    intro i j
    refine ⟨⟨V i ⊓ V j, compact_opens_inter Y hY _ _ (hV i) (hV j), ?_⟩,
      ?_, ?_⟩
    · exact fun x hx ↦ ⟨hVE i hx, hVE j hx⟩
    · exact inf_le_left (a := V i) (b := V j)
    · exact inf_le_right (a := V i) (b := V j)
  have hanti : Antitone V := fun _ _ h ↦ h
  have hEJ : E = {x : Y | ∀ j : J, x ∈ V j} := by
    ext x
    constructor
    · exact fun hx j ↦ hVE j hx
    · intro hx
      rw [hE]
      exact Set.mem_iInter.mpr fun i ↦ hx ⟨U i, hU i, hUV i⟩
  rw [hEJ]
  let P : Set Y := {x : Y | ∀ j : J, x ∈ V j}
  let hl := subspace_local Y.toLocallyRingedSpace P
  let Z := locallyRingedSubspace Y.toLocallyRingedSpace P hl
  let inc := subspace_ι Y.toLocallyRingedSpace P hl
  have hPV : ∀ j, P ⊆ V j := fun j x hx ↦ hx j
  let toChart : ∀ j, Z ⟶ (V j).toScheme.toLocallyRingedSpace := fun j ↦
    LocallyRingedSpace.IsOpenImmersion.lift (V j).ι.toLRSHom inc (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨x.val, x.property j⟩, rfl⟩)
  have chart_fac (j) : toChart j ≫ (V j).ι.toLRSHom = inc :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have chart_base (j) (x : Z) : (toChart j).base x = ⟨x.val, x.property j⟩ := by
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.base) (chart_fac j)) x
  have chart_stalk (j) (x : Z) : IsIso ((toChart j).stalkMap x) := by
    have : IsIso (inc.stalkMap x) := subspace_stalk_iso _ _ x
    have : IsIso ((toChart j ≫ (V j).ι.toLRSHom).stalkMap x) := by
      rw [chart_fac j]
      infer_instance
    have hs := LocallyRingedSpace.stalkMap_comp (toChart j) (V j).ι.toLRSHom x
    have : IsIso ((V j).ι.toLRSHom.stalkMap ((toChart j).base x) ≫
        (toChart j).stalkMap x) := hs ▸ this
    exact IsIso.of_isIso_comp_left ((V j).ι.toLRSHom.stalkMap _) _
  obtain ⟨r, hr, ⟨hc⟩⟩ := chart_sections_colimit Y V hV hanti
    (fun _ _ h ↦ h) (fun i j ↦ by
      obtain ⟨k, hik, hjk⟩ := hdir i j
      exact ⟨k, le_inf hik hjk⟩)
  have hr_chart (j) : r.app j = Γ.map (toChart j).op := by
    rw [hr]
    change (V j).topIso.hom ≫ Scheme.intersectionRestriction Y V (V j)
      (fun _ hx ↦ hx j) = (toChart j).c.app (op ⊤)
    have he := SheafedSpace.congr_hom_app
      (congrArg (fun f ↦ f.toShHom) (chart_fac j)) (op (V j))
    have he' := congrArg ((V j).topIso.hom ≫ ·) he
    change (V j).topIso.hom ≫ (V j).ι.app (V j) ≫
      (toChart j).c.app (op ((V j).ι ⁻¹ᵁ V j)) = _ at he'
    have htop : (V j).ι ⁻¹ᵁ V j = ⊤ := (V j).ι_preimage_self
    have hunit : (V j).topIso.hom ≫ (V j).ι.app (V j) =
        (V j).toScheme.presheaf.map (eqToHom htop).op := by
      simp [Scheme.Opens.topIso_hom, Scheme.Opens.ι_app,
        ← Y.presheaf.map_comp, Scheme.Opens.toScheme_presheaf_map]
      congr 1
    rw [← Category.assoc, hunit] at he'
    have hn := (toChart j).c.naturality (eqToHom htop).op
    dsimp only [TopCat.Presheaf.pushforward_obj_map] at hn
    rw [hn] at he'
    dsimp only [Scheme.intersectionRestriction]
    have hpre : (Opens.map (toChart j).base).obj ((V j).ι ⁻¹ᵁ V j) = ⊤ := by
      rw [htop]
      rfl
    apply (cancel_mono (Z.presheaf.map (eqToHom hpre).op)).mp
    have hmap : ((Opens.map (toChart j).base).map
        (eqToHom htop).op.unop).op = (eqToHom hpre).op := Subsingleton.elim _ _
    rw [hmap] at he'
    erw [he']
    change ((V j).topIso.hom ≫ inc.c.app (op (V j)) ≫
      Z.presheaf.map (homOfLE (by intro x hx; exact x.property j)).op) ≫
        Z.presheaf.map (eqToHom hpre).op = _
    simp only [Category.assoc, ← Z.presheaf.map_comp]
    congr 2
  have : ∀ j : J, (V j).toScheme.IsQuasiAffine := fun j ↦ hY _ (hV j)
  obtain ⟨t, ht, huniq, hemb, hrange, hopen, hWopen⟩ :=
    Scheme.quasiAffineChartLimitTopology Y J hdir V hanti (Cocone.mk _ r) hc
  have htZ : t = Z.toΓSpec.base.hom := by
    symm
    apply huniq
    intro j x
    have hn := identityToΓSpec.naturality (toChart j)
    have he := ConcreteCategory.congr_hom
      (congrArg (fun f : Z ⟶ (Spec ((V j).toScheme.presheaf.obj (op ⊤))).toLocallyRingedSpace
        ↦ f.base) hn) x
    change (V j).toScheme.toSpecΓ ((toChart j).base x) =
      (Spec.map (Γ.map (toChart j).op)) (Z.toΓSpec.base x) at he
    change (Spec.map (r.app j)) (Z.toΓSpec.base x) = _
    have heq : (r.app j : (V j).toScheme.presheaf.obj (op ⊤) ⟶ Γ.obj (op Z)) =
        Γ.map (toChart j).op := hr_chart j
    erw [heq]
    exact he.symm.trans (congrArg (V j).toScheme.toSpecΓ (chart_base j x))
  have : IsDirected J (· ≤ ·) := ⟨hdir⟩
  have hstage (z : Z) (j : J) :
      ∃ θ : CommRingCat.of (Localization.AtPrime
          ((Z.toΓSpecFun z).comap (r.app j).hom).asIdeal) ⟶ Z.presheaf.stalk z,
        CommRingCat.ofHom (algebraMap
          ((Scheme.quasiAffineChartSectionDiagram Y V hanti).obj j)
          (Localization.AtPrime ((Z.toΓSpecFun z).comap (r.app j).hom).asIdeal)) ≫ θ =
            r.app j ≫ Z.presheaf.Γgerm z ∧ IsIso θ := by
    have := chart_stalk j z
    have : LocallyRingedSpace.IsOpenImmersion (V j).toScheme.toLocallyRingedSpace.toΓSpec :=
      inferInstanceAs (IsOpenImmersion (V j).toScheme.toSpecΓ)
    let rj : Γ.obj (op (V j).toScheme.toLocallyRingedSpace) ⟶ Γ.obj (op Z) := r.app j
    change ∃ θ : CommRingCat.of (Localization.AtPrime
        ((Z.toΓSpecFun z).comap rj.hom).asIdeal) ⟶ Z.presheaf.stalk z,
      CommRingCat.ofHom (algebraMap (Γ.obj (op (V j).toScheme.toLocallyRingedSpace))
        (Localization.AtPrime ((Z.toΓSpecFun z).comap rj.hom).asIdeal)) ≫
        θ = rj ≫ Z.presheaf.Γgerm z ∧ IsIso θ
    have heq : rj = Γ.map (toChart j).op := hr_chart j
    rw [heq]
    exact stage_localization Z (V j).toScheme.toLocallyRingedSpace (toChart j) z
  obtain ⟨hstalk, hsub⟩ := affinization_localization_stalk_criterion Z
    (Scheme.quasiAffineChartSectionDiagram Y V hanti) r hc hstage
  refine ⟨hl, Z.toΓSpec, Z.Γ_Spec_left_triangle, ?_, ?_, ?_, ?_⟩
  · intro j' hj'
    apply (ΓSpec.locallyRingedSpaceAdjunction.homEquiv _ _).symm.injective
    apply Quiver.Hom.unop_inj
    change toSpecΓ _ ≫ j'.c.app (op ⊤) = toSpecΓ _ ≫ Z.toΓSpec.c.app (op ⊤)
    rw [hj', Z.Γ_Spec_left_triangle]
    rfl
  · let B : J → (Spec (Γ.obj (op Z))).Opens := fun j ↦
      ⟨(Spec.map (r.app j)) ⁻¹' Set.range (V j).toScheme.toSpecΓ, (hopen j).1⟩
    let F : Set (Spec (Γ.obj (op Z))) := ⋂₀ (SetLike.coe '' Set.range B)
    have hF : F = Set.range t := by
      rw [hrange]
      ext x
      simp [F, B]
    let homeo : Z ≃ₜ F := hemb.toHomeomorph.trans (Homeomorph.setCongr hF.symm)
    obtain ⟨hlocal, e, i, hi, hcomp⟩ := hsub F homeo (by
      intro x
      change t x = Z.toΓSpec.base x
      exact congrArg (fun f ↦ f x) htZ)
    refine ⟨Set.range B, Set.range_nonempty _, ?_, hlocal, e, ?_⟩
    · rintro _ ⟨j, rfl⟩
      exact (hopen j).2
    · change e.hom.toShHom ≫ ringedSubspaceι
        (Spec.locallyRingedSpaceObj (Γ.obj (op Z))) F = Z.toΓSpec.toShHom
      rw [← hi]
      exact congrArg (fun f ↦ f.toShHom) hcomp
  · intro W hW
    let g : W.toScheme.toLocallyRingedSpace.toTopCat ⟶ TopCat.of P :=
      TopCat.ofHom ⟨fun x ↦ ⟨x.val, hW x.property⟩,
        continuous_subtype_val.subtype_mk _⟩
    let l := subspace_lift P hl W.ι.toLRSHom g rfl
    have hlinc : l ≫ inc = W.ι.toLRSHom := subspace_lift_fac _ _ _ _ _
    have hbase : ∀ x : W, l.base x = ⟨x.val, hW x.property⟩ := fun _ ↦ rfl
    refine ⟨l, hbase, congrArg (fun f ↦ f.toShHom) hlinc, ?_, ?_⟩
    · exact identityToΓSpec.naturality l
    · apply IsOpenImmersion.iff_isIso_stalkMap.mpr
      constructor
      · have hl_emb : Topology.IsEmbedding l.base :=
          Topology.IsEmbedding.of_comp l.base.hom.continuous continuous_subtype_val
            W.isOpenEmbedding.isEmbedding
        have hj_emb : Topology.IsEmbedding Z.toΓSpec.base := by
          change Topology.IsEmbedding Z.toΓSpec.base.hom
          rw [← htZ]
          exact hemb
        refine ⟨hj_emb.comp hl_emb, ?_⟩
        have hh := (hWopen W (by
          intro x hx
          exact Set.mem_iInter.mpr (hW hx))).2
        change IsOpen (Set.range (fun x : W ↦ Z.toΓSpec.base (l.base x)))
        have heq : Set.range (fun x : W ↦ Z.toΓSpec.base (l.base x)) =
            t '' {x | x.val ∈ W} := by
          change Set.range (fun x : W ↦ Z.toΓSpec.base.hom (l.base x)) = _
          rw [← htZ]
          ext y
          constructor
          · rintro ⟨x, rfl⟩
            exact ⟨l.base x, x.property, rfl⟩
          · rintro ⟨x, hx, rfl⟩
            exact ⟨⟨x.val, hx⟩, rfl⟩
        rw [heq]
        exact hh
      · intro x
        have : IsIso (l.stalkMap x) := subspace_stalk_lift_iso _ _ _ _ _ x
        change IsIso ((l ≫ Z.toΓSpec).stalkMap x)
        rw [LocallyRingedSpace.stalkMap_comp]
        have := (hstalk (l.base x)).1
        infer_instance
  · intro Y'  E' hl' e he
    let e' := Scheme.forgetToLocallyRingedSpace.mapIso e
    obtain ⟨a, ha, hfac⟩ := subspace_transport Y.toLocallyRingedSpace
      Y'.toLocallyRingedSpace P E' hl hl' e' he
    refine ⟨a, ha, hfac, ?_⟩
    exact identityToΓSpec.naturality a.hom

end AlgebraicGeometry
