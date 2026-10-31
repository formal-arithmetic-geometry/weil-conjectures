/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Quasi-coherent modules on algebraic-space étale sites

Source: Stacks Project, Modules on Sites, Tag 03DL (local presentations);
Properties of Spaces, Tags 03ED, 03G9 and 03M0 (small étale sites and quasi-coherent modules)
(blueprint: def-trf-space-quasi-coherent-module).

The predicate is Mathlib's `SheafOfModules.IsQuasicoherent`, without a second definition.
The slice sheafification instances keep section and ring carriers in universe `u`,
although the site has objects in universe `u+1`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma chart_map_etale {S : Scheme.{u}} (X : AlgebraicSpace S)
    {U T : X.EtaleSite} (f : U ⟶ T) : Etale ((etaleForget X).map f) := by
  exact representable_etale_scheme_tests.2.2.2.2.2.2.2.2.2 X
    U.obj.left T.obj.left U.obj.hom T.obj.hom f.hom.left
    U.property T.property f.hom.w

private def sliceToEtale {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite) :
    Over T ⥤ ((etaleForget X).obj T).Etale where
  obj V := @Scheme.Etale.mk _ _ ((etaleForget X).map V.hom) (chart_map_etale X V.hom)
  map f := MorphismProperty.Over.homMk ((etaleForget X).map f.left)
    (by
      change (etaleForget X).map f.left ≫ (etaleForget X).map _ = _
      rw [← Functor.map_comp, Over.w f]
      rfl)

private def etaleToSliceObj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.EtaleSite) (V : ((etaleForget X).obj T).Etale) : X.EtaleSite := by
  let p : Over.mk (V.hom ≫ T.obj.left.hom) ⟶ T.obj.left := Over.homMk V.hom
  refine ⟨CostructuredArrow.mk (yoneda.map p ≫ T.obj.hom), ?_⟩
  exact isEtale_comp _ _
    ((representable_etale_scheme_tests.2.2.2.2.2.2.2.1 _ _ p).2 V.prop) T.property

private def etaleToSlice {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite) :
    ((etaleForget X).obj T).Etale ⥤ Over T where
  obj V := Over.mk (ObjectProperty.homMk (Y := T)
    (CostructuredArrow.homMk (Over.homMk V.hom) (by rfl)) : etaleToSliceObj X T V ⟶ T)
  map f := Over.homMk (ObjectProperty.homMk
    (CostructuredArrow.homMk (Over.homMk f.left (by
      change f.left ≫ (_ ≫ _) = _ ≫ _
      rw [← Category.assoc, MorphismProperty.Over.w f])) (by
        change yoneda.map _ ≫ (yoneda.map _ ≫ _) = yoneda.map _ ≫ _
        rw [← Category.assoc, ← yoneda.map_comp]
        congr 2
        apply Over.OverMorphism.ext
        exact MorphismProperty.Over.w f))) (by
          apply ObjectProperty.hom_ext
          apply CostructuredArrow.hom_ext
          apply Over.OverMorphism.ext
          exact MorphismProperty.Over.w f)

private def sliceToEtaleFullyFaithful {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.EtaleSite) : (sliceToEtale X T).FullyFaithful where
  preimage {U V} f := by
    have hf : f.left ≫ (etaleForget X).map V.hom = (etaleForget X).map U.hom :=
      MorphismProperty.Over.w f
    change f.left ≫ V.hom.hom.left.left = U.hom.hom.left.left at hf
    exact Over.homMk
      (ObjectProperty.homMk (CostructuredArrow.homMk
        (Over.homMk f.left (by
          have hU := U.hom.hom.left.w
          have hV := V.hom.hom.left.w
          change f.left ≫ V.left.obj.left.hom = U.left.obj.left.hom
          rw [← hV, ← Category.assoc, hf, hU])) (by
          have hU := CostructuredArrow.w U.hom.hom
          have hV := CostructuredArrow.w V.hom.hom
          rw [← hU, ← hV, ← Category.assoc, ← yoneda.map_comp]
          congr 2
          apply Over.OverMorphism.ext
          exact hf))) (by
          apply ObjectProperty.hom_ext
          apply CostructuredArrow.hom_ext
          apply Over.OverMorphism.ext
          exact hf)
  map_preimage f := by rfl
  preimage_map f := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    rfl

private instance sliceToEtale_isEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.EtaleSite) : (sliceToEtale X T).IsEquivalence := by
  let h := sliceToEtaleFullyFaithful X T
  have := h.full
  have := h.faithful
  have : (sliceToEtale X T).EssSurj := ⟨fun V ↦
    ⟨(etaleToSlice X T).obj V, ⟨Iso.refl _⟩⟩⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private lemma exists_chart_pullback {S : Scheme.{u}} (X : AlgebraicSpace S)
    {U V W : X.EtaleSite} (f : V ⟶ U) (g : W ⟶ U)
    (x : (etaleForget X).obj V) (y : (etaleForget X).obj W)
    (hxy : ((etaleForget X).map f).base x = ((etaleForget X).map g).base y) :
    ∃ (P : X.EtaleSite) (a : P ⟶ V) (b : P ⟶ W), a ≫ f = b ≫ g ∧
      ∃ z : (etaleForget X).obj P, ((etaleForget X).map a).base z = x := by
  let f' := (etaleForget X).map f
  let g' := (etaleForget X).map g
  have : Etale f' := chart_map_etale X f
  have : Etale g' := chart_map_etale X g
  let E : ((etaleForget X).obj U).Etale :=
    Scheme.Etale.mk (pullback.fst f' g' ≫ f')
  let P : Over U := (etaleToSlice X U).obj E
  let h := sliceToEtaleFullyFaithful X U
  let a' : (sliceToEtale X U).obj P ⟶ (sliceToEtale X U).obj (Over.mk f) :=
    MorphismProperty.Over.homMk (pullback.fst f' g') rfl
  let b' : (sliceToEtale X U).obj P ⟶ (sliceToEtale X U).obj (Over.mk g) :=
    MorphismProperty.Over.homMk (pullback.snd f' g') pullback.condition.symm
  let a : P ⟶ Over.mk f := h.preimage a'
  let b : P ⟶ Over.mk g := h.preimage b'
  refine ⟨P.left, a.left, b.left, (Over.w a).trans (Over.w b).symm, ?_⟩
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨z, ?_⟩
  have ha : (etaleForget X).map a.left = pullback.fst f' g' :=
    congrArg (fun k ↦ k.left) (h.map_preimage a')
  rw [ha]
  exact hz

private def chartPointTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    GrothendieckTopology X.EtaleSite where
  sieves U := {R | ∀ x : (etaleForget X).obj U,
    ∃ (V : X.EtaleSite) (f : V ⟶ U), R f ∧
      ∃ y : (etaleForget X).obj V, ((etaleForget X).map f).base y = x}
  top_mem' U x := ⟨U, 𝟙 U, trivial, x, by simp⟩
  pullback_stable' {U V R} f hR x := by
    obtain ⟨W, g, hg, y, hy⟩ := hR (((etaleForget X).map f).base x)
    obtain ⟨P, a, b, hab, z, hz⟩ := exists_chart_pullback X f g x y hy.symm
    refine ⟨P, a, ?_, z, hz⟩
    change R (a ≫ f)
    rw [hab]
    exact R.downward_closed hg b
  transitive' {U R} hR Q hQ x := by
    obtain ⟨V, f, hf, y, hy⟩ := hR x
    obtain ⟨W, g, hg, z, hz⟩ := hQ hf y
    refine ⟨W, g ≫ f, hg, z, ?_⟩
    simpa only [Functor.map_comp, Scheme.Hom.comp_apply, hz] using hy

private lemma etaleTopology_eq_pointTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.etaleTopology = chartPointTopology X := by
  apply le_antisymm
  · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro U R hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    intro x
    obtain ⟨V, f, hf, y, hy⟩ := hR.2 x
    exact ⟨V, f, Sieve.le_generate R _ _ hf, y, hy⟩
  · intro U R hR
    rw [← Sieve.generate_sieve R]
    exact Precoverage.generate_mem_toGrothendieck
      ⟨fun V f _ ↦ chart_map_etale X f, hR⟩

private lemma mem_etaleTopology_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    {U : X.EtaleSite} (R : Sieve U) :
    R ∈ X.etaleTopology U ↔ ∀ x : (etaleForget X).obj U,
      ∃ (V : X.EtaleSite) (f : V ⟶ U), R f ∧
        ∃ y : (etaleForget X).obj V, ((etaleForget X).map f).base y = x := by
  rw [etaleTopology_eq_pointTopology]
  rfl

private lemma mem_sliceTopology_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.EtaleSite) {U : Over T} (R : Sieve U) :
    R ∈ X.etaleTopology.over T U ↔ ∀ x : (etaleForget X).obj U.left,
      ∃ (V : Over T) (f : V ⟶ U), R f ∧
        ∃ y : (etaleForget X).obj V.left,
          ((etaleForget X).map f.left).base y = x := by
  rw [GrothendieckTopology.mem_over_iff, mem_etaleTopology_iff]
  constructor
  · intro h x
    obtain ⟨V, f, hf, y, hy⟩ := h x
    rw [Sieve.overEquiv_iff] at hf
    exact ⟨Over.mk (f ≫ U.hom), Over.homMk f, hf, y, hy⟩
  · intro h x
    obtain ⟨V, f, hf, y, hy⟩ := h x
    refine ⟨V.left, f.left, ?_, y, hy⟩
    exact ⟨V, f, 𝟙 _, hf, by simp⟩

private instance sliceToEtale_dense {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.EtaleSite) :
    (sliceToEtale X T).IsDenseSubsite (X.etaleTopology.over T)
      (((etaleForget X).obj T).smallEtaleTopology) where
  functorPushforward_mem_iff {U R} := by
    rw [Scheme.mem_smallEtaleTopology_iff, mem_sliceTopology_iff]
    constructor
    · intro h x
      obtain ⟨V, f, hf, y, hy⟩ := h x
      obtain ⟨W, a, b, ha, hab⟩ := hf
      refine ⟨W, a, ha, b.left.base y, ?_⟩
      have hh := congrArg (fun k ↦ k.left.base y) hab
      exact hh.symm.trans hy
    · intro h x
      obtain ⟨V, f, hf, y, hy⟩ := h x
      refine ⟨(sliceToEtale X T).obj V, (sliceToEtale X T).map f,
        ⟨V, f, 𝟙 _, hf, by simp⟩, y, ?_⟩
      exact hy

private instance etaleSliceInverse_dense {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.EtaleSite) :
    (sliceToEtale X T).asEquivalence.inverse.IsDenseSubsite
      (((etaleForget X).obj T).smallEtaleTopology) (X.etaleTopology.over T) where
  functorPushforward_mem_iff {U R} := by
    let e := (sliceToEtale X T).asEquivalence
    rw [← (sliceToEtale X T).functorPushforward_mem_iff
      (X.etaleTopology.over T) (((etaleForget X).obj T).smallEtaleTopology)]
    change (R.functorPushforward e.symm.functor).functorPushforward e.symm.inverse ∈ _ ↔ _
    rw [Sieve.functorPushforward_equivalence_eq_pullback,
      GrothendieckTopology.pullback_mem_iff_of_isIso]
    rfl

/-- Additive sheafification exists on every small étale slice in the section universe.
Source: Stacks Project, Properties of Spaces, Tag 03ED; Modules on Sites, Tag 03DL
(blueprint: def-trf-space-quasi-coherent-module).

Proof: for an étale scheme chart T → X, the localized site X_et/T is equivalent to
T_et: compose an étale T-scheme with T → X, and in the other direction retain the
scheme map to T. Both functors preserve the underlying jointly surjective étale
coverings. The affine étale basis of T has a u-small skeleton and u-small covering
refinements. The two additive plus constructions on this basis therefore have
u-small section groups and give additive sheafification. Transfer along the basis
and the slice equivalence gives the asserted weak sheafification. -/
@[instance] theorem etaleModuleOverHasWeakSheafify
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite) :
    HasWeakSheafify (X.etaleTopology.over T) AddCommGrpCat.{u} := by
  have : HasSheafify (X.etaleTopology.over T) AddCommGrpCat.{u} :=
    (sliceToEtale X T).asEquivalence.hasSheafify (X.etaleTopology.over T)
      (((etaleForget X).obj T).smallEtaleTopology) AddCommGrpCat.{u}
  infer_instance

/-- Additive sheafification on every étale slice inverts exactly locally bijective maps.
Source: Stacks Project, Modules on Sites, Tag 03DL; Sites, sheafification
(blueprint: def-trf-space-quasi-coherent-module).

Proof: use the u-small affine étale basis of the chart scheme as in
etaleModuleOverHasWeakSheafify. A locally bijective map induces an isomorphism after
two plus constructions: local representatives give surjectivity and local equality
gives injectivity. Conversely, the sheafification units are locally bijective, so
an isomorphism of sheafifications implies local surjectivity and local injectivity
of the original map. Refinement and the equivalence with X_et/T transfer these
claims to the displayed slice topology. -/
@[instance] theorem etaleModuleOverWEqualsLocallyBijective
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite) :
    (X.etaleTopology.over T).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  have : ((sliceToEtale X T).asEquivalence.inverse.sheafPushforwardContinuous
      AddCommGrpCat.{u} (((etaleForget X).obj T).smallEtaleTopology)
        (X.etaleTopology.over T)).IsEquivalence :=
    inferInstanceAs (((sliceToEtale X T).asEquivalence.sheafCongr
      (X.etaleTopology.over T) (((etaleForget X).obj T).smallEtaleTopology)
        AddCommGrpCat.{u}).functor.IsEquivalence)
  exact GrothendieckTopology.WEqualsLocallyBijective.transport (X.etaleTopology.over T)
    (((etaleForget X).obj T).smallEtaleTopology)
    (sliceToEtale X T).asEquivalence.inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

/-- The full subcategory of modules locally presented by arbitrary coproducts of the ring.
Source: Stacks Project, Modules on Sites, Tag 03DL; Properties of Spaces, Tags 03G9 and 03M0
(blueprint: def-trf-space-quasi-coherent-module). -/
abbrev QCoh {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (SheafOfModules.isQuasicoherent X.structureSheaf).FullSubcategory

end

end AlgebraicGeometry.AlgebraicSpace
