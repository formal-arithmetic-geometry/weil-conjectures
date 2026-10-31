/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChartwiseEtalePermanence
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.PresheafFieldLiftFamilyCalculus
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# Scheme density in the enlarged étale site

Source: Stacks Project, Properties of Spaces, Tags 03G0, 03G1 and the proof of 03G2;
chartwise convention Tag 03FR (blueprint: lem-trf-space-enlarged-site-scheme-density).

All sites, coverings, scheme objects and restriction functors are the published
constructions. The pullback clause also specifies the underlying sheaf pullback square.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

-- Forget to the actual presheaves, retaining their pullback universal properties.
private def densityForget {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.EnlargedEtaleSite ⥤ (Over S)ᵒᵖ ⥤ Type u :=
  ObjectProperty.ι _ ⋙ Over.forget X ⋙ ObjectProperty.ι _ ⋙ sheafToPresheaf _ _

private instance densityForget_faithful {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (densityForget X).Faithful := by
  unfold densityForget
  infer_instance

private instance densityForget_reflects {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ReflectsLimitsOfShape WalkingCospan (densityForget X) := by
  unfold densityForget
  infer_instance

private theorem density_chartwise {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T U : X.EnlargedEtaleSite} (f : T ⟶ U) : IsChartwiseEtale f.hom.left :=
  chartwise_etale_permanence.{u, 0, 0}.2.2.2.2.1 _ _ _ T.obj.hom U.obj.hom
    f.hom.left T.property U.property f.hom.w

private theorem density_cover_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type v} (U : X.EnlargedEtaleSite) (T : I → X.EnlargedEtaleSite)
    (f : ∀ i, T i ⟶ U) :
    Presieve.ofArrows T f ∈ X.enlargedEtalePrecoverage U ↔
      IsJointlySurjective (fun i ↦ (f i).hom.left.hom.hom) := by
  constructor
  · intro h K _ s x
    obtain ⟨⟨⟨V, a⟩, ha⟩, L, hL, e, y, hy⟩ := h.2 K s x
    obtain ⟨i⟩ := ha
    exact ⟨i, L, hL, e, y, hy⟩
  · intro h
    refine ⟨fun _ a _ ↦ density_chartwise a, ?_⟩
    intro K _ s x
    obtain ⟨i, L, hL, e, y, hy⟩ := h K s x
    exact ⟨⟨⟨T i, f i⟩, ⟨i⟩⟩, L, hL, e, y, hy⟩

private theorem density_terminal {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ T : X.EnlargedEtaleSite, T.obj = Over.mk (𝟙 X) ∧ Nonempty (IsTerminal T) := by
  let T : X.EnlargedEtaleSite := ⟨Over.mk (𝟙 X), chartwise_etale_permanence.{u, 0, 0}.2.1 X⟩
  refine ⟨T, rfl, ⟨IsTerminal.ofUniqueHom
    (fun U ↦ ObjectProperty.homMk (Over.homMk U.obj.hom (by simp [T]))) ?_⟩⟩
  intro U f
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simpa [T] using f.hom.w

private theorem density_pullbacks {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T U V : X.EnlargedEtaleSite) (f : T ⟶ V) (g : U ⟶ V) :
    ∃ (P : X.EnlargedEtaleSite) (p : P ⟶ T) (q : P ⟶ U),
      IsPullback p q f g ∧
      IsPullback p.hom.left.hom q.hom.left.hom f.hom.left.hom g.hom.left.hom := by
  have hf : IsChartwiseEtale f.hom.left :=
    chartwise_etale_permanence.{u, 0, 0}.2.2.2.2.1 _ _ _ T.obj.hom V.obj.hom f.hom.left
      T.property V.property f.hom.w
  let A := enlargedFibreProduct g.hom.left f.hom.left
  let a : A ⟶ U.obj.left := enlargedFibreProductFst g.hom.left f.hom.left
  let b : A ⟶ T.obj.left := ObjectProperty.homMk
    (Limits.pullback.snd g.hom.left.hom f.hom.left.hom)
  have ha : IsChartwiseEtale a :=
    chartwise_etale_permanence.{u, 0, 0}.2.2.2.1 _ _ _ _ _ hf
  let P : X.EnlargedEtaleSite := ⟨Over.mk (a ≫ U.obj.hom),
    chartwise_etale_permanence.{u, 0, 0}.2.2.1 _ _ _ _ _ ha U.property⟩
  have hab : b ≫ f.hom.left = a ≫ g.hom.left := by
    apply ObjectProperty.hom_ext
    exact (Limits.pullback.condition (f := g.hom.left.hom) (g := f.hom.left.hom)).symm
  let p : P ⟶ T := ObjectProperty.homMk (Over.homMk b (by
    change b ≫ T.obj.hom = a ≫ U.obj.hom
    rw [← f.hom.w, ← g.hom.w, ← Category.assoc, ← Category.assoc, hab]))
  let q : P ⟶ U := ObjectProperty.homMk (Over.homMk a rfl)
  have sq : IsPullback p.hom.left.hom q.hom.left.hom
      f.hom.left.hom g.hom.left.hom :=
    (IsPullback.of_hasPullback g.hom.left.hom f.hom.left.hom).flip
  refine ⟨P, p, q, ?_, ?_⟩
  · apply IsPullback.of_map_of_faithful (densityForget X)
    exact (sheafToPresheaf _ _).map_isPullback sq
  · exact sq

private instance densityForget_preserves {S : Scheme.{u}} (X : AlgebraicSpace S) :
    PreservesLimitsOfShape WalkingCospan (densityForget X) := by
  apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro T U V f g _
  obtain ⟨P, p, q, h, hs⟩ := density_pullbacks X T U V f g
  exact ⟨P, p, q, h, (sheafToPresheaf _ _).map_isPullback hs⟩

private theorem density_cover_pullback {S : Scheme.{u}} (X : AlgebraicSpace S)
    {I : Type v} {U V : X.EnlargedEtaleSite} {T P : I → X.EnlargedEtaleSite}
    (f : ∀ i, T i ⟶ U) (g : V ⟶ U) (p : ∀ i, P i ⟶ V) (q : ∀ i, P i ⟶ T i)
    (h : ∀ i, IsPullback (p i) (q i) g (f i))
    (hf : Presieve.ofArrows T f ∈ X.enlargedEtalePrecoverage U) :
    Presieve.ofArrows P p ∈ X.enlargedEtalePrecoverage V := by
  apply (density_cover_iff V P p).2
  intro K _ s x
  obtain ⟨i, L, hL, e, y, hy⟩ := (density_cover_iff U T f).1 hf K s
    (g.hom.left.hom.hom.app _ x)
  let r : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ Over.mk s :=
    Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
  have heq : g.hom.left.hom.hom.app _ (V.obj.left.obj.obj.map r.op x) =
      (f i).hom.left.hom.hom.app _ y := by
    rw [hy]
    exact ConcreteCategory.congr_hom (g.hom.left.hom.hom.naturality r.op) x
  have sq := ((h i).map (densityForget X)).app
    (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))
  obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback sq _ _ heq
  exact ⟨i, L, hL, e, z, hz⟩

private theorem density_site {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.enlargedEtalePrecoverage.IsSiteForCoverings := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · intro U V f hf
    have h := (presheaf_field_lift_family_calculus.{u, 0, 0} S).1 _ _
      ((densityForget X).mapIso (asIso f))
    simpa only [Presieve.ofArrows_of_unique] using
      (density_cover_iff V (fun _ : Unit ↦ U) (fun _ ↦ f)).2 h
  · intro U R T hR hT
    refine ⟨fun _ a _ ↦ density_chartwise a, ?_⟩
    let J (a : R.uncurry) : Type (u + 1) := (T a.1.2 a.2).uncurry
    have h := (presheaf_field_lift_family_calculus S).2.1 R.uncurry J
      U.obj.left.obj.obj (fun a ↦ a.1.1.obj.left.obj.obj)
      (fun a b ↦ b.1.1.obj.left.obj.obj)
      (fun a ↦ a.1.2.hom.left.hom.hom)
      (fun a b ↦ b.1.2.hom.left.hom.hom) hR.2
      (fun a ↦ (hT a.1.1 a.1.2 a.2).2)
    intro K _ s x
    obtain ⟨⟨a, b⟩, L, hL, e, y, hy⟩ := h K s x
    refine ⟨⟨⟨b.1.1, b.1.2 ≫ a.1.2⟩, ?_⟩, L, hL, e, y, hy⟩
    exact ⟨a.1.1, b.1.2, a.1.2, a.2, b.2, rfl⟩
  · intro I U T f hf V g
    choose P p q hp hq using fun i ↦ density_pullbacks X V (T i) U g (f i)
    exact ⟨P, p, q, hp, density_cover_pullback X f g p q hp hf⟩

private def density_fullyFaithful {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (enlargedSchemeInclusion X).FullyFaithful where
  preimage {U V} f := ObjectProperty.homMk (CostructuredArrow.homMk
    (Yoneda.fullyFaithful.preimage f.hom.left.hom.hom) (by
      rw [Yoneda.fullyFaithful.map_preimage]
      exact congrArg (fun k ↦ k.hom.hom) f.hom.w))
  map_preimage f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Sheaf.hom_ext
    exact Yoneda.fullyFaithful.map_preimage _
  preimage_map f := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact Yoneda.fullyFaithful.preimage_map _

-- A point over a field supplies an extension and a map from its residue-field spectrum.
private theorem density_field_point {K : Type u} [Field K]
    (T : Scheme.{u}) (f : T ⟶ Spec (CommRingCat.of K)) (t : T) :
    ∃ (L : Type u) (_ : Field L) (e : K →+* L) (a : Spec (CommRingCat.of L) ⟶ T),
      a ≫ f = Spec.map (CommRingCat.ofHom e) := by
  obtain ⟨e, he⟩ := Spec.map_surjective (T.fromSpecResidueField t ≫ f)
  exact ⟨T.residueField t, inferInstance, e.hom, T.fromSpecResidueField t, he.symm⟩

private theorem density_surjective_lifts {S : Scheme.{u}}
    {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) (hf : IsSurjective f) :
    IsJointlySurjective (fun _ : Unit ↦ f) := by
  intro K _ s x
  let a : yoneda.obj (Over.mk s) ⟶ F := yonedaEquiv.symm x
  obtain ⟨U, p, q, sq, hp⟩ := hf (Over.mk s) a
  let := hp
  obtain ⟨t, _⟩ := p.left.surjective (default : Spec (CommRingCat.of K))
  obtain ⟨L, hL, e, b, hb⟩ := density_field_point U.left p.left t
  let y : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ U :=
    Over.homMk b (by
      change b ≫ U.hom = Spec.map (CommRingCat.ofHom e) ≫ s
      rw [← p.w, ← Category.assoc, hb]
      rfl)
  let r : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ Over.mk s :=
    Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
  have hy : y ≫ p = r := by
    apply Over.OverMorphism.ext
    exact hb
  refine ⟨(), L, hL, e, q.app _ y, ?_⟩
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app sq.w
      (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))) y
  change f.app _ (q.app _ y) = a.app _ (y ≫ p) at h
  rw [hy] at h
  exact h

private theorem density_scheme_points {S : Scheme.{u}} {I : Type v}
    (T : Over S) (U : I → Over S) (f : ∀ i, U i ⟶ T) :
    IsJointlySurjective (fun i ↦ yoneda.map (f i)) ↔
      ∀ x : T.left, ∃ (i : I) (y : (U i).left), (f i).left y = x := by
  constructor
  · intro h x
    let s := T.left.fromSpecResidueField x ≫ T.hom
    let a : Over.mk s ⟶ T := Over.homMk (T.left.fromSpecResidueField x) rfl
    obtain ⟨i, L, hL, e, y, hy⟩ := h (T.left.residueField x) s a
    refine ⟨i, y.left (default : Spec (CommRingCat.of L)), ?_⟩
    have he := congrArg (fun k ↦ k.left (default : Spec (CommRingCat.of L))) hy
    change (f i).left (y.left (default : Spec (CommRingCat.of L))) =
      T.left.fromSpecResidueField x
      ((Spec.map (CommRingCat.ofHom e)) default) at he
    simpa only [Scheme.fromSpecResidueField_apply] using he
  · intro h K _ s x
    obtain ⟨i, y, hy⟩ := h (x.left (default : Spec (CommRingCat.of K)))
    let P := Limits.pullback (f i).left x.left
    obtain ⟨t, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (f i).left) (g := x.left) y
      (default : Spec (CommRingCat.of K)) hy
    obtain ⟨L, hL, e, b, hb⟩ := density_field_point P
      (Limits.pullback.snd (f i).left x.left) t
    let a : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ U i :=
      Over.homMk (b ≫ Limits.pullback.fst (f i).left x.left) (by
        change (b ≫ Limits.pullback.fst _ _) ≫ (U i).hom =
          Spec.map (CommRingCat.ofHom e) ≫ s
        rw [← (f i).w]
        simp only [Category.assoc]
        rw [Limits.pullback.condition_assoc, x.w, ← Category.assoc, hb]
        rfl)
    refine ⟨i, L, hL, e, a, ?_⟩
    apply Over.OverMorphism.ext
    change (b ≫ Limits.pullback.fst _ _) ≫ (f i).left =
      Spec.map (CommRingCat.ofHom e) ≫ x.left
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hb]

private theorem density_scheme_etale {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : X.EtaleSite} (f : U ⟶ V) : Etale f.hom.left.left :=
  representable_etale_scheme_tests.2.2.2.2.2.2.2.2.2 X U.obj.left V.obj.left
    U.obj.hom V.obj.hom f.hom.left U.property V.property f.hom.w

private theorem density_cover_agreement {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : X.EtaleSite) (R : Presieve U) :
    R ∈ X.etalePrecoverage U ↔
      R.map (enlargedSchemeInclusion X) ∈
        X.enlargedEtalePrecoverage ((enlargedSchemeInclusion X).obj U) := by
  obtain ⟨I, V, a, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows, density_cover_iff]
  change _ ↔ IsJointlySurjective (fun i ↦ yoneda.map (a i).hom.left)
  rw [density_scheme_points]
  constructor
  · intro h x
    obtain ⟨W, f, ⟨i⟩, y, hy⟩ := h.2 x
    exact ⟨i, y, hy⟩
  · intro h
    refine ⟨fun _ f _ ↦ density_scheme_etale f, ?_⟩
    intro x
    obtain ⟨i, y, hy⟩ := h x
    exact ⟨V i, a i, ⟨i⟩, y, hy⟩

private theorem density_small_pullback {S : Scheme.{u}} (X : AlgebraicSpace S)
    {U V T : X.EtaleSite} (a : U ⟶ T) (b : V ⟶ T) :
    ∃ (W : X.EtaleSite) (p : W ⟶ U) (q : W ⟶ V),
      IsPullback p q a b ∧
      IsPullback ((enlargedSchemeInclusion X).map p)
        ((enlargedSchemeInclusion X).map q)
        ((enlargedSchemeInclusion X).map a) ((enlargedSchemeInclusion X).map b) := by
  let P := Limits.pullback a.hom.left b.hom.left
  let p : P ⟶ U.obj.left := Limits.pullback.fst _ _
  let q : P ⟶ V.obj.left := Limits.pullback.snd _ _
  have hq : Etale q.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback a.hom.left b.hom.left).map (Over.forget S))
    (density_scheme_etale a)
  have hqe : IsEtale (yoneda.map q) :=
    (representable_etale_scheme_tests.2.2.2.2.2.2.2.1 _ _ q).2 hq
  let W : X.EtaleSite := ⟨CostructuredArrow.mk (yoneda.map q ≫ V.obj.hom),
    isEtale_comp _ _ hqe V.property⟩
  let p' : W ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk p (by
    dsimp [p, q, W]
    rw [← CostructuredArrow.w a.hom, ← CostructuredArrow.w b.hom,
      ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      Limits.pullback.condition]))
  let q' : W ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk q (by rfl))
  have hi : IsPullback ((enlargedSchemeInclusion X).map p')
      ((enlargedSchemeInclusion X).map q')
      ((enlargedSchemeInclusion X).map a) ((enlargedSchemeInclusion X).map b) := by
    apply IsPullback.of_map_of_faithful (densityForget X)
    exact (IsPullback.of_hasPullback a.hom.left b.hom.left).map yoneda
  have := (density_fullyFaithful X).faithful
  have := (density_fullyFaithful X).full
  exact ⟨W, p', q', hi.of_map_of_faithful (enlargedSchemeInclusion X), hi⟩

private theorem density_continuous {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (enlargedSchemeInclusion X).IsContinuous X.etaleTopology X.enlargedEtaleTopology := by
  let : ∀ {U V T : X.EtaleSite} {a : U ⟶ T} {b : V ⟶ T}, HasPullback a b := by
    intro U V T a b
    obtain ⟨P, p, q, h, _⟩ := density_small_pullback X a b
    exact h.hasPullback
  let : HasPullbacks X.EtaleSite := hasPullbacks_of_hasLimit_cospan _
  let : PreservesLimitsOfShape WalkingCospan (enlargedSchemeInclusion X) := by
    apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
    intro U V T a b _
    exact density_small_pullback X a b
  refine ⟨fun G ↦ ?_⟩
  rw [X.etalePrecoverage.isSheaf_toGrothendieck_iff]
  intro U V b R hR
  obtain ⟨I, T, a, rfl⟩ := R.exists_eq_ofArrows
  choose P p q hp hi using fun i ↦ density_small_pullback X b (a i)
  have hc : Presieve.ofArrows P p ∈ X.etalePrecoverage V := by
    apply (density_cover_agreement X V _).2
    rw [Presieve.map_ofArrows]
    exact density_cover_pullback X _ _ _ _ hi (by
      simpa only [Presieve.map_ofArrows] using (density_cover_agreement X U _).1 hR)
  rw [← Sieve.ofArrows, ← Sieve.ofArrows_eq_pullback_of_isPullback a hp,
    Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate]
  let : (enlargedSchemeInclusion X).PreservesPairwisePullbacks (Presieve.ofArrows P p) :=
    ⟨fun _ _ _ _ _ _ ↦ inferInstance⟩
  apply (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks
    (enlargedSchemeInclusion X) G.obj _).2
  exact ((isSheaf_iff_isSheaf_of_type _ _).1 G.property).isSheafFor_of_mem_precoverage
    ((density_cover_agreement X V _).1 hc)

private theorem density_atlas {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.EnlargedEtaleSite) :
    ∃ (W : X.EtaleSite) (a : (enlargedSchemeInclusion X).obj W ⟶ T),
      IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom ∧
      Presieve.singleton a ∈ X.enlargedEtalePrecoverage T := by
  obtain ⟨U, a, he, hs⟩ := T.obj.left.property.2
  let W : X.EtaleSite := ⟨CostructuredArrow.mk (a ≫ T.obj.hom.hom.hom),
    T.property U a he⟩
  let p : (enlargedSchemeInclusion X).obj W ⟶ T :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk ⟨a⟩) rfl)
  refine ⟨W, p, he, hs, ?_⟩
  have h := (density_cover_iff T (fun _ : Unit ↦ (enlargedSchemeInclusion X).obj W)
    (fun _ ↦ p)).2 (density_surjective_lifts a hs)
  simpa only [Presieve.ofArrows_of_unique] using h

private theorem density_refinement {S : Scheme.{u}} (X : AlgebraicSpace S)
    (I : Type v) (U : X.EtaleSite) (T : I → X.EnlargedEtaleSite)
    (f : ∀ i, T i ⟶ (enlargedSchemeInclusion X).obj U)
    (hf : Presieve.ofArrows T f ∈
      X.enlargedEtalePrecoverage ((enlargedSchemeInclusion X).obj U)) :
    ∃ (W : I → X.EtaleSite)
      (a : ∀ i, (enlargedSchemeInclusion X).obj (W i) ⟶ T i)
      (b : ∀ i, W i ⟶ U),
      (∀ i, IsEtale (a i).hom.left.hom.hom ∧ IsSurjective (a i).hom.left.hom.hom) ∧
      (∀ i, (enlargedSchemeInclusion X).map (b i) = a i ≫ f i) ∧
      Presieve.ofArrows W b ∈ X.etalePrecoverage U := by
  choose W a he hs hc using fun i ↦ density_atlas X (T i)
  let b (i : I) : W i ⟶ U := (density_fullyFaithful X).preimage (a i ≫ f i)
  have hb (i : I) : (enlargedSchemeInclusion X).map (b i) = a i ≫ f i :=
    (density_fullyFaithful X).map_preimage _
  refine ⟨W, a, b, fun i ↦ ⟨he i, hs i⟩, hb, ?_⟩
  apply (density_cover_agreement X U _).2
  rw [Presieve.map_ofArrows, density_cover_iff]
  have h := (presheaf_field_lift_family_calculus S).2.1 I (fun _ ↦ Unit)
    ((enlargedSchemeInclusion X).obj U).obj.left.obj.obj
    (fun i ↦ (T i).obj.left.obj.obj)
    (fun i _ ↦ ((enlargedSchemeInclusion X).obj (W i)).obj.left.obj.obj)
    (fun i ↦ (f i).hom.left.hom.hom) (fun i _ ↦ (a i).hom.left.hom.hom)
    ((density_cover_iff _ T f).1 hf) (fun i ↦ density_surjective_lifts _ (hs i))
  intro K _ s x
  obtain ⟨⟨i, _⟩, L, hL, e, y, hy⟩ := h K s x
  refine ⟨i, L, hL, e, y, ?_⟩
  change ((enlargedSchemeInclusion X).map (b i)).hom.left.hom.hom.app _ y = _
  rw [hb]
  exact hy

-- The generated topology adds no covering sieves without actual covering refinements.
private theorem density_covering_refinement {S : Scheme.{u}} (X : AlgebraicSpace S)
    {U : X.EnlargedEtaleSite} {R : Sieve U} (hR : R ∈ X.enlargedEtaleTopology U) :
    ∃ Q ∈ X.enlargedEtalePrecoverage U, Q ≤ R.arrows := by
  classical
  have hJ := density_site X
  have : X.enlargedEtalePrecoverage.HasIsos := hJ.1
  induction hR with
  | of U Q hQ => exact ⟨Q, hQ, Sieve.le_generate Q⟩
  | top U =>
    exact ⟨Presieve.singleton (𝟙 U),
      Precoverage.mem_coverings_of_isIso (𝟙 U), by simp⟩
  | pullback U R hR V f ih =>
    obtain ⟨Q, hQ, hle⟩ := ih
    obtain ⟨I, T, a, rfl⟩ := Q.exists_eq_ofArrows
    obtain ⟨P, p, q, hp, hc⟩ := hJ.2.2 I U T a hQ V f
    refine ⟨Presieve.ofArrows P p, hc, ?_⟩
    rintro W b ⟨i⟩
    change R (p i ≫ f)
    rw [(hp i).w]
    exact R.downward_closed (hle _ _ ⟨i⟩) (q i)
  | transitive U R Q hR hQ ihR ihQ =>
    obtain ⟨T, hT, hle⟩ := ihR
    have hh : ∀ (V : X.EnlargedEtaleSite) (a : V ⟶ U) (_ : T a),
        ∃ P ∈ X.enlargedEtalePrecoverage V, P ≤ (Q.pullback a).arrows := by
      intro V a ha
      exact ihQ (hle _ _ ha)
    choose P hP hPQ using hh
    refine ⟨T.bind (fun {V a} ha ↦ P V a ha),
      hJ.2.1 U T (fun {V} a ha ↦ P V a ha) hT hP, ?_⟩
    rintro W b ⟨V, g, a, ha, hg, rfl⟩
    exact hPQ V a ha _ _ hg

private theorem density_cocontinuous {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (enlargedSchemeInclusion X).IsCocontinuous X.etaleTopology X.enlargedEtaleTopology := by
  constructor
  intro U R hR
  obtain ⟨Q, hQ, hle⟩ := density_covering_refinement X hR
  obtain ⟨I, T, f, rfl⟩ := Q.exists_eq_ofArrows
  obtain ⟨W, a, b, _, hb, hc⟩ := density_refinement X I U T f hQ
  apply X.etaleTopology.superset_covering _ (Precoverage.generate_mem_toGrothendieck hc)
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  change R ((enlargedSchemeInclusion X).map (b i))
  rw [hb i]
  exact R.downward_closed (hle _ _ ⟨i⟩) (a i)

private theorem density_special {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (enlargedSchemeInclusion X).IsSpecialCocontinuousForCoverings
      X.etalePrecoverage X.enlargedEtalePrecoverage := by
  let : (enlargedSchemeInclusion X).Faithful := (density_fullyFaithful X).faithful
  let : X.enlargedEtalePrecoverage.HasIsos := (density_site X).1
  have hid (U : X.EtaleSite) : Presieve.singleton (𝟙 U) ∈ X.etalePrecoverage U := by
    apply (density_cover_agreement X U _).2
    rw [Presieve.map_singleton]
    exact Precoverage.mem_coverings_of_isIso _
  refine ⟨density_cocontinuous X, ?_, ?_, ?_, ?_, ?_⟩
  · intro U R hR
    exact (density_cover_agreement X U R).1 hR
  · intro T U V R hR a b ha
    obtain ⟨P, p, q, h, hi⟩ := density_small_pullback X a b
    exact h.preservesLimit_cospan_iff.mpr hi
  · intro U V a b hab
    have heq : a = b := (enlargedSchemeInclusion X).map_injective hab
    exact ⟨Presieve.singleton (𝟙 U), hid U, fun _ _ _ ↦ by rw [heq]⟩
  · intro U V c
    refine ⟨Presieve.singleton (𝟙 U), hid U, ?_⟩
    rintro W f ⟨⟩
    exact ⟨(density_fullyFaithful X).preimage c, by
      rw [(enlargedSchemeInclusion X).map_id U, Category.id_comp]
      exact (density_fullyFaithful X).map_preimage c⟩
  · intro T
    obtain ⟨W, a, _, _, ha⟩ := density_atlas X T
    refine ⟨PUnit, fun _ ↦ W, fun _ ↦ a, ?_⟩
    simpa only [Presieve.ofArrows_pUnit] using ha

private theorem density_denseSubsite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (enlargedSchemeInclusion X).IsDenseSubsite X.etaleTopology X.enlargedEtaleTopology := by
  let F := enlargedSchemeInclusion X
  let : F.Full := (density_fullyFaithful X).full
  let : F.Faithful := (density_fullyFaithful X).faithful
  let : F.IsContinuous X.etaleTopology X.enlargedEtaleTopology := density_continuous X
  let : F.IsCocontinuous X.etaleTopology X.enlargedEtaleTopology := density_cocontinuous X
  let : F.IsCoverDense X.enlargedEtaleTopology :=
    F.isCoverDense_of_generate_singleton_functor_π_mem _ (by
      intro T
      obtain ⟨W, a, _, _, ha⟩ := density_atlas X T
      exact ⟨W, a, Precoverage.generate_mem_toGrothendieck ha⟩)
  refine { functorPushforward_mem_iff := ?_ }
  intro U R
  constructor
  · intro hR
    have h := F.cover_lift X.etaleTopology X.enlargedEtaleTopology hR
    rwa [Sieve.functorPullback_functorPushforward_eq] at h
  · exact (CoverPreserving.of_isContinuous F _ _).cover_preserve

/-- The enlarged étale coverings form a site with terminal object `X/X` and sheaf
pullbacks. Scheme coverings agree in both sites, and scheme inclusion is fully faithful,
continuous and special cocontinuous. Scheme atlases refine arbitrary covers and give
singleton covers of all objects. Literal restriction is an equivalence on set sheaves.
Source: Stacks, Tags 03G0, 03G1, proof of 03G2, and 03FR
(blueprint: lem-trf-space-enlarged-site-scheme-density).

Proof, following the eight steps of the node:
1. Apply chartwise_etale_permanence for isomorphisms, composition, arbitrary base
   change and cancellation. These prove the three covering axioms. The identity of X
   is terminal. fibreProduct_isAlgebraicSpace and cancellation produce pullbacks over X
   with their actual sheaf universal property. Terminal objects and pullbacks give
   finite limits (lem-weil-pbc-finite-limits-from-terminal-pullbacks).
2. Scheme point covers agree with field-point-class covers. Evaluate a lifted
   residue-field map to recover a point in the covering image. Conversely, form the
   scheme pullback of a covering arrow along the prescribed field-valued map.
   A compatible pair of points lifts to this pullback; the residue field of that
   point gives the required extension and lift. representable_etale_scheme_tests
   gives étaleness of all small-site arrows.{u, 0, 0}.
3. Scheme inclusion uses schemeSpace, the actual Yoneda sheaf. Yoneda full
   faithfulness restricts to the same over-X equations, giving full faithfulness.
4. Scheme fibre products represent the corresponding sheaf fibre products
   (def-pc-fibre-product). The covering agreement in step 2 gives continuity.
5. Choose a surjective representable étale scheme atlas of any enlarged object
   (def-trf-algebraic-space). Chartwise étaleness of its structure map makes the
   composite a small-site object. A scheme-test pullback of the atlas over Spec K
   has a point, whose residue field gives a lift of the prescribed section. Thus
   the atlas is a singleton enlarged covering.
6. For a covering of a scheme object, choose these atlases for each member. Cover
   composition gives an enlarged covering, hence a small-site covering by step 2.
   These composites refine the original family with its same index set, including
   the empty family. This proves cocontinuity.
7. Full faithfulness supplies local equality and local lifting using identity covers.
   Together with steps 4--6 these are all five special cocontinuity conditions
   (def-weil-pbc-special-cocontinuous-functor).
8. The same full faithfulness, continuity, cocontinuity and singleton covering
   density give Mathlib's IsDenseSubsite. Apply its restriction equivalence in the
   displayed coefficient universe. This is the sieve form of the same comparison
   theorem and its restriction functor is definitionally enlargedRestriction. -/
theorem enlargedSite_scheme_density {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.enlargedEtalePrecoverage.IsSiteForCoverings ∧
    (∃ T : X.EnlargedEtaleSite, T.obj = Over.mk (𝟙 X) ∧ Nonempty (IsTerminal T)) ∧
    (∀ (T U V : X.EnlargedEtaleSite) (f : T ⟶ V) (g : U ⟶ V),
      ∃ (P : X.EnlargedEtaleSite) (p : P ⟶ T) (q : P ⟶ U),
        IsPullback p q f g ∧
        IsPullback p.hom.left.hom q.hom.left.hom f.hom.left.hom g.hom.left.hom) ∧
    Nonempty (HasFiniteLimits X.EnlargedEtaleSite) ∧
    (∀ (U : X.EtaleSite) (R : Presieve U),
      R ∈ X.etalePrecoverage U ↔
        R.map (enlargedSchemeInclusion X) ∈
          X.enlargedEtalePrecoverage ((enlargedSchemeInclusion X).obj U)) ∧
    Nonempty (enlargedSchemeInclusion X).FullyFaithful ∧
    (enlargedSchemeInclusion X).IsContinuous X.etaleTopology X.enlargedEtaleTopology ∧
    (∀ (I : Type v) (U : X.EtaleSite) (T : I → X.EnlargedEtaleSite)
      (f : ∀ i : I, T i ⟶ (enlargedSchemeInclusion X).obj U),
      Presieve.ofArrows T f ∈
        X.enlargedEtalePrecoverage ((enlargedSchemeInclusion X).obj U) →
      ∃ (W : I → X.EtaleSite)
        (a : ∀ i : I, (enlargedSchemeInclusion X).obj (W i) ⟶ T i)
        (b : ∀ i : I, W i ⟶ U),
        (∀ i : I, IsEtale (a i).hom.left.hom.hom ∧
          IsSurjective (a i).hom.left.hom.hom) ∧
        (∀ i : I, (enlargedSchemeInclusion X).map (b i) = a i ≫ f i) ∧
        Presieve.ofArrows W b ∈ X.etalePrecoverage U) ∧
    (∀ T : X.EnlargedEtaleSite,
      ∃ (W : X.EtaleSite) (a : (enlargedSchemeInclusion X).obj W ⟶ T),
        IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom ∧
        Presieve.singleton a ∈ X.enlargedEtalePrecoverage T) ∧
    (enlargedSchemeInclusion X).IsSpecialCocontinuousForCoverings
      X.etalePrecoverage X.enlargedEtalePrecoverage ∧
    (enlargedRestriction X (Type (max (u + 1) w))).IsEquivalence := by
  have hsite := density_site X
  obtain ⟨T, hT, ht⟩ := density_terminal X
  let : HasTerminal X.EnlargedEtaleSite := ht.some.hasTerminal
  let : ∀ {U V W : X.EnlargedEtaleSite} {f : U ⟶ W} {g : V ⟶ W},
      HasPullback f g := by
    intro U V W f g
    obtain ⟨P, p, q, h, _⟩ := density_pullbacks X U V W f g
    exact h.hasPullback
  let : HasPullbacks X.EnlargedEtaleSite := hasPullbacks_of_hasLimit_cospan _
  let : (enlargedSchemeInclusion X).IsDenseSubsite
      X.etaleTopology X.enlargedEtaleTopology := density_denseSubsite X
  refine ⟨hsite, ⟨T, hT, ht⟩, density_pullbacks X,
    ⟨hasFiniteLimits_of_hasTerminal_and_pullbacks⟩, density_cover_agreement X,
    ⟨density_fullyFaithful X⟩, density_continuous X, density_refinement X,
    density_atlas X, density_special X, ?_⟩
  unfold enlargedRestriction
  infer_instance

end AlgebraicGeometry.AlgebraicSpace
