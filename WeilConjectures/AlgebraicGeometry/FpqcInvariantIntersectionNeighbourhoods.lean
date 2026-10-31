/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.DescentOrbitSaturated
import WeilConjectures.AlgebraicGeometry.TransportLeftNaturality
import WeilConjectures.AlgebraicGeometry.FlatRelationQcImageIntersections
import WeilConjectures.AlgebraicGeometry.FlatRelationInvariantOpenComplement

/-!
# Invariant neighbourhoods inside intersections of quasi-compact opens

Source: Stacks Project, Groupoids, Tags 03LO, 0APA, 0APB and 0APF; More on Groupoids,
Tag 0APK, the translation to properties (a) and (b).
(blueprint: lem-a1-fpqc-invariant-intersection-neighbourhoods).

The descent datum is the existing transport datum. Its universal transport defines the
relation target on `V ×_S X`. Invariance of an open is expressed as equality in the lattice
of opens of this scheme; invariance of an arbitrary subset is equality of inverse images.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over.DescentDatum

/-- The canonical target `V ×_S X → V` of the relation associated to a descent datum.
It is the `V`-component of `φ : V ×_S X ≅ X ×_S V`, obtained by transporting the universal
point over the first `X`-coordinate to the second `X`-coordinate. This constructs the map
from the given datum, with no choice of a relation or extra compatibility hypothesis.

Source: Stacks Project, Groupoids, Tag 0APF, cartesian groupoid of a descent datum;
More on Groupoids, Tag 0APK, properties (a) and (b).
(blueprint: lem-a1-fpqc-invariant-intersection-neighbourhoods). -/
noncomputable def descentRelationTarget {X S : Scheme.{u}} {p : X ⟶ S} {V : Over X}
    (D : Over.DescentDatum p V) : Limits.pullback (V.hom ≫ p) p ⟶ V.left :=
  (D.transport (Limits.pullback.fst (V.hom ≫ p) p ≫ V.hom) (Limits.pullback.snd (V.hom ≫ p) p)
    (by simpa only [Category.assoc] using (Limits.pullback.condition (f := V.hom ≫ p) (g := p)))
    (Over.homMk (Limits.pullback.fst (V.hom ≫ p) p))).left

/-- Every point of a quasi-separated scheme with descent datum over a flat surjection of
affine schemes has an invariant open neighbourhood contained in an invariant intersection
of a nonempty family of quasi-compact opens. The open equality is in the lattice of opens
of `V ×_S X`, and the second equality concerns only subsets of its underlying space.

Source: Stacks Project, Groupoids, Tags 03LO, 0APA and 0APB, applied via Tag 0APF;
More on Groupoids, Tag 0APK, properties (a) and (b).
(blueprint: lem-a1-fpqc-invariant-intersection-neighbourhoods).

Proof:
1. Set R = V ×_S X, s = pr_V and t = descentRelationTarget D. Since p is a morphism
   between affines, it is affine. Both s and t are affine, quasi-compact and flat by
   lem-weil-pbc-morphism-affine-schemes-affine,
   lem-weil-pbc-affine-morphism-permanence and lem-weil-pbc-flat-morphism-base-change.
   The identity section (id_V, V.hom) has both composites equal to id_V by
   lem-galois-descent-datum-diagonal-identity (the recorded transport_self law).
2. For A a subset of V set sigma(A) = t(s⁻¹(A)). By lem-pd-descent-orbit-saturated,
   each singleton orbit is invariant. Unions give invariance of sigma(A), and the
   identity section gives A contained in sigma(A), including when A is empty.
3. Choose an affine open Q containing v by lem-weil-pbc-affine-opens-basis. It is
   quasi-compact by lem-weil-pbc-affine-scheme-qcqs. The inverse image s⁻¹(Q) is
   quasi-compact by lem-weil-pbc-quasi-compact-morphism-preimage-qc-open, hence its
   continuous image K = sigma(Q) is quasi-compact. Flatness of t and
   lem-weil-pbc-flat-generalizations-lift make K stable under generalization. A finite
   affine covering of K gives a quasi-compact open H with Q contained in K contained in H.
4. Set Z = V minus H and T = sigma(Z). Then Z is contained in T, T is invariant and
   K is disjoint from T. Realize s⁻¹(Z) as a closed subscheme C of R using
   lem-weil-pbc-closed-subset-closed-subscheme. Its composite with t is affine by
   def-weil-closed-immersion and pqf-def-affine-morphism, hence quasi-compact by
   lem-weil-pbc-affine-morphism-permanence. By lem-sc-picard-closure-specialization,
   every point of the closure B of T specializes from a point of T.
5. Lift such generalizations along s and t using lem-weil-pbc-flat-generalizations-lift.
   Invariance of T and continuity prove both inclusions s⁻¹(B) = t⁻¹(B). Generalization
   stability of K makes K disjoint from B. Thus W = V minus B is invariant open and
   v belongs to Q contained in K contained in W contained in H.
6. Put E = sigma(H). It is invariant, contains W, and is quasi-compact and stable under
   generalization by the same inverse-image and flat lifting arguments as in step 3.
   Cover it by a finite union H₂ of affine opens, a quasi-compact open of V.
7. The open H₂ is quasi-separated by lem-weil-pbc-quasi-separated-affine-cover-criterion,
   applied to affine opens of V lying inside H₂. By lem-weil-pbc-qcqs-scheme-spectral it
   is spectral. Apply lem-weil-pbc-spectral-generalizations-of-quasi-compact to E in H₂:
   its generalizations equal E, so E is the intersection of the quasi-compact opens of
   H₂ containing it. This is a set-indexed, nonempty family (it contains H₂), and each
   member is also a quasi-compact open in V.
8. The equalities s⁻¹(W) = t⁻¹(W) and s⁻¹(E) = t⁻¹(E) say exactly that φ sends the
   first inverse image to the second. For W these are equal opens, hence equal open
   subschemes by def-weil-open-immersion; for E only subsets are used. If V is empty,
   the assertion over v is vacuous. -/
theorem exists_fpqc_invariant_intersection_neighbourhood
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (p : X ⟶ S) [Flat p] [Surjective p]
    {V : Over X} [QuasiSeparatedSpace V.left] (D : Over.DescentDatum p V) (v : V.left) :
    ∃ (W : V.left.Opens) (E : Set V.left), v ∈ W ∧ (W : Set V.left) ⊆ E ∧
      (∃ 𝒰 : Set V.left.Opens, 𝒰.Nonempty ∧
        (∀ U ∈ 𝒰, IsCompact (U : Set V.left)) ∧
        E = ⋂ U ∈ 𝒰, (U : Set V.left)) ∧
      Limits.pullback.fst (V.hom ≫ p) p ⁻¹ᵁ W = D.descentRelationTarget ⁻¹ᵁ W ∧
      (Limits.pullback.fst (V.hom ≫ p) p) ⁻¹' E = D.descentRelationTarget ⁻¹' E := by
  classical
  let s := Limits.pullback.fst (V.hom ≫ p) p
  let q := Limits.pullback.snd (V.hom ≫ p) p
  let t := D.descentRelationTarget
  have hsq : IsPullback s q (V.hom ≫ p) p := IsPullback.of_hasPullback _ _
  have hp : (s ≫ V.hom) ≫ p = q ≫ p := by
    simpa only [Category.assoc] using hsq.w
  let a₀ : Over.mk (s ≫ V.hom) ⟶ V := Over.homMk s
  have ht : (D.transport (s ≫ V.hom) q hp a₀).left = t := rfl
  have htq : t ≫ V.hom = q := by
    rw [← ht]
    exact Over.w _
  -- Inversion identifies the target with a base change projection.
  let i := hsq.lift t (s ≫ V.hom) (by
    rw [← Category.assoc, htq]
    exact hp.symm)
  have his : i ≫ s = t := hsq.lift_fst _ _ _
  have hiq : i ≫ q = s ≫ V.hom := hsq.lift_snd _ _ _
  have hit : i ≫ t = s := by
    let b : Over.mk q ⟶ V := Over.homMk t htq
    have hb : D.transport (s ≫ V.hom) q hp a₀ = b := by
      ext
      exact ht
    have hn : (D.transport q (s ≫ V.hom) hp.symm b).left = i ≫ t := by
      rw [← ht]
      apply transport_left_naturality D i (s ≫ V.hom) q hp a₀
      · rw [← Category.assoc, his, htq]
      · exact hiq.symm
      · exact his.symm
    rw [← hn, ← hb, D.transport_transport, D.transport_self]
    rfl
  have hii : i ≫ i = 𝟙 _ := by
    apply hsq.hom_ext
    · simp only [Category.assoc, his, hit, Category.id_comp]
    · rw [Category.assoc, hiq, ← Category.assoc, his, htq, Category.id_comp]
  have : IsIso i := ⟨⟨i, hii, hii⟩⟩
  have : Flat s := by dsimp [s]; infer_instance
  have : IsAffineHom p := isAffineHom_of_isAffine p
  have : IsAffineHom s :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hsq.flip inferInstance
  have : Flat t := by rw [← his]; infer_instance
  have : IsAffineHom t := by rw [← his]; infer_instance
  let e : V.left ⟶ Limits.pullback (V.hom ≫ p) p :=
    Limits.pullback.lift (𝟙 V.left) V.hom (by simp)
  have hes : e ≫ s = 𝟙 V.left := by simp [e, s]
  have heq : e ≫ q = V.hom := by simp [e, q]
  have het : e ≫ t = 𝟙 V.left := by
    have he₁ : V.hom = e ≫ (s ≫ V.hom) := by
      rw [← Category.assoc, hes, Category.id_comp]
    have hn := transport_left_naturality D e (s ≫ V.hom) q hp a₀
      V.hom V.hom rfl (Over.homMk (𝟙 V.left)) he₁ heq.symm hes.symm
    rw [ht] at hn
    simpa only [D.transport_self, Over.homMk_left] using hn.symm
  have hincl : ∀ A : Set V.left, A ⊆ t '' (s ⁻¹' A) := by
    intro A x hx
    have hsx : s (e x) = x := by
      simpa only [Scheme.Hom.comp_apply, Scheme.Hom.id_base, TopCat.id_app] using
        congrArg (fun f : V.left ⟶ V.left ↦ f x) hes
    have htx : t (e x) = x := by
      simpa only [Scheme.Hom.comp_apply, Scheme.Hom.id_base, TopCat.id_app] using
        congrArg (fun f : V.left ⟶ V.left ↦ f x) het
    refine ⟨e x, ?_, htx⟩
    change s (e x) ∈ A
    rwa [hsx]
  have hsat : ∀ A : Set V.left,
      s ⁻¹' (t '' (s ⁻¹' A)) = t ⁻¹' (t '' (s ⁻¹' A)) := by
    intro A
    have hUnion : t '' (s ⁻¹' A) = ⋃ x ∈ A, t '' (s ⁻¹' {x}) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨s r, hr, r, rfl, rfl⟩
      · rintro ⟨x, hx, r, hr, rfl⟩
        exact ⟨r, hr.symm ▸ hx, rfl⟩
    rw [hUnion]
    simp only [Set.preimage_iUnion]
    congr 1
    funext x
    congr 1
    funext _
    exact descent_orbit_saturated D s q t hsq ht x
  obtain ⟨Q, hQ, hvQ, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := V.left) (U := ⊤) (x := v) (by trivial)
  obtain ⟨_, hgen, ⟨H, hH, hKH⟩, _⟩ :=
    flat_relation_qc_image_intersections s t Q hQ.isCompact
  let K : Set V.left := t '' (s ⁻¹' (Q : Set V.left))
  have hKgen : StableUnderGeneralization K := by
    intro x y hyx hx
    exact hgen x hx y hyx.mem_closure
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  obtain ⟨_, _, _, _, _, hWo, hWinv, hKW, hWH⟩ :=
    flat_relation_invariant_open_complement s t e hes het hsat H K hKH
      (hsat Q) hKgen
  let W : V.left.Opens := ⟨_, hWo⟩
  let E : Set V.left := t '' (s ⁻¹' (H : Set V.left))
  obtain ⟨_, _, ⟨H₂, hH₂, hEH₂⟩, hinter⟩ :=
    flat_relation_qc_image_intersections s t H hH
  obtain ⟨hne, hE⟩ := hinter H₂ hH₂ hEH₂
  let 𝒰 : Set V.left.Opens :=
    {U | (U : Set V.left) ⊆ H₂ ∧ IsCompact (U : Set V.left) ∧ E ⊆ U}
  refine ⟨W, E, hKW (hincl Q hvQ), hWH.trans (hincl H), ?_, ?_, hsat H⟩
  · refine ⟨𝒰, ?_, fun U hU ↦ hU.2.1, ?_⟩
    · obtain ⟨U, hU⟩ := hne
      exact ⟨⟨U, hU.2.1⟩, hU.1, hU.2.2⟩
    · change t '' (s ⁻¹' (H : Set V.left)) = _
      rw [hE]
      ext x
      simp only [Set.mem_sInter, Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro hx U hU
        exact hx U ⟨hU.1, U.isOpen, hU.2⟩
      · intro hx U hU
        exact hx ⟨U, hU.2.1⟩ ⟨hU.1, hU.2.2⟩
  · apply TopologicalSpace.Opens.ext
    exact hWinv

end CategoryTheory.Over.DescentDatum
