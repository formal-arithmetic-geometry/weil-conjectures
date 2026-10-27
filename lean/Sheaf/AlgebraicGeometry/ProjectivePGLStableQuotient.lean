/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.PGLLinearizedPolarization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.FiniteGradedProjProjective
import Sheaf.AlgebraicGeometry.PGLInvariantImageRestriction
import Sheaf.AlgebraicGeometry.PGLInvariantSectionFiniteness
import Sheaf.AlgebraicGeometry.PGLSemistableAffineQuotientGluing
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Projective geometric quotients of closed stable PGL loci

Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 1,
Theorem 1.10; Morrison, arXiv:0810.2340, §3.3--3.4
(blueprint: lem-sfb-projective-pgl-stable-quotient).

The quotient scheme is explicitly Proj of the invariant section algebra on the
scheme-theoretic closure, rather than an unspecified scheme with an orbit map.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
private theorem coefficient_proj {k R : Type u} [Field k] [CommRing R]
    (A : ℕ → AddSubgroup R) [GradedRing A] (φ : k →+* A 0)
    (hfg : ((algebraMap (A 0) R).comp φ).FiniteType)
    (hzero : @Module.Finite k (A 0) _ _ φ.toAlgebra.toModule) :
    (∃ d : ℕ, 0 < d ∧ ∀ e : ℕ, 0 < e → ∀ (n : ℕ) (a : R),
      a ∈ A (n * (d * e)) → a ∈ Subring.closure ((A 0 : Set R) ∪ A (d * e))) ∧
    LocallyOfFiniteType (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom φ)) ∧
    QuasiCompact (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom φ)) ∧
    IsHProjective (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom φ)) := by
  let ψ := (algebraMap (A 0) R).comp φ
  let : Algebra k R := ψ.toAlgebra
  let : Algebra k (A 0) := φ.toAlgebra
  let B : ℕ → Submodule k R := fun n ↦
    { A n with
      smul_mem' := by
        intro c a ha
        change (φ c : R) * a ∈ A n
        simpa using SetLike.GradedMul.mul_mem (φ c).property ha }
  let : GradedRing B :=
    { one_mem := SetLike.GradedOne.one_mem (A := A)
      mul_mem := fun _ _ _ _ ha hb ↦ SetLike.GradedMul.mul_mem (A := A) ha hb
      toDecomposition :=
        { decompose' := DirectSum.decompose A
          left_inv := (DirectSum.decompose A).left_inv
          right_inv := (DirectSum.decompose A).right_inv } }
  have : Algebra.FiniteType k R := hfg
  have : Module.Finite k (A 0) := hzero
  let f : A 0 →ₗ[k] B 0 :=
    { toFun := fun x ↦ ⟨x.val, x.property⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have : Module.Finite k (B 0) := Module.Finite.of_surjective f (fun x ↦ ⟨x, rfl⟩)
  obtain ⟨⟨d, hd⟩, hft, hqc, hp⟩ := finite_graded_proj_projective B
  let fromB : B →+*ᵍ A := { RingHom.id R with map_mem := fun ha ↦ ha }
  let toB : A →+*ᵍ B := { RingHom.id R with map_mem := fun ha ↦ ha }
  have hfrom : HomogeneousIdeal.irrelevant A ≤ (HomogeneousIdeal.irrelevant B).map fromB := by
    apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
    intro n hn a ha
    exact Ideal.mem_map_of_mem fromB (HomogeneousIdeal.mem_irrelevant_of_mem B hn ha)
  have hto : HomogeneousIdeal.irrelevant B ≤ (HomogeneousIdeal.irrelevant A).map toB := by
    apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
    intro n hn a ha
    exact Ideal.mem_map_of_mem toB (HomogeneousIdeal.mem_irrelevant_of_mem A hn ha)
  let e : Proj A ≅ Proj B :=
    { hom := Proj.map fromB hfrom
      inv := Proj.map toB hto
      hom_inv_id := by
        rw [← Proj.map_comp]
        exact (Proj.map_congr
          (show fromB.comp toB = .id _ from GradedRingHom.ext fun _ ↦ rfl)
          _ (by simp)).trans Proj.map_id
      inv_hom_id := by
        rw [← Proj.map_comp]
        exact (Proj.map_congr
          (show toB.comp fromB = .id _ from GradedRingHom.ext fun _ ↦ rfl)
          _ (by simp)).trans Proj.map_id }
  have : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  have he : e.hom ≫ Proj.toSpecOfAlgebra B =
      Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom φ) := by
    dsimp only [e, Proj.toSpecOfAlgebra]
    rw [← Category.assoc, Proj.map_toSpecZero]
    simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  refine ⟨⟨d, d.pos, ?_⟩, ?_, ?_, ?_⟩
  · intro m hm
    exact (hd ⟨d * m, Nat.mul_pos d.pos hm⟩ (dvd_mul_right _ _)).1
  · rw [← he]
    have : LocallyOfFiniteType (Proj.toSpecOfAlgebra B) := hft
    exact locallyOfFiniteType_comp e.hom _
  · rw [← he]
    have : QuasiCompact (Proj.toSpecOfAlgebra B) := hqc
    exact quasiCompact_comp e.hom _
  · rw [← he]
    have : IsHProjective (Proj.toSpecOfAlgebra B) := hp
    obtain ⟨ι, hι, j, hj, hbase⟩ := hp.exists_isClosedImmersion
    have : IsClosedImmersion j := hj
    exact ⟨ι, hι, e.hom ≫ j, inferInstance, by rw [Category.assoc, hbase]⟩


namespace PGLLinearization

variable {k : Type u} [Field k] {J Z : Over (Spec (.of k))}

/-- The existing scheme-theoretic image construction, equipped with its
composite structure morphism to Spec k. Source: MFK, Chapter 1, Theorem 1.10,
closed stable-locus consequence
(blueprint: lem-sfb-projective-pgl-stable-quotient). -/
noncomputable abbrev closureOver (j : J ⟶ Z) : Over (Spec (.of k)) :=
  Over.mk (j.left.imageι ≫ Z.hom)

/-- The existing image inclusion as a map over k. Source: MFK, Chapter 1,
Theorem 1.10, closed stable-locus consequence
(blueprint: lem-sfb-projective-pgl-stable-quotient). -/
noncomputable def closureInclusion (j : J ⟶ Z) : closureOver j ⟶ Z :=
  Over.homMk j.left.imageι

section

variable {r : ℕ} {X : Over (Spec (.of k))} {L : X.left.Modules} [L.IsInvertible]

private theorem finiteGeneration (E : Action k r X L)
    (φ : k →+* E.CoefficientRing)
    (hc : ∀ c : k, E.coefficientVal (φ c) = constantSection (Z := X) (L := L) c)
    (hfg : ((algebraMap (E.invariantGrade 0) E.invariantRing).comp φ).FiniteType) :
    E.IsFinitelyGenerated := by
  classical
  let ψ := (algebraMap (E.invariantGrade 0) E.invariantRing).comp φ
  let : Algebra k E.invariantRing := ψ.toAlgebra
  have h : Algebra.FiniteType k E.invariantRing := hfg
  obtain ⟨s, hs⟩ := h.1
  let t := s.image E.invariantRing.subtype
  refine ⟨t, ?_, ?_⟩
  · intro a ha
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
    exact a.property
  · apply le_antisymm
    · apply Subring.closure_le.mpr
      rintro a (⟨c, rfl⟩ | ha)
      · rw [← hc]
        exact (φ c).val.property
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
        exact a.property
    · intro a ha
      let S : Subring (Scheme.Modules.InvertibleSectionRing L) :=
        Subring.closure (Set.range (constantSection (Z := X) (L := L)) ∪ ↑t)
      let B : Subalgebra k E.invariantRing :=
        { S.comap E.invariantRing.subtype with
          algebraMap_mem' := fun c ↦ by
            change E.coefficientVal (φ c) ∈ S
            rw [hc]
            exact Subring.subset_closure (Or.inl ⟨c, rfl⟩) }
      have hb : Algebra.adjoin k (s : Set E.invariantRing) ≤ B := by
        apply Algebra.adjoin_le
        intro a ha
        exact Subring.subset_closure (Or.inr (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
      have : (⟨a, ha⟩ : E.invariantRing) ∈ B := by
        apply hb
        rw [hs]
        trivial
      exact this

end

section

variable {r : ℕ} {X : Over (Spec (.of k))} {L : Z.left.Modules}

private theorem stable_restriction (i : X ⟶ Z) [Mono i]
    (D : Action k r Z L)
    (E : Action k r X ((Scheme.Modules.pullback i.left).obj L))
    (hE : D.IsRestriction i E)
    (hss : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : fieldTest k Ω ⟶ X), E.IsSemistable Ω x ↔ D.IsSemistable Ω (x ≫ i))
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (x : fieldTest k Ω ⟶ X) (hx : D.IsStable Ω (x ≫ i)) : E.IsStable Ω x := by
  obtain ⟨hsem, ⟨C, hC, hpoints⟩, hstab⟩ := hx
  let b : pullback X.hom (fieldTest k Ω).hom ⟶
      pullback Z.hom (fieldTest k Ω).hom :=
    pullback.map _ _ _ _ i.left (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hb (y : fieldTest k Ω ⟶ X) :
      b (geometricImage Ω y) = geometricImage Ω (y ≫ i) := by
    change (pullback.lift y.left (𝟙 _) _ ≫ b)
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) = _
    apply congrArg (fun f : (fieldTest k Ω).left ⟶ _ ↦
      f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω))
    apply pullback.hom_ext <;> simp [b]
  refine ⟨(hss Ω x).mpr hsem, ⟨b ⁻¹' C, hC.preimage b.continuous, ?_⟩, ?_⟩
  · intro y hy
    change _ ↔ b (geometricImage Ω y) ∈ C
    rw [hb, ← hpoints (y ≫ i) ((hss Ω y).mp hy)]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, ((hE _ (fieldMatrix Ω g) x).1).symm.trans (congrArg (· ≫ i) hg)⟩
    · rintro ⟨g, hg⟩
      refine ⟨g, (cancel_mono i).mp ?_⟩
      exact ((hE _ (fieldMatrix Ω g) x).1).trans hg
  · apply hstab.subset
    rintro a ⟨g, hg, rfl⟩
    exact ⟨g, ((hE _ (fieldMatrix Ω g) x).1).symm.trans
      (congrArg (· ≫ i) hg), rfl⟩

end

/-- A closed invariant subscheme of the semistable locus contained in the stable
locus has a projective finite-type geometric quotient, categorical for maps to
all algebraic spaces, given by Proj of the invariant section ring of its closure.
No restriction on the characteristic or on linear reductivity is imposed.
Source: MFK, Chapter 1, Theorem 1.10; arbitrary-characteristic reductivity by
Haboush; Morrison, arXiv:0810.2340, §3.3--3.4
(blueprint: lem-sfb-projective-pgl-stable-quotient).
Proof:
1. Form X = the scheme-theoretic image of J → Z. Its restriction over Z^ss is J.
   The flat-density lemma, lemma-nagata-dense-flat-pullback, shows the action and
   linearization restrict to X: their factorization identities hold on the
   schematically dense G × J in G × X.
2. By lem-sfb-projective-polarization-section-algebra, the section algebras on Z
   and X are finite type with finite-dimensional pieces; restriction is
   surjective in all sufficiently large degrees.
3. Use lem-sfb-pgl-geometric-reductivity to power-lift invariant homogeneous
   sections along those surjections, via symmetric algebras and multiplication.
   This proves X^ss = J, without exactness of taking invariants.
4. The same reductivity theorem makes the invariant section algebra finite
   type. Its degree-zero algebra is finite-dimensional. Apply
   lem-sfb-finite-graded-proj-projective to get the Veronese presentations and
   projectivity over k, even when the constants exceed k.
5. The section-algebra theorem identifies the nonvanishing affine charts X_s
   with Spec S_(s). Invariant localization gives R_(s) = (S_(s))^G: multiply
   an invariant fraction's numerator by a sufficient power of s to kill its
   coaction defect. This also works when s is a zero divisor.
6. Apply lem-sfb-affine-pgl-finite-stabilizer-quotient on every chart. The maps
   glue because the fraction maps agree on X_(st); their inverse images of
   D_+(s) are precisely X_s. They are invariant and surjective.
7. Uniqueness of the affine factorizations glues maps to every algebraic
   space (def-trf-algebraic-space), including nonseparated ones. On geometric
   points the affine orbit bijections glue as well. -/
theorem projective_pgl_stable_quotient
    (r : ℕ) (hr : 1 ≤ r) (Z : Over (Spec (.of k)))
    (hprojective : IsHProjective Z.hom)
    (hfiniteType : LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom)
    (L : Z.left.Modules) [L.IsInvertible] (hample : IsAmple Z.hom L)
    (D : Action k r Z L) (U : Z.left.Opens)
    (hsemistable : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : fieldTest k Ω ⟶ Z),
      x.left.base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) ∈ U ↔ D.IsSemistable Ω x)
    (J : Over (Spec (.of k))) (j : J ⟶ Z) (jU : J.left ⟶ U.toScheme)
    (hclosed : IsClosedImmersion jU) (hfactor : jU ≫ U.ι = j.left)
    (hinvariant : D.IsInvariantSubscheme j)
    (hstable : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : fieldTest k Ω ⟶ J), D.IsStable Ω (x ≫ j)) :
    ∃ E : Action k r (closureOver j)
      ((Scheme.Modules.pullback j.left.imageι).obj L),
      D.IsRestriction (closureInclusion j) E ∧ E.IsFinitelyGenerated ∧
      (∃ d : ℕ, 0 < d ∧ ∀ e : ℕ, 0 < e → E.VeroneseGenerated (d * e)) ∧
      ∃ φ : k →+* E.CoefficientRing,
        (∀ c : k, E.coefficientVal (φ c) =
          constantSection (Z := closureOver j)
            (L := (Scheme.Modules.pullback j.left.imageι).obj L) c) ∧
        ∃ q : J ⟶ E.projOver φ,
          IsHProjective (E.projOver φ).hom ∧
          LocallyOfFiniteType (E.projOver φ).hom ∧ QuasiCompact (E.projOver φ).hom ∧
          Surjective q.left ∧
          (∀ (T : Over (Spec (.of k))) (g : Matrices k r T) (x y : T ⟶ J),
            y ≫ j = D.act T g (x ≫ j) → y ≫ q = x ≫ q) ∧
          (∀ (B : AlgebraicSpace (Spec (.of k))) (f : yoneda.obj J ⟶ B.obj.obj),
            D.IsInvariantMap j B f →
              ∃! a : yoneda.obj (E.projOver φ) ⟶ B.obj.obj, yoneda.map q ≫ a = f) ∧
          (∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω],
            Function.Surjective (fun x : fieldTest k Ω ⟶ J ↦ x ≫ q) ∧
            ∀ x y : fieldTest k Ω ⟶ J,
              (x ≫ q = y ≫ q ↔ ∃ g : Matrix.GeneralLinearGroup (Fin r) Ω,
                D.act _ (fieldMatrix Ω g) (x ≫ j) = y ≫ j)) := by
  classical
  have : IsHProjective Z.hom := hprojective
  have : LocallyOfFiniteType Z.hom := hfiniteType.1
  have : QuasiCompact Z.hom := hfiniteType.2
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : IsClosedImmersion jU := hclosed
  have : IsImmersion j.left := by
    rw [← hfactor]
    infer_instance
  have : TopologicalSpace.NoetherianSpace J.left :=
    j.left.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j.left := inferInstance
  have : IsOpenImmersion j.left.toImage := inferInstance
  let i : J ⟶ closureOver j := Over.homMk j.left.toImage (by
    change j.left.toImage ≫ (j.left.imageι ≫ Z.hom) = J.hom
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, Over.w])
  have hi : i ≫ closureInclusion j = j := by
    apply Over.OverMorphism.ext
    exact j.left.toImage_imageι
  have : IsClosedImmersion (closureInclusion j).left := by
    change IsClosedImmersion j.left.imageι
    infer_instance
  have : Mono (closureInclusion j).left := inferInstance
  have : Mono (closureInclusion j) := Over.mono_of_mono_left _
  have : IsOpenImmersion i.left := by
    change IsOpenImmersion j.left.toImage
    infer_instance
  obtain ⟨E, hE, hss⟩ := invariant_image_restriction r hr Z hprojective hfiniteType
    L hample D J j inferInstance hinvariant (closureOver j) (closureInclusion j)
    inferInstance (by exact Scheme.IdealSheafData.ker_subschemeι j.left.ker)
  change D.IsRestriction (closureInclusion j) E at hE
  have : IsHProjective (closureOver j).hom := by
    obtain ⟨ι, hι, v, hv, hbase⟩ := hprojective.exists_isClosedImmersion
    have : IsClosedImmersion v := hv
    exact ⟨ι, hι, j.left.imageι ≫ v, inferInstance, by
      change (j.left.imageι ≫ v) ≫ _ = j.left.imageι ≫ Z.hom
      rw [Category.assoc, hbase]⟩
  have : LocallyOfFiniteType (closureOver j).hom := locallyOfFiniteType_comp _ _
  have : QuasiCompact (closureOver j).hom := quasiCompact_comp _ _
  have hampleX := hample.pullback j.left.imageι
  have hclosedRange : IsClosed (U.ι ⁻¹' Set.range j.left) := by
    have heq : U.ι ⁻¹' Set.range j.left = Set.range jU := by
      rw [← hfactor, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.preimage_image_eq _ U.ι.isOpenEmbedding.injective]
    rw [heq]
    exact jU.isClosedEmbedding.isClosed_range
  have hssJ : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : fieldTest k Ω ⟶ closureOver j),
      E.IsSemistable Ω x ↔ ∃ y : fieldTest k Ω ⟶ J, y ≫ i = x := by
    intro Ω _ _ _ x
    rw [hss Ω x]
    constructor
    · intro hx
      have hxU := (hsemistable Ω (x ≫ closureInclusion j)).mpr hx
      have hrange : Set.range x.left ⊆ Set.range j.left.toImage := by
        rintro z ⟨t, rfl⟩
        have ht : t = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) := by
          apply PrimeSpectrum.ext
          exact Ideal.eq_bot_of_prime t.asIdeal
        subst t
        exact j.left.preimage_subset_range_toImage_of_isClosed hclosedRange hxU
      let y : (fieldTest k Ω).left ⟶ J.left :=
        IsOpenImmersion.lift j.left.toImage x.left hrange
      have hy : y ≫ j.left.toImage = x.left := IsOpenImmersion.lift_fac _ _ _
      let y' : fieldTest k Ω ⟶ J := Over.homMk y (by
        rw [← Over.w i, ← Category.assoc]
        change (y ≫ j.left.toImage) ≫ _ = _
        rw [hy, Over.w])
      exact ⟨y', Over.OverMorphism.ext hy⟩
    · rintro ⟨y, rfl⟩
      simpa only [Category.assoc, hi] using (hstable Ω y).1
  have hstableX : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : fieldTest k Ω ⟶ J), E.IsStable Ω (x ≫ i) := by
    intro Ω _ _ _ x
    apply stable_restriction (closureInclusion j) D E hE hss Ω (x ≫ i)
    simpa only [Category.assoc, hi] using hstable Ω x
  obtain ⟨φ, hc, hfg, hzero⟩ := invariant_section_finiteness r hr (closureOver j)
    inferInstance ⟨inferInstance, inferInstance⟩ _ hampleX E
  have halg := coefficient_proj E.invariantGrade φ hfg hzero
  obtain ⟨q, hqsurj, hqinv, hqcat, hqgeom⟩ := semistable_affine_quotient_gluing r hr
    (closureOver j) inferInstance ⟨inferInstance, inferInstance⟩ _ hampleX E J i
    inferInstance hssJ hstableX φ hc
  refine ⟨E, hE, finiteGeneration E φ hc hfg, halg.1, φ, hc, q,
    halg.2.2.2, halg.2.1, halg.2.2.1, hqsurj, ?_, ?_, ?_⟩
  · intro T g x y hxy
    apply hqinv T g x y
    apply (cancel_mono (closureInclusion j)).mp
    rw [Category.assoc, hi, (hE T g (x ≫ i)).1, Category.assoc, hi]
    exact hxy
  · intro B f hf
    apply hqcat B f
    intro T g x y hxy
    apply hf T g x y
    rw [← hi]
    calc
      y ≫ i ≫ closureInclusion j = E.act T g (x ≫ i) ≫ closureInclusion j := by
        simpa only [Category.assoc] using congrArg (· ≫ closureInclusion j) hxy
      _ = D.act T g ((x ≫ i) ≫ closureInclusion j) := by
        simpa only [Category.assoc] using (hE T g (x ≫ i)).1
  · intro Ω _ _ _
    refine ⟨(hqgeom Ω).1, fun x y ↦ (hqgeom Ω).2 x y |>.trans ?_⟩
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      rw [← hi]
      calc
        D.act _ (fieldMatrix Ω g) ((x ≫ i) ≫ closureInclusion j) =
            E.act _ (fieldMatrix Ω g) (x ≫ i) ≫ closureInclusion j := by
          simpa only [Category.assoc] using
            (hE _ (fieldMatrix Ω g) (x ≫ i)).1.symm
        _ = y ≫ i ≫ closureInclusion j := by
          simpa only [Category.assoc] using congrArg (· ≫ closureInclusion j) hg
    · rintro ⟨g, hg⟩
      refine ⟨g, (cancel_mono (closureInclusion j)).mp ?_⟩
      exact ((hE _ (fieldMatrix Ω g) (x ≫ i)).1).trans
        (by simpa only [Category.assoc, hi] using hg)

end PGLLinearization
end AlgebraicGeometry
