/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Image

/-!
# The multiplication-by-`n` isogeny

Multiplication by `n` on an abelian variety `A` of dimension `g` is a finite flat surjective
homomorphism, hence an isogeny, of degree `n ^ (2 * g)`, and its kernel `A[n]` is a finite flat
group scheme of that order. On points over an algebraically closed field it is surjective, so
`A(K)` is a divisible group.

Multiplication by `n` is written `𝟙 A ^ n`, the `n`-th power of the identity in the group
`A ⟶ A` coming from `CategoryTheory.GrpObj.Hom.group`.

## Main statements

- `AlgebraicGeometry.isFinite_npow_id`, `AlgebraicGeometry.surjective_npow_id`: multiplication
  by `n` is finite and surjective.
- `AlgebraicGeometry.IsIsogeny.isFinite`, `AlgebraicGeometry.IsIsogeny.flat`,
  `AlgebraicGeometry.IsIsogeny.finrank_eq`: an isogeny is finite flat of degree the order of
  its kernel.
- `AlgebraicGeometry.isIsogeny_npow_id`, `AlgebraicGeometry.isogenyDegree_npow_id`:
  multiplication by `n` is an isogeny of degree `n ^ (2 * g)`.
- `AlgebraicGeometry.finrank_npow_id`: multiplication by `n` is finite locally free of rank
  `n ^ (2 * g)`.
- `AlgebraicGeometry.isFinite_torsionSubgroupScheme`,
  `AlgebraicGeometry.flat_torsionSubgroupScheme`,
  `AlgebraicGeometry.finrankΓ_torsionSubgroupScheme`: `A[n]` is finite flat of order
  `n ^ (2 * g)`.
- `AlgebraicGeometry.surjective_npow_points`: `A(K)` is divisible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-mult-finite`: Finiteness of the fibres of the multiplication map.

Let `A` be an abelian variety over `K` and `0 < n`. Then `[n] : A ⟶ A` is finite. -/
theorem isFinite_npow_id (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ)
    (hn : 0 < n) :
    IsFinite (𝟙 A ^ n).left :=
  sorry

/-- Blueprint `sk-prop-av-mult-finite`: Finiteness of the fibres of the multiplication map.

The kernel `A[n] = ker [n]` of multiplication by `0 < n` on an abelian variety is a finite
group scheme. -/
theorem isFinite_torsionSubgroupScheme (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (n : ℕ) (hn : 0 < n) :
    IsFinite (torsionSubgroupScheme A n).hom :=
  sorry

/-- Blueprint `sk-prop-av-mult-surjective`: Surjectivity of the multiplication map.

Let `A` be an abelian variety over `K` and `0 < n`. Then `[n] : A ⟶ A` is surjective, so `A` is
a divisible group scheme.

This is also blueprint `lem-sc-mult-n-isogeny`, whose finiteness half is
`AlgebraicGeometry.isFinite_torsionSubgroupScheme`. The scheme-theoretic image `Z` of `[n]` is a
closed subscheme of `A` onto which `[n]` maps surjectively
(`AlgebraicGeometry.exists_isMonHom_imageι`). As `A ⟶ Z` is finite and surjective,
`dim Z = dim A`; a closed subset of the irreducible finite-dimensional `A` of full dimension is
all of `A`. -/
theorem surjective_npow_id (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ)
    (hn : 0 < n) :
    Surjective (𝟙 A ^ n).left := by
  have := isFinite_npow_id A n hn
  have := irreducibleSpace_of_connectedSpace A
  let f := (𝟙 A ^ n).left
  obtain ⟨-, hsurj, -⟩ := exists_isMonHom_imageι (𝟙 A ^ n)
  have : IsProper (f.toImage ≫ f.imageι ≫ A.hom) := by
    rw [f.toImage_imageι_assoc, Over.w (𝟙 A ^ n)]; infer_instance
  have : IsProper f.toImage := .of_comp _ (f.imageι ≫ A.hom)
  have : LocallyQuasiFinite (f.toImage ≫ f.imageι) := by
    rw [f.toImage_imageι]; infer_instance
  have : LocallyQuasiFinite f.toImage := .of_comp _ f.imageι
  have hι := f.imageι.isClosedEmbedding.isInducing.surjective_of_topologicalKrullDim_eq
    f.imageι.isClosedEmbedding.isClosed_range (by
      rw [IsAbelianVariety.topologicalKrullDim_eq]
      exact WithBot.coe_injective.ne (ENat.natCast_ne_top _))
    f.toImage.topologicalKrullDim_eq_of_surjective.symm
  have : Surjective (f.toImage ≫ f.imageι) := ⟨by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]; exact hι.comp hsurj.surj⟩
  rwa [f.toImage_imageι] at this

/-- Blueprint `sk-prop-av-mult-surjective`: Surjectivity of the multiplication map.

The `n`-torsion of an abelian variety is zero-dimensional for `0 < n`: it is finite over `K`
(`AlgebraicGeometry.isFinite_torsionSubgroupScheme`), so its underlying space is discrete. -/
theorem topologicalKrullDim_torsionSubgroupScheme (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (n : ℕ) (hn : 0 < n) :
    topologicalKrullDim (torsionSubgroupScheme A n).left = 0 := by
  have := isFinite_torsionSubgroupScheme A n hn
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  have : DiscreteTopology (torsionSubgroupScheme A n).left := by
    rw [← isDiscrete_univ_iff]
    convert (torsionSubgroupScheme A n).hom.isDiscrete_preimage_singleton p
    exact (Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _).symm
  let x := (η[torsionSubgroupScheme A n]).left p
  have : Nonempty (TopologicalSpace.IrreducibleCloseds (torsionSubgroupScheme A n).left) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

variable {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]

/-- Translation identifies the fibres of a homomorphism `f : A ⟶ B` of group schemes with its
kernel: for a point `x : Spec Ω ⟶ A`, the fibre of `f` over `x ≫ f` is the base change
`ker f ×_K Spec Ω`, embedded into `A` by `(k, t) ↦ k + x t`. -/
theorem exists_isPullback_kernel (f : A ⟶ B) [IsMonHom f] {Ω : CommRingCat.{u}}
    (x : Spec Ω ⟶ A.left) :
    ∃ φ : pullback (GrpObj.ker f).hom (x ≫ A.hom) ⟶ A.left,
      IsPullback φ (pullback.snd (GrpObj.ker f).hom (x ≫ A.hom)) f.left (x ≫ f.left) :=
  ⟨_, (GrpObj.isPullback_ker_tensor f (Over.homMk x rfl : Over.mk (x ≫ A.hom) ⟶ A)).map
    (Over.forget _)⟩

/-- The fibres of an isogeny are finite: the fibre over `f a` is the image of the finite scheme
`ker f ×_K Spec κ(a)` under translation by the `κ(a)`-point `a`. -/
theorem IsIsogeny.finite_preimage_singleton (f : A ⟶ B) [IsIsogeny f] (y : B.left) :
    (f.left ⁻¹' {y}).Finite := by
  obtain ⟨a, rfl⟩ := f.left.surjective y
  let x := A.left.fromSpecResidueField a
  let z : Spec (A.left.residueField a) := IsLocalRing.closedPoint _
  obtain ⟨φ, H⟩ := exists_isPullback_kernel f x
  have : Finite (pullback (C := Scheme) (GrpObj.ker f).hom (x ≫ A.hom)) := by
    refine Set.finite_univ_iff.mp (((pullback.snd (GrpObj.ker f).hom
      (x ≫ A.hom)).finite_preimage_singleton z).subset fun w _ ↦ ?_)
    exact Subsingleton.elim (α := Spec (A.left.residueField a)) _ _
  refine (Set.finite_range φ).subset fun a' (ha' : f.left a' = f.left a) ↦ ?_
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f.left) (g := x ≫ f.left)
    a' z (by rw [ha', Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply])
  exact ⟨H.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, hw]⟩

/-- All fibres of an isogeny `f` have degree the order of its kernel: by
`AlgebraicGeometry.exists_isPullback_kernel` the fibre over `f a`, base changed to `κ(a)`, is
the kernel base changed to `κ(a)`, and the fibre degree is invariant under base change. -/
theorem IsIsogeny.fiberDegree_eq (f : A ⟶ B) [IsIsogeny f] [IsAffineHom f.left] (y : B.left) :
    f.left.fiberDegree y = isogenyDegree f := by
  obtain ⟨a, rfl⟩ := f.left.surjective y
  let x := A.left.fromSpecResidueField a
  let z : Spec (A.left.residueField a) := IsLocalRing.closedPoint _
  obtain ⟨φ, H⟩ := exists_isPullback_kernel f x
  have hz : (x ≫ f.left) z = f.left a := by
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  rw [← hz, ← Scheme.Hom.fiberDegree_of_isPullback f.left H z,
    Scheme.Hom.fiberDegree_of_isPullback (GrpObj.ker f).hom (.of_hasPullback _ _) z,
    fiberDegree_eq_finrankΓ]
  rfl

variable [IsAbelianVariety A] [IsAbelianVariety B]

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

An isogeny of abelian varieties is a finite morphism: it is proper, `A` being proper, and has
finite fibres (`AlgebraicGeometry.IsIsogeny.finite_preimage_singleton`). -/
theorem IsIsogeny.isFinite (f : A ⟶ B) [IsIsogeny f] : IsFinite f.left := by
  have : IsProper (f.left ≫ B.hom) := by rw [Over.w f]; infer_instance
  have : IsProper f.left := .of_comp f.left B.hom
  have := LocallyQuasiFinite.of_finite_preimage_singleton f.left
    (IsIsogeny.finite_preimage_singleton f)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

An isogeny of abelian varieties is a flat morphism: it is finite onto the reduced scheme `B`
with all fibres of the same degree (`AlgebraicGeometry.Scheme.Hom.flat_of_fiberDegree_eq`). -/
theorem IsIsogeny.flat (f : A ⟶ B) [IsIsogeny f] : Flat f.left := by
  have := IsIsogeny.isFinite f
  have : IsReduced B.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian B.hom
  have := LocallyOfFiniteType.isLocallyNoetherian B.hom
  exact f.left.flat_of_fiberDegree_eq (IsIsogeny.fiberDegree_eq f)

/-- Blueprint `sk-prop-av-isogeny-degree`: The degree of an isogeny is the degree of the kernel.

For an isogeny `f : A ⟶ B` of abelian varieties with kernel of order `d`, the sheaf `f_* 𝒪_A` is
locally free of rank `d`: the degree of the finite flat morphism `f` equals the order of its
kernel. -/
theorem IsIsogeny.finrank_eq (f : A ⟶ B) [IsIsogeny f] (y : B.left) :
    f.left.finrank y = isogenyDegree f := by
  have := IsIsogeny.isFinite f
  have : IsReduced B.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian B.hom
  have := LocallyOfFiniteType.isLocallyNoetherian B.hom
  exact f.left.finrank_eq_of_fiberDegree_eq (IsIsogeny.fiberDegree_eq f) y

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

Let `A` be an abelian variety over `K` and let `0 < n`. Then `[n] : A ⟶ A` is a finite flat
surjective homomorphism, hence an isogeny.

This is also blueprint `lem-sc-isogeny-facts`. Multiplication by `n` is a homomorphism since `A`
is commutative (`AlgebraicGeometry.IsAbelianVariety.isCommMonObj`), it is surjective by
`AlgebraicGeometry.surjective_npow_id`, and its kernel `A[n]` is finite by
`AlgebraicGeometry.isFinite_torsionSubgroupScheme`. -/
theorem isIsogeny_npow_id (n : ℕ) (hn : 0 < n) : IsIsogeny (𝟙 A ^ n) :=
  have := surjective_npow_id A n hn
  { isFinite_ker := isFinite_torsionSubgroupScheme A n hn }

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

Multiplication by `0 < n` on an abelian variety of dimension `g` has degree `n ^ (2 * g)`. -/
theorem isogenyDegree_npow_id (n : ℕ) (hn : 0 < n) :
    isogenyDegree (𝟙 A ^ n) = n ^ (2 * IsAbelianVariety.dim A) :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

The `n`-torsion of an abelian variety is flat over the base field for `0 < n`. -/
theorem flat_torsionSubgroupScheme (n : ℕ) (hn : 0 < n) :
    Flat (torsionSubgroupScheme A n).hom :=
  sorry

/-- Blueprint `sk-prop-av-isogeny`: The multiplication-by-`n` isogeny.

The `n`-torsion of an abelian variety of dimension `g` has order `n ^ (2 * g)` for `0 < n`. -/
theorem finrankΓ_torsionSubgroupScheme (n : ℕ) (hn : 0 < n) :
    (torsionSubgroupScheme A n).hom.finrankΓ = n ^ (2 * IsAbelianVariety.dim A) :=
  isogenyDegree_npow_id n hn

/-- Blueprint `lem-sc-mult-n-finite-flat`: Multiplication by `n` is finite flat of degree
`n ^ (2 * g)`.

Let `A` be an abelian variety of dimension `g` over `K` and let `0 < n`. Then `[n] : A ⟶ A` is
finite locally free of rank `n ^ (2 * g)`. Finiteness and flatness are
`AlgebraicGeometry.isFinite_npow_id` and `AlgebraicGeometry.IsIsogeny.flat`, and the kernel
`A[n]` has order `n ^ (2 * g)` by `AlgebraicGeometry.finrankΓ_torsionSubgroupScheme`. -/
theorem finrank_npow_id (n : ℕ) (hn : 0 < n) (y : A.left) :
    (𝟙 A ^ n).left.finrank y = n ^ (2 * IsAbelianVariety.dim A) := by
  have := isIsogeny_npow_id (A := A) n hn
  rw [IsIsogeny.finrank_eq, isogenyDegree_npow_id n hn]

/-- Blueprint `sk-prop-av-divisible`: Surjectivity of multiplication by `n` on points.

Let `A` be an abelian variety over an algebraically closed field `K` and `0 < n`. Then
`[n] : A(K) ⟶ A(K)` is surjective: `A(K)` is a divisible abelian group. -/
theorem surjective_npow_points [IsAlgClosed K] (n : ℕ) (hn : 0 < n) :
    Function.Surjective fun a : 𝟙_ (Over (Spec (.of K))) ⟶ A ↦ a ^ n := by
  have := isIsogeny_npow_id (A := A) n hn
  have := IsIsogeny.isFinite (𝟙 A ^ n)
  intro b
  obtain ⟨x, hx⟩ := exists_comp_eq_of_isFinite_of_surjective (𝟙 A ^ n).left b.left
  refine ⟨Over.homMk (U := 𝟙_ _) (V := A) x ?_, ?_⟩
  · rw [← Over.w (𝟙 A ^ n), reassoc_of% hx, Over.w b]
  · dsimp only
    rw [← Category.comp_id (Over.homMk _ _), ← comp_pow]
    exact Over.OverMorphism.ext hx

end AlgebraicGeometry
