/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Correspondence
public import WeilConjectures.TraceFormula.FixedPointScheme

/-!

# Components of the Frobenius fixed locus

For the model Frobenius `Φ` of `X = X₀ ×_{k₀} k` and `m ≥ 1`, the fixed scheme `Fix(Φ_m)` is a
finite disjoint union of reduced points `∐ Spec k`
(`ProEtale.CondensedRing.IsModelFrobenius.nonempty_isLimit_fixedPointsFork`). Consequently an
open subscheme `B` of the fixed locus whose underlying set is a single point `{z}` is the
component `{z}`, a copy of the base point `Spec k` (blueprint `sk-lem-tf-fixed-points`, as used
in the proofs of `sk-i-curve-zero` and `sk-p-frob`).

## Main definitions and statements

- `ProEtale.CondensedRing.isoPointOfRangeEq`: an open subscheme `j : B ⟶ Y` with the same range
  as an open immersion `g : Spec k ⟶ Y` over `Spec k` is isomorphic to `Spec k` over `Spec k`,
  compatibly with `j` and `g`.
- `ProEtale.CondensedRing.IsModelFrobenius.exists_isOpenImmersion_rationalPoint_of_isLimit`:
  every point `z` of the fixed scheme of `Φ_m` is the image of an open immersion
  `Spec k ⟶ Fix(Φ_m)` over `Spec k`.
- `ProEtale.CondensedRing.Correspondence.FixedLocus.isoPointOfRangeEq`: for the fixed locus `F`
  of the graph correspondence `(𝟙, Φ_m)` and an open immersion `j : B ⟶ F.F` with range `{z}`,
  an isomorphism `B ≅ Spec k` over `Spec k`; the composite `Spec k ≅ B ⟶ F.F` is the rational
  point with underlying point `z`
  (`ProEtale.CondensedRing.Correspondence.FixedLocus.isoPointOfRangeEq_inv_comp_eq`).
- `ProEtale.CondensedRing.Correspondence.FixedLocus.isoSigmaPointFixedFieldPoints`:
  `Fix(Φ_m) ≅ ∐_{x ∈ X₀(𝔽_{q^m})} Spec k` (blueprint `sk-lem-tf-fixed-points`); the fixed locus
  is finite, proper and reduced (`FixedLocus.isFinite_hom`, `FixedLocus.isProper_hom`,
  `FixedLocus.isReduced`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

section OpenPoint

variable {B Y : Over (Spec (.of k))} (j : B ⟶ Y) [IsOpenImmersion j.left] (g : RationalPoint Y)
  [IsOpenImmersion g.left]

/-- An open subscheme `j : B ⟶ Y` over `Spec k` with the same underlying set as an open immersion
`g : Spec k ⟶ Y` over `Spec k` is isomorphic to `Spec k` over `Spec k`. -/
noncomputable def isoPointOfRangeEq (h : Set.range j.left.base = Set.range g.left.base) :
    B ≅ point k :=
  Over.isoMk (IsOpenImmersion.isoOfRangeEq j.left g.left h) (by
    have hg : g.left ≫ Y.hom = 𝟙 _ := by simp
    calc _ = ((IsOpenImmersion.isoOfRangeEq j.left g.left h).hom ≫ g.left) ≫ Y.hom := by
          rw [Category.assoc, hg]; rfl
      _ = B.hom := by rw [IsOpenImmersion.isoOfRangeEq_hom_fac, Over.w j])

@[reassoc (attr := simp)]
lemma isoPointOfRangeEq_hom_comp (h : Set.range j.left.base = Set.range g.left.base) :
    (isoPointOfRangeEq j g h).hom ≫ g = j := by
  ext1
  exact IsOpenImmersion.isoOfRangeEq_hom_fac j.left g.left h

@[reassoc (attr := simp)]
lemma isoPointOfRangeEq_inv_comp (h : Set.range j.left.base = Set.range g.left.base) :
    (isoPointOfRangeEq j g h).inv ≫ j = g := by
  rw [Iso.inv_comp_eq, isoPointOfRangeEq_hom_comp]

end OpenPoint

/-- The underlying set of a rational point is a single point. -/
lemma range_rationalPoint_left_base {Y : Over (Spec (.of k))} (g : RationalPoint Y) :
    Set.range g.left.base = {g.left.base (default : Spec (.of k))} := by
  have : Subsingleton (point k).left := inferInstanceAs (Subsingleton (Spec (.of k)))
  refine Set.ext fun y ↦ ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩
    exact congrArg g.left.base (Subsingleton.elim a (default : Spec (.of k)))
  · rintro rfl
    exact ⟨_, rfl⟩

section FixedLocus

variable {X : Over (Spec (.of k))} [IsAlgClosed k] [LocallyOfFiniteType X.hom] {k₀ : Type u}
  [Field k₀] [Finite k₀]
  [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}
  {m : ℕ}

/-- Every point `z` of the fixed scheme `Fix(Φ_m)` of the model Frobenius, `m ≥ 1`, is the image
of an open immersion `Spec k ⟶ Fix(Φ_m)` over `Spec k`: `Fix(Φ_m)` is a finite disjoint union of
reduced points (blueprint `sk-lem-tf-fixed-points`). -/
lemma IsModelFrobenius.exists_isOpenImmersion_rationalPoint_of_isLimit
    (hΦ : IsModelFrobenius Φ f₀ p) (hm : 1 ≤ m) {T : Over (Spec (.of k))} {ι : T ⟶ X}
    {w : ι ≫ 𝟙 X = ι ≫ frobeniusIterate Φ m} (hT : IsLimit (Fork.ofι ι w)) (z : T.left) :
    ∃ g : RationalPoint T, IsOpenImmersion g.left ∧ Set.range g.left.base = {z} := by
  let φ := IsLimit.conePointUniqueUpToIso (hΦ.nonempty_isLimit_fixedPointsFork hm).some hT
  let φ' : sigmaPoint k (FixedPoint Φ m) ≅ T := φ
  obtain ⟨i, a, ha⟩ := Set.mem_iUnion.mp
    ((iUnion_range_sigmaPointι k (FixedPoint Φ m)).symm ▸ Set.mem_univ (φ'.inv.left.base z))
  refine ⟨sigmaPointι k _ i ≫ φ'.hom, ?_, ?_⟩
  · have : IsIso φ'.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso φ').hom)
    rw [Over.comp_left, sigmaPointι_left]
    infer_instance
  · rw [range_rationalPoint_left_base]
    congr 1
    have : Subsingleton (point k).left := inferInstanceAs (Subsingleton (Spec (.of k)))
    rw [Subsingleton.elim (default : Spec (.of k)) a, Over.comp_left, Scheme.Hom.comp_apply,
      ha, ← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    rfl

end FixedLocus

namespace Correspondence

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} [IsAlgClosed k] {k₀ : Type u}
  [Field k₀] [Finite k₀]
  [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}
  {m : ℕ} {v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K}
  {F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus} {B : Over (Spec (.of k))}
  (j : B ⟶ F.F) [IsOpenImmersion j.left] {z : F.F.left}

/-- For the fixed locus `F` of the graph correspondence `(𝟙, Φ_m)` of the model Frobenius,
`m ≥ 1`, every point `z` of `F` is the image of an open immersion `Spec k ⟶ F` over `Spec k`
(blueprint `sk-lem-tf-fixed-points`). -/
lemma FixedLocus.exists_isOpenImmersion_rationalPoint (hΦ : IsModelFrobenius Φ f₀ p)
    (hm : 1 ≤ m) (z : F.F.left) :
    ∃ g : RationalPoint F.F, IsOpenImmersion g.left ∧ Set.range g.left.base = {z} :=
  hΦ.exists_isOpenImmersion_rationalPoint_of_isLimit hm F.isLimit z

/-- **An open piece of the Frobenius fixed locus with one point is a point** (blueprint
`sk-lem-tf-fixed-points`, as used in `sk-i-curve-zero` and `sk-p-frob`): for the fixed locus `F`
of the graph correspondence `(𝟙, Φ_m)` of the model Frobenius, `m ≥ 1`, and an open immersion
`j : B ⟶ F` whose underlying set is a single point `{z}`, `B ≅ Spec k` over `Spec k`. The fixed
scheme is a finite disjoint union of reduced points, so `B` is the component `{z}`. -/
noncomputable def FixedLocus.isoPointOfRangeEq (hΦ : IsModelFrobenius Φ f₀ p) (hm : 1 ≤ m)
    (hB : Set.range j.left.base = {z}) : B ≅ point k :=
  have := (F.exists_isOpenImmersion_rationalPoint hΦ hm z).choose_spec.1
  CondensedRing.isoPointOfRangeEq j (F.exists_isOpenImmersion_rationalPoint hΦ hm z).choose
    (hB.trans (F.exists_isOpenImmersion_rationalPoint hΦ hm z).choose_spec.2.symm)

/-- The rational point `Spec k ≅ B ⟶ F` of `FixedLocus.isoPointOfRangeEq` has underlying
point `z`. -/
lemma FixedLocus.isoPointOfRangeEq_inv_comp_left_base (hΦ : IsModelFrobenius Φ f₀ p)
    (hm : 1 ≤ m) (hB : Set.range j.left.base = {z}) (s : Spec (.of k)) :
    ((FixedLocus.isoPointOfRangeEq j hΦ hm hB).inv ≫ j).left.base s = z := by
  have h : ((FixedLocus.isoPointOfRangeEq j hΦ hm hB).inv ≫ j).left.base s ∈
      Set.range j.left.base := by
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  rwa [hB] at h

/-- The rational point `Spec k ≅ B ⟶ F` of `FixedLocus.isoPointOfRangeEq` is the unique rational
point of `F` with underlying point `z`, for instance the lift `F.liftPoint x hx` of a rational
point `x` fixed by `Φ_m`. -/
lemma FixedLocus.isoPointOfRangeEq_inv_comp_eq (hΦ : IsModelFrobenius Φ f₀ p) (hm : 1 ≤ m)
    (z' : RationalPoint F.F)
    (hB : Set.range j.left.base = {z'.left.base (default : Spec (.of k))}) :
    (FixedLocus.isoPointOfRangeEq j hΦ hm hB).inv ≫ j = z' := by
  refine rationalPoint_ext ?_
  rw [isoPointOfRangeEq_inv_comp_left_base]
  exact congrArg z'.left.base (Subsingleton.elim (α := Spec (.of k)) _ _)
/-! ### The fixed locus as a disjoint union of points -/

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
