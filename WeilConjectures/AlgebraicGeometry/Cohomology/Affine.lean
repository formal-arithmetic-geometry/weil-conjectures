/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Topology.Sheaves.CechCriterion

/-!
# Cohomology of quasi-coherent sheaves on affine schemes

Serre's vanishing theorem says that the higher cohomology of a quasi-coherent sheaf of modules
on an affine scheme vanishes. Its standard consequence is Leray's theorem: the Čech cohomology
of an open covering all of whose finite intersections are affine computes the sheaf cohomology
of any quasi-coherent sheaf of modules. This applies to every open affine covering of a scheme
which is separated over an affine base.

The Čech complex of a family of open subsets `U : ι → X.Opens` with coefficients in a presheaf
is `CategoryTheory.cechComplexFunctor`: the finite products used there are the finite
intersections `U i₀ ⊓ ⋯ ⊓ U iₙ`, so its `q`-th cohomology is the Čech cohomology `Ȟ^q(𝔘, ℱ)`
of the covering. We take the coefficients in `ℱ.presheafModuleCat`, the presheaf of
`Γ(X, ⊤)`-modules underlying `ℱ`, so that `Ȟ^q(𝔘, ℱ)` is a `Γ(X, ⊤)`-module.

## Implementation notes

The blueprint states Leray's theorem as "the edge map of the Čech-to-derived spectral sequence
is an isomorphism". The edge map is not available as a definition, so
`nonempty_cechComplex_linearEquiv_H` only records the existence of a `Γ(X, ⊤)`-linear
isomorphism, without identifying it with the edge map. For `X` over a base `S`, linearity over
`Γ(X, ⊤)` gives linearity over `Γ(S, 𝒪_S)` acting through `X ⟶ S`, and over `k` when
`S = Spec k`, which is what the tangent-space computation of the Jacobian needs. Identifying
the isomorphism awaits the edge map of `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine`: the higher cohomology of a
  quasi-coherent sheaf of modules on an affine scheme vanishes.
- `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H`: Leray's theorem, i.e.
  Čech cohomology of an open covering with affine finite intersections computes the cohomology
  of a quasi-coherent sheaf, linearly over the global functions.
- `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated`: the
  case of an open affine covering of a scheme separated over an affine base.
- `AlgebraicGeometry.Scheme.Modules.finrankH_pushforward_of_isAffineHom`: the pushforward along
  an affine morphism preserves the cohomology of quasi-coherent sheaves of modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The action of `Γ(X, V)` on Čech cochains -/

section CechCochain

open TopCat.Presheaf

variable {n : ℕ}

/-- A nonempty finite intersection of members of a family contained in `V` is contained in `V`. -/
lemma iInf_le_of_forall_le {k : ℕ} (U : Fin n → X.Opens) {V : X.Opens} (hU : ∀ i, U i ≤ V)
    (y : Fin (k + 1) → Fin n) : ⨅ l, U (y l) ≤ V :=
  (iInf_le _ 0).trans (hU _)

/-- The action of `Γ(X, V)` on the Čech cochains of a family of opens contained in `V`. -/
noncomputable def cechCochainSMul (ℱ : X.Modules) {V : X.Opens} (U : Fin n → X.Opens)
    (hU : ∀ i, U i ≤ V) (k : ℕ) : Γ(X, V) →+* AddMonoid.End 
    (TopCat.Presheaf.CechCochain U ℱ.presheaf k) where
  toFun a :=
    { toFun c y := X.presheaf.map (homOfLE (iInf_le_of_forall_le U hU y)).op a • c y
      map_zero' := funext fun _ ↦ smul_zero _
      map_add' _ _ := funext fun _ ↦ smul_add _ _ _ }
  map_one' := AddMonoidHom.ext fun c ↦ funext fun y ↦ by
    simp only [map_one, one_smul]
    rfl
  map_mul' a b := AddMonoidHom.ext fun c ↦ funext fun y ↦ by
    simp only [map_mul, mul_smul]
    rfl
  map_zero' := AddMonoidHom.ext fun c ↦ funext fun y ↦ by
    simp only [map_zero, zero_smul]
    rfl
  map_add' a b := AddMonoidHom.ext fun c ↦ funext fun y ↦ by
    simp only [map_add, add_smul]
    rfl

@[simp]
lemma cechCochainSMul_apply (ℱ : X.Modules) {V : X.Opens} (U : Fin n → X.Opens)
    (hU : ∀ i, U i ≤ V) (k : ℕ) (a : Γ(X, V)) (c : CechCochain U ℱ.presheaf k)
    (y : Fin (k + 1) → Fin n) :
    cechCochainSMul ℱ U hU k a c y =
      X.presheaf.map (homOfLE (iInf_le_of_forall_le U hU y)).op a • c y :=
  rfl

/-- The action of `Γ(X, V)` on Čech cochains commutes with the Čech differential. -/
lemma cechComplex_d_cechCochainSMul (ℱ : X.Modules) {V : X.Opens} (U : Fin n → X.Opens)
    (hU : ∀ i, U i ≤ V) (k : ℕ) (a : Γ(X, V)) (b : CechCochain U ℱ.presheaf k) :
    ((cechComplex U).obj ℱ.presheaf).d k (k + 1) (cechCochainSMul ℱ U hU k a b) =
      cechCochainSMul ℱ U hU (k + 1) a (((cechComplex U).obj ℱ.presheaf).d k (k + 1) b) := by
  funext (y : Fin (k + 1 + 1) → Fin n)
  refine Eq.trans ?_ (cechCochainSMul_apply ℱ U hU (k + 1) a _ y).symm
  simp only [cechComplex_d_apply, cechCochainSMul_apply, Finset.smul_sum,
    Scheme.Modules.map_smul, Scheme.presheaf_map_homOfLE_map_homOfLE_apply]
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

/-- The action of `Γ(X, V)` on Čech cochains commutes with restriction to a smaller family. -/
lemma cechCochainRestrict_cechCochainSMul (ℱ : X.Modules) {V : X.Opens}
    {U U' : Fin n → X.Opens} (hU : ∀ i, U i ≤ V) (h : ∀ i, U' i ≤ U i) (k : ℕ) (a : Γ(X, V))
    (c : CechCochain U ℱ.presheaf k) :
    cechCochainRestrict ℱ.presheaf h k (cechCochainSMul ℱ U hU k a c) =
      cechCochainSMul ℱ U' (fun i ↦ (h i).trans (hU i)) k a
        (cechCochainRestrict ℱ.presheaf h k c) := by
  funext y
  rw [cechCochainRestrict_apply, cechCochainSMul_apply, Scheme.Modules.map_smul,
    Scheme.presheaf_map_homOfLE_map_homOfLE_apply, cechCochainSMul_apply,
    cechCochainRestrict_apply]

/-- A variant of `exists_map_eq_pow_smul_of_isAffineOpen` for an open `O` equal to `D(g)`. -/
lemma exists_map_eq_pow_smul_of_basicOpen_eq (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {W O : X.Opens}
    (hW : IsAffineOpen W) (g : Γ(X, W)) (hO : X.basicOpen g = O) (hOW : O ≤ W)
    (s : Γ(ℱ, O)) :
    ∃ (N : ℕ) (t : Γ(ℱ, W)), ℱ.presheaf.map (homOfLE hOW).op t =
      X.presheaf.map (homOfLE hOW).op g ^ N • s := by
  subst hO
  exact exists_map_eq_pow_smul_of_isAffineOpen ℱ hW g s

/-- A variant of `exists_pow_smul_eq_zero_of_isAffineOpen` for an open `O` equal to `D(g)`. -/
lemma exists_pow_smul_eq_zero_of_basicOpen_eq (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {W O : X.Opens}
    (hW : IsAffineOpen W) (g : Γ(X, W)) (hO : X.basicOpen g = O) (hOW : O ≤ W)
    (t : Γ(ℱ, W)) (ht : ℱ.presheaf.map (homOfLE hOW).op t = 0) :
    ∃ N : ℕ, g ^ N • t = 0 := by
  subst hO
  exact exists_pow_smul_eq_zero_of_isAffineOpen ℱ hW g t ht

/-- Let `V` be affine, `f : Fin n → Γ(X, V)` and `c` a Čech cocycle of the family of basic
opens `D(f i)` with values in a quasi-coherent module. Then for every `j` some power of `f j`
times `c` is a coboundary: after restricting to `D(f j)` the covering contains the whole space,
so the restriction of `c` is a coboundary, and one clears denominators. -/
lemma exists_pow_smul_eq_cechComplex_d (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {V : X.Opens} (hV : IsAffineOpen V)
    (f : Fin n → Γ(X, V)) (q : ℕ) (c : CechCochain (fun i ↦ X.basicOpen (f i)) ℱ.presheaf (q + 1))
    (hc : ((cechComplex fun i ↦ X.basicOpen (f i)).obj ℱ.presheaf).d (q + 1) (q + 2) c = 0)
    (j : Fin n) :
    ∃ (N : ℕ) (b : CechCochain (fun i ↦ X.basicOpen (f i)) ℱ.presheaf q),
      ((cechComplex fun i ↦ X.basicOpen (f i)).obj ℱ.presheaf).d q (q + 1) b =
        cechCochainSMul ℱ _ (fun i ↦ X.basicOpen_le (f i)) (q + 1) (f j ^ N) c := by
  classical
  have hUV (i : Fin n) : X.basicOpen (f i) ≤ V := X.basicOpen_le (f i)
  have hU'U (i : Fin n) : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ X.basicOpen (f i) :=
    inf_le_left
  have hU'V (i : Fin n) : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ V := inf_le_left.trans (hUV i)
  have hI (k : ℕ) (y : Fin (k + 1) → Fin n) : IsAffineOpen (⨅ l, X.basicOpen (f (y l))) := by
    rw [Scheme.iInf_basicOpen_eq_basicOpen_prod]
    exact hV.basicOpen _
  have hO (k : ℕ) (y : Fin (k + 1) → Fin n) :
      X.basicOpen (X.presheaf.map (homOfLE (iInf_le_of_forall_le _ hUV y)).op (f j)) =
        ⨅ l, (X.basicOpen (f (y l)) ⊓ X.basicOpen (f j)) := by
    rw [Scheme.basicOpen_res, iInf_inf]
  have hex := exactAt_cechComplex_of_le (fun i ↦ X.basicOpen (f i) ⊓ X.basicOpen (f j))
    ℱ.presheaf (j := j) (fun i ↦ le_inf inf_le_right inf_le_right) q
  rw [exactAt_cechComplex_iff] at hex
  obtain ⟨b', hb'⟩ := hex (cechCochainRestrict ℱ.presheaf hU'U (q + 1) c) (by
    rw [cechComplex_d_cechCochainRestrict, hc]
    exact map_zero _)
  have hlift (y : Fin (q + 1) → Fin n) : ∀ᶠ N in Filter.atTop,
      ∃ t : Γ(ℱ, ⨅ l, X.basicOpen (f (y l))),
        ℱ.presheaf.map (homOfLE (iInf_mono fun l ↦ hU'U (y l))).op t =
          cechCochainSMul ℱ _ hU'V q (f j ^ N) b' y := by
    obtain ⟨N₀, t, ht⟩ := exists_map_eq_pow_smul_of_basicOpen_eq ℱ (hI q y) _ (hO q y)
      (iInf_mono fun l ↦ hU'U (y l)) (b' y)
    refine Filter.eventually_atTop.2 ⟨N₀, fun N hN ↦ ⟨X.presheaf.map
      (homOfLE (iInf_le_of_forall_le _ hUV y)).op (f j) ^ (N - N₀) • t, ?_⟩⟩
    rw [Scheme.Modules.map_smul, ht, map_pow, Scheme.presheaf_map_homOfLE_map_homOfLE_apply,
      ← mul_smul, ← pow_add, Nat.sub_add_cancel hN, cechCochainSMul_apply, map_pow]
  obtain ⟨N, hN⟩ := (Filter.eventually_all.2 hlift).exists
  choose s hs using hN
  have hz : cechCochainRestrict ℱ.presheaf hU'U (q + 1)
      (cechCochainSMul ℱ _ hUV (q + 1) (f j ^ N) c) = cechCochainRestrict ℱ.presheaf hU'U (q + 1)
        (((cechComplex fun i ↦ X.basicOpen (f i)).obj ℱ.presheaf).d q (q + 1) s) := by
    have hs' : cechCochainRestrict ℱ.presheaf hU'U q s = cechCochainSMul ℱ _ hU'V q (f j ^ N) b' :=
      funext hs
    rw [cechCochainRestrict_cechCochainSMul, ← cechComplex_d_cechCochainRestrict, hs',
      cechComplex_d_cechCochainSMul, hb']
  have hkill (y : Fin (q + 1 + 1) → Fin n) : ∀ᶠ M in Filter.atTop,
      X.presheaf.map (homOfLE (iInf_le_of_forall_le _ hUV y)).op (f j) ^ M •
        (cechCochainSMul ℱ _ hUV (q + 1) (f j ^ N) c y -
          ((cechComplex fun i ↦ X.basicOpen (f i)).obj ℱ.presheaf).d q (q + 1) s y) = 0 := by
    obtain ⟨M₀, hM₀⟩ := exists_pow_smul_eq_zero_of_basicOpen_eq ℱ (hI (q + 1) y) _
      (hO (q + 1) y) (iInf_mono fun l ↦ hU'U (y l))
      (cechCochainSMul ℱ _ hUV (q + 1) (f j ^ N) c y -
        ((cechComplex fun i ↦ X.basicOpen (f i)).obj ℱ.presheaf).d q (q + 1) s y) (by
        rw [map_sub, sub_eq_zero]
        exact congrFun hz y)
    refine Filter.eventually_atTop.2 ⟨M₀, fun M hM ↦ ?_⟩
    rw [← Nat.sub_add_cancel hM, pow_add, mul_smul, hM₀, smul_zero]
  obtain ⟨M, hM⟩ := (Filter.eventually_all.2 hkill).exists
  refine ⟨M + N, cechCochainSMul ℱ _ hUV q (f j ^ M) s, ?_⟩
  rw [cechComplex_d_cechCochainSMul, pow_add, map_mul, AddMonoid.End.coe_mul,
    Function.comp_apply]
  funext (y : Fin (q + 1 + 1) → Fin n)
  have hy := hM y
  rw [smul_sub, sub_eq_zero] at hy
  refine (cechCochainSMul_apply ℱ _ hUV (q + 1) _ _ y).trans
    ((cechCochainSMul_apply ℱ _ hUV (q + 1) _ _ y).trans ?_).symm
  rw [map_pow]
  exact hy

end CechCochain

open TopCat.Presheaf in
/-- **The Čech complex of a standard covering is exact.** Let `V` be an affine open of `X`, so
that `V = Spec A` with `A = Γ(X, V)`, let `f₁, …, fₙ ∈ A` generate the unit ideal, i.e. the basic
opens `D(fᵢ)` cover `V`, and let `ℱ` be a quasi-coherent `𝒪_X`-module, with `M = ℱ(V)`. Then the
Čech complex `0 → ∏ᵢ M_{fᵢ} → ∏_{i, j} M_{fᵢfⱼ} → ⋯` of the covering is exact in positive degrees.

This is the ordered Čech complex `TopCat.Presheaf.cechComplex`; exactness of the augmented
complex in degree `0` is the sheaf condition for `ℱ`. The proof localizes at each `fⱼ`: after
inverting `fⱼ` the covering contains the whole space and the complex is contractible, so every
cocycle is killed by a power of each `fⱼ` up to a coboundary, and these powers still generate
the unit ideal.

(blueprint: `lem-pc-affine-cech-complex`) -/
theorem exactAt_cechComplex_basicOpen (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {V : X.Opens} (hV : IsAffineOpen V)
    {n : ℕ} (f : Fin n → Γ(X, V)) (hf : ⨆ i, X.basicOpen (f i) = V) (q : ℕ) :
    ((TopCat.Presheaf.cechComplex fun i ↦ X.basicOpen (f i)).obj ℱ.presheaf).ExactAt (q + 1) := by
  rw [exactAt_cechComplex_iff]
  intro c hc
  let J : Ideal Γ(X, V) :=
    { carrier := {a | ∃ b : CechCochain (fun i ↦ X.basicOpen (f i)) ℱ.presheaf q,
        ((cechComplex fun i ↦ X.basicOpen (f i)).obj ℱ.presheaf).d q (q + 1) b =
        cechCochainSMul ℱ _ (fun i ↦ X.basicOpen_le (f i)) (q + 1) a c}
      add_mem' := by
        rintro a a' ⟨b, hb⟩ ⟨b', hb'⟩
        refine ⟨b + b', ((map_add _ b b').trans (congrArg₂ (· + ·) hb hb')).trans ?_⟩
        rw [map_add]
        rfl
      zero_mem' := ⟨0, by
        refine (map_zero _).trans ?_
        rw [map_zero]
        rfl⟩
      smul_mem' := by
        rintro r a ⟨b, hb⟩
        refine ⟨cechCochainSMul ℱ _ (fun i ↦ X.basicOpen_le (f i)) q r b, ?_⟩
        rw [cechComplex_d_cechCochainSMul, hb, smul_eq_mul, map_mul, AddMonoid.End.coe_mul,
          Function.comp_apply] }
  obtain ⟨b, hb⟩ : (1 : Γ(X, V)) ∈ J := by
    rw [← Ideal.eq_top_iff_one, ← Ideal.radical_eq_top, eq_top_iff,
      ← (hV.self_le_iSup_basicOpen_iff (s := Set.range f)).1 ?_, Ideal.span_le]
    · rintro _ ⟨j, rfl⟩
      exact exists_pow_smul_eq_cechComplex_d ℱ hV f q c hc j
    · exact hf.ge.trans (iSup_le fun i ↦ le_iSup_of_le ⟨f i, i, rfl⟩ le_rfl)
  refine ⟨b, ?_⟩
  rw [hb, map_one, AddMonoid.End.coe_one, id_eq]

/-- **Vanishing of cohomology on affine schemes.** Let `X = Spec A` be affine. For every
quasi-coherent `𝒪_X`-module `ℱ` and every `q > 0` we have `H^q(X, ℱ) = 0`; the vanishing of the
abelian group `ℱ.H (q + 1)` is expressed as it being a subsingleton.

This is the Čech criterion `TopCat.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` applied to the
affine opens and their standard coverings by basic opens, on which the Čech complex of `ℱ` is
exact in positive degrees by `exactAt_cechComplex_basicOpen`.

(blueprint: `sk-lem-picard-affine`, `lem-pc-affine-vanishing`) -/
theorem subsingleton_H_succ_of_isAffine [IsAffine X] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Subsingleton (ℱ.H (q + 1)) := by
  refine TopCat.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) IsAffineOpen
    (fun {n} U ↦ ∃ (V : X.Opens) (_ : IsAffineOpen V) (f : Fin n → Γ(X, V)),
      U = (fun i ↦ X.basicOpen (f i)) ∧ ⨆ i, X.basicOpen (f i) = V)
    (isAffineOpen_top X) ?_ ?_ ?_ q
  · rintro n _ ⟨V, hV, f, rfl, -⟩ k y
    rw [Scheme.iInf_basicOpen_eq_basicOpen_prod]
    exact hV.basicOpen _
  · intro V hV W hW
    choose g hgW hxg using fun x : V ↦ hV.exists_basicOpen_le (V := W x) ⟨x.1, hW x⟩ x.2
    obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V ↦ (X.basicOpen (g x) : Set X))
      (fun x ↦ (X.basicOpen (g x)).isOpen) (fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxg _⟩)
    have hsup : ⨆ i, X.basicOpen (g (t.equivFin.symm i).1) = V := by
      refine le_antisymm (iSup_le fun i ↦ X.basicOpen_le _) fun x hx ↦ ?_
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact Opens.mem_iSup.2 ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩
    exact ⟨t.card, fun i ↦ X.basicOpen (g (t.equivFin.symm i).1),
      ⟨V, hV, fun i ↦ g (t.equivFin.symm i).1, rfl, hsup⟩, hsup,
      fun i ↦ ⟨(t.equivFin.symm i).1, hgW _⟩⟩
  · rintro n _ ⟨V, hV, f, rfl, hf⟩ q
    exact exactAt_cechComplex_basicOpen ℱ hV f hf q

/-- **Leray's theorem for quasi-coherent sheaves.** Let `𝔘 = (U i)` be an open covering of `X`
all of whose nonempty finite intersections `U i₀ ⊓ ⋯ ⊓ U iₙ` are affine. Then for every
quasi-coherent `𝒪_X`-module `ℱ` and every `q` the Čech cohomology of the covering agrees with
the sheaf cohomology, `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)`, as `Γ(X, ⊤)`-modules.

The left-hand side is the `q`-th cohomology of the Čech complex `cechComplexFunctor U` of the
family `U` with coefficients in the presheaf of `Γ(X, ⊤)`-modules `ℱ.presheafModuleCat`; the
right-hand side carries the `Γ(X, ⊤)`-module structure
`AlgebraicGeometry.Scheme.Modules.moduleH`.

The isomorphism ought to be the edge map of the Čech-to-derived spectral sequence
`CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`, which is an isomorphism because
the higher rows of that spectral sequence vanish by `subsingleton_H_succ_of_isAffine`; see the
implementation notes of this module for what is lost by not naming it. -/
@[stacks 01XD]
theorem nonempty_cechComplex_linearEquiv_H {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q) :=
  sorry

/-- **Leray's theorem for schemes separated over an affine base.** Let `X` be separated over an
affine base `S` and let `𝔘 = (U i)` be a covering of `X` by open affines. Then for every
quasi-coherent `𝒪_X`-module `ℱ` and every `q` we have `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)` as
`Γ(X, ⊤)`-modules. This is `nonempty_cechComplex_linearEquiv_H`, the finite intersections of
the `U i` being affine because `X` is separated.

Restricting scalars along `f.appTop`, the isomorphism is `Γ(S, 𝒪_S)`-linear, and `k`-linear
when `S = Spec k`.

(blueprint: `sk-lem-picard-cech-computes`) -/
theorem nonempty_cechComplex_linearEquiv_H_of_isSeparated {S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [IsAffine S] {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hU' : iSup U = ⊤) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q) :=
  haveI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  nonempty_cechComplex_linearEquiv_H U
    (fun s hs ↦ IsAffineOpen.biInf (s : Set ι) s.finite_toSet hs (fun i _ ↦ hU i)) hU' ℱ q

section AffineMorphism

variable (k : Type u) [Field k] {Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

/-- **Cohomology along an affine morphism.** Let `g : X ⟶ Y` be an affine morphism of
`k`-schemes. Then `H^q(X, ℱ) ≅ H^q(Y, g_* ℱ)`, `k`-linearly and naturally in the quasi-coherent
`𝒪_X`-module `ℱ`. The higher direct images `R^p g_* ℱ` vanish, since on an affine open `V` of `Y`
they are computed by the cohomology of `ℱ` on the affine scheme `g ⁻¹ᵁ V`, which vanishes by
`subsingleton_H_succ_of_isAffine`; the Leray spectral sequence then degenerates. -/
theorem nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom (g : X ⟶ Y)
    [g.IsOver (Spec (.of k))] [IsAffineHom g] (q : ℕ) :
    Nonempty ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ cohomologyFunctor k q ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ pushforward g ⋙
        cohomologyFunctor k q) :=
  sorry

/-- **Cohomology along an affine morphism.** Let `g : X ⟶ Y` be an affine morphism of
`k`-schemes. For every quasi-coherent `𝒪_X`-module `ℱ` and every `q` we have
`H^q(Y, g_* ℱ) ≅ H^q(X, ℱ)` (`nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`), so the
two have the same dimension over `k`. -/
theorem finrankH_pushforward_of_isAffineHom (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    [IsAffineHom g] (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    (q : ℕ) : ((pushforward g).obj ℱ).finrankH k q = ℱ.finrankH k q := by
  obtain ⟨e⟩ := nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k g q
  exact ((e.app ⟨ℱ, inferInstance⟩).toLinearEquiv.finrank_eq).symm

/-- The Euler characteristic is invariant under pushforward along an affine morphism:
`χ(Y, g_* ℱ) = χ(X, ℱ)` for a quasi-coherent `𝒪_X`-module `ℱ`. -/
theorem eulerChar_pushforward_of_isAffineHom (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    [IsAffineHom g] (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    ((pushforward g).obj ℱ).eulerChar k = ℱ.eulerChar k := by
  simp only [eulerChar, finrankH_pushforward_of_isAffineHom k g ℱ]

end AffineMorphism

end AlgebraicGeometry.Scheme.Modules
