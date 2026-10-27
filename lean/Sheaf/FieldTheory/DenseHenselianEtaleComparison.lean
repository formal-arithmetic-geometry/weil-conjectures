/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Homeomorph.Lemmas
import Sheaf.FieldTheory.SeparableClosureRestrictionImage
import Sheaf.FieldTheory.DenseHenselianRelativeSeparableClosed
import Sheaf.FieldTheory.DenseHenselianSimpleRootApproximation
import Sheaf.AlgebraicGeometry.GaloisRestrictionEtaleEquivalence

/-!
# Étale comparison for dense extensions of henselian valued fields

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XX 4.4, printed p.374
(blueprint: lem-per-dense-henselian-field-etale-comparison).

The Galois isomorphism is specified on elements of the chosen compatible separable
closures, which characterizes restriction uniquely. Cohomology uses the existing
`Etale.cohomologyMap`, with its existing inverse image `Etale.upperStar`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w s t

open CategoryTheory

namespace AlgebraicGeometry.Etale

private theorem separable_mem_closure_range
    (K : Type u) (Ks : Type s) (Ls : Type t) [Field K] [Field Ks] [Field Ls]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ls] [Algebra K Ls]
    [IsScalarTower K Ks Ls] (b : Ls) (hb : IsSeparable K b) :
    b ∈ Set.range (algebraMap Ks Ls) := by
  have : IsSepClosed Ks := IsSepClosure.sep_closed K
  have hs := IsSepClosed.splits_codomain (f := algebraMap K Ks) (minpoly K b) hb
  apply hs.mem_range_of_isRoot (Polynomial.map_ne_zero (minpoly.ne_zero hb.isIntegral))
  change Polynomial.eval b
    (((minpoly K b).map (algebraMap K Ks)).map (algebraMap Ks Ls)) = 0
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K Ks Ls]
  rw [Polynomial.eval_map_algebraMap, minpoly.aeval]

private theorem isSeparable_of_simple_root
    (K : Type u) (E : Type t) [Field K] [Field E] [Algebra K E]
    (g : Polynomial K) (b : E) (hg : g.Monic)
    (hb : Polynomial.aeval b g = 0) (hd : Polynomial.aeval b g.derivative ≠ 0) :
    IsSeparable K b := by
  have hi : _root_.IsIntegral K b := ⟨g, hg, hb⟩
  apply (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hi)).mpr
  intro hz
  obtain ⟨h, hh⟩ := minpoly.dvd K b hb
  apply hd
  simp [hh, Polynomial.derivative_mul, hz, minpoly.aeval]

/-- A dense inclusion of henselian valued fields induces the restriction isomorphism
of absolute Galois groups and natural isomorphisms on torsion étale cohomology.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XX 4.4, printed p.374
(blueprint: lem-per-dense-henselian-field-etale-comparison).

Proof:
1. For an element of L separable algebraic over K, choose a finite Galois envelope
   (`lem-weil-pbc-finite-set-in-finite-galois-subextension`). The uniqueness clause of
   `lem-per-henselian-finite-extension-topology` identifies the topology on K(a) with
   the one induced from L. Density and `lem-per-henselian-krasner-neighbourhood` give
   b in K close enough to a that a belongs to K(b) = K. Thus K is relatively separably
   closed in L, including the case a already belongs to K.
2. By `lem-per-galois-restriction-image`, restriction is continuous and its image is
   the subgroup fixing the intersection of L with the chosen separable closure of K.
   Step 1 identifies that intersection with K, so restriction is surjective.
3. Given a in Ls, choose a finite Galois envelope over L and prolong its valuation
   by `lem-per-henselian-finite-extension-topology`. Its valuation ring is henselian.
   The separable minimal polynomial f of a is monic and has nonzero derivative at a.
   In a Krasner neighbourhood of a, `lem-per-henselian-simple-root-stability` gives
   a simple root b of every sufficiently close monic polynomial. Density, applied
   coordinatewise to its finitely many coefficients, gives such a polynomial over K.
   Krasner over L gives a in L(b).
4. The minimal polynomial m of b over K divides that polynomial g. Differentiating
   g = m h and evaluating at b gives m'(b) h(b) = g'(b), which is nonzero. The
   irreducible-derivative criterion `lem-trf-irreducible-separable-derivative` makes
   m separable. As Ks is separably closed (`def-kun-separably-closed`), b is in its
   image in Ls. Thus L and Ks generate Ls and the restriction kernel is trivial.
5. The Krull finite-limit theorem `lem-exc-galois-krull-finite-limit` and
   `lem-galois-closed-subgroup-product-finite-groups` make both groups compact
   Hausdorff. Apply `lem-weil-pbc-compact-hausdorff-bijection` to the continuous
   bijective restriction map. Its inverse is multiplicative, giving the displayed
   topological group isomorphism with the specified restriction formula.
6. In a common algebraically closed overfield (`def-weil-algebraic-closure`), use
   `lem-exc-abelian-sheaves-gmodules` and `lem-per-field-pullback-galois-action`.
   Inverse image corresponds to restriction along this topological group isomorphism,
   an exact equivalence. Its map on global sections identifies invariants for the
   same group, naturally in the sheaf.
7. Take a K-injective resolution (`prop-weil-pbc-kinjective-resolutions-exist`,
   `def-weil-pbc-kinjective-resolutions`). An exact equivalence and its exact
   quasi-inverse identify Hom complexes, so inverse image preserves K-injectivity.
   Step 6 identifies the section complexes termwise and compatibly with differentials.
   Taking degree-q cohomology gives precisely the canonical pullback, bijective in
   every nonnegative degree and natural in torsion sheaves. This uses no uniform
   torsion exponent, completeness, rank-one, discreteness, or characteristic assumption. -/
theorem denseHenselianField_etaleComparison
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (Γ : Type v) (Δ : Type w)
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    [vK : Valued K Γ] [vL : Valued L Δ]
    [vK.v.IsNontrivial] [vL.v.IsNontrivial]
    [HenselianLocalRing vK.v.valuationSubring]
    [HenselianLocalRing vL.v.valuationSubring]
    (h_induced : Topology.IsInducing (algebraMap K L))
    (h_dense : DenseRange (algebraMap K L))
    (Ks : Type s) (Ls : Type t) [Field Ks] [Field Ls]
    [Algebra K Ks] [IsSepClosure K Ks]
    [Algebra L Ls] [IsSepClosure L Ls]
    [Algebra Ks Ls] [Algebra K Ls]
    [IsScalarTower K Ks Ls] [IsScalarTower K L Ls] :
    (∃ e : Gal(Ls/L) ≃ₜ* Gal(Ks/K),
      ∀ (σ : Gal(Ls/L)) (x : Ks),
        algebraMap Ks Ls (e σ x) = σ (algebraMap Ks Ls x)) ∧
    (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      F.IsTorsion → ∀ q : ℕ,
        Function.Bijective (cohomologyMap
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) F q)) ∧
    (∀ (F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      F.IsTorsion → G.IsTorsion → ∀ (φ : F ⟶ G) (q : ℕ) (x : Sheaf.H F q),
        cohomologyMap (Spec.map (CommRingCat.ofHom (algebraMap K L))) G q
            (Sheaf.H.map φ q x) =
          Sheaf.H.map
            ((upperStar AddCommGrpCat.{u + 1}
              (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map φ) q
            (cohomologyMap (Spec.map (CommRingCat.ofHom (algebraMap K L))) F q x)) := by
  let r := IntermediateField.restrictRestrictAlgEquivMapHom K Ks L Ls
  have hr (σ : Gal(Ls/L)) (x : Ks) :
      algebraMap Ks Ls (r σ x) = σ (algebraMap Ks Ls x) :=
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgAut Gal(Ls/L) K Ls σ) Ks x
  obtain ⟨hc, _, himage⟩ :=
    IntermediateField.separableClosure_restriction_image K L Ks Ls
  have hsurj : Function.Surjective r := by
    intro σ
    have hmem : σ ∈ (r.range : Set Gal(Ks/K)) := by
      rw [himage]
      intro x hx
      obtain ⟨a, ha⟩ := hx
      have hsep : IsSeparable K a := by
        apply (isSeparable_map_iff (IsScalarTower.toAlgHom K L Ls)
          (algebraMap L Ls).injective).mp
        rw [show IsScalarTower.toAlgHom K L Ls a = algebraMap Ks Ls x from ha]
        exact (Algebra.IsSeparable.isSeparable K x).map
          (IsScalarTower.toAlgHom K Ks Ls) (algebraMap Ks Ls).injective
      obtain ⟨k, hk⟩ := FieldTheory.denseHenselian_isSeparable_mem_range
        K L Γ Δ h_induced h_dense a hsep
      have hxk : x = algebraMap K Ks k := by
        apply (algebraMap Ks Ls).injective
        calc
          algebraMap Ks Ls x = algebraMap L Ls a := ha.symm
          _ = algebraMap L Ls (algebraMap K L k) := congrArg (algebraMap L Ls) hk.symm
          _ = algebraMap K Ls k := (IsScalarTower.algebraMap_apply K L Ls k).symm
          _ = algebraMap Ks Ls (algebraMap K Ks k) :=
            IsScalarTower.algebraMap_apply K Ks Ls k
      rw [hxk, σ.commutes]
    exact hmem
  have hinj : Function.Injective r := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro a
    obtain ⟨g, b, hg, hb, hd, hab⟩ := FieldTheory.denseHenselian_exists_simple_root
      K L Γ Δ h_induced h_dense Ls a
    have hbsep := isSeparable_of_simple_root K Ls g b hg hb hd
    obtain ⟨x, hx⟩ := separable_mem_closure_range K Ks Ls b hbsep
    have hfix : σ b = τ b := by
      rw [← hx, ← hr σ x, ← hr τ x, hστ]
    exact IntermediateField.adjoin_induction L
      (p := fun y _ ↦ σ y = τ y)
      (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hfix)
      (fun c ↦ (σ.commutes c).trans (τ.commutes c).symm)
      (fun y z _ _ hy hz ↦ by simp only [map_add, hy, hz])
      (fun y _ hy ↦ by simp only [map_inv₀, hy])
      (fun y z _ _ hy hz ↦ by simp only [map_mul, hy, hz]) hab
  let e₀ : Gal(Ls/L) ≃* Gal(Ks/K) := MulEquiv.ofBijective r ⟨hinj, hsurj⟩
  let h : Gal(Ls/L) ≃ₜ Gal(Ks/K) :=
    (isHomeomorph_iff_continuous_bijective.mpr ⟨hc, hinj, hsurj⟩).homeomorph
  let e : Gal(Ls/L) ≃ₜ* Gal(Ks/K) :=
    { e₀ with continuous_toFun := hc, continuous_invFun := h.continuous_invFun }
  have he : ∀ (σ : Gal(Ls/L)) (x : Ks),
      algebraMap Ks Ls (e σ x) = σ (algebraMap Ks Ls x) := hr
  have : (upperStar AddCommGrpCat.{u + 1}
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).IsEquivalence :=
    upperStar_isEquivalence_of_galoisRestriction K L Ks Ls e he
  refine ⟨⟨e, he⟩, ?_, ?_⟩
  · intro F _ q
    exact Sheaf.H.mapFunctor_bijective _ _ F q
  · intro F G _ _ φ q x
    exact cohomologyMap_map _ q φ x

end AlgebraicGeometry.Etale
