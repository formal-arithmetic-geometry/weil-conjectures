/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.DenseEmbedding
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Étale comparison for dense extensions of henselian valued fields

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XX, section 4.4,
printed page 374, the dense henselian valued field comparison and its displayed
Galois-group isomorphism (blueprint: lem-per-dense-henselian-field-etale-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v w a b

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A dense inclusion of nontrivially valued henselian fields identifies their absolute
Galois groups with their Krull topologies and preserves torsion étale cohomology naturally.
The two valuation rings are the existing valuation integer subrings. `IsDenseInducing`
expresses both the induced valuation topology and density. The towers express compatibility
of the chosen separable closures. The equation characterizing `e` says that it is restriction
along their embedding, rather than an unspecified isomorphism. The cohomology map is the
canonical inverse-image map; `Sheaf.H` is the existing abelian-sheaf cohomology convention.

Source: ILO, Travaux de Gabber, Exposé XX, section 4.4, printed page 374, displayed
Galois comparison and the preceding reduction to cohomology of fraction fields.
(blueprint: lem-per-dense-henselian-field-etale-comparison)

Proof (the node's nine steps):
1. Every `a ∈ K'` separable algebraic over K lies in K. Put `E = K(a)`. By
   lem-per-henselian-finite-extension-topology the topology of E inherited from K' is that of
   the unique prolonged henselian valuation. Embed E in a finite Galois `N/K`
   (lem-weil-pbc-finite-galois-receiving-separable-extensions). By
   lem-per-henselian-krasner-neighbourhood a small open neighbourhood of a in N consists of b
   with `a ∈ K(b)`; its trace on E is open. K is dense in E, so choose such b in K: then
   `a ∈ K(b) = K`. Only equality of valuation topologies is used.
2. Every monic separable irreducible `h ∈ K[T]` stays irreducible over K': the coefficients
   of a proper factor over K' are symmetric functions of roots of h in `Ks`
   (lem-trf-separable-polynomial-linear-factorization,
   lem-weil-pbc-separable-closure-exists-galois), hence lie in K by step 1. So for finite
   separable `L = K(t)` (lem-weil-pbc-finite-separable-primitive-element), `K' ⊗_K L` is the
   field `K'[T]/(min_t)`, isomorphic to the compositum `K'L`.
3. Fix `θ ∈ K's`, `L = K'(θ)`, minimal polynomial f over K' of degree `n > 1`. Take a finite
   Galois `N/K'` containing L, prolong the valuation
   (lem-per-henselian-finite-extension-topology), take the Krasner neighbourhood U of θ
   (lem-per-henselian-krasner-neighbourhood), and apply
   lem-per-henselian-simple-root-stability over L to f, θ and `U ∩ L`. Approximating the
   coefficients of f by elements of K (density) gives monic `g ∈ K[T]` of degree n with a
   simple root `β ∈ U ∩ L`.
4. Then `θ ∈ K'(β)`, so `K'(β) = L`, g is the minimal polynomial of β over K', irreducible
   over K' and K, and separable since `g'(β) ≠ 0`. Hence β lies in the image of `Ks`
   (lem-trf-separable-polynomial-linear-factorization), and `K's = K' · Ks`.
5. By step 2 on finite subextensions, `K' ⊗_K Ks → K' · Ks` is injective with field image,
   the whole compositum. For `σ ∈ Gal(Ks/K)`, `1 ⊗ σ` extends σ to `K's` fixing K'; an
   automorphism fixing K' and Ks is the identity. Restriction is a bijective homomorphism,
   characterized by the displayed equation.
6. Stabilizers of finite `S ⊂ Ks` pull back to stabilizers of S; a finite `T ⊂ K's` is
   expressed from K' and a finite `S ⊂ Ks`, so stabilizers of T contain extensions of the
   stabilizer of S. Restriction and its inverse are continuous for the Krull topologies.
7. Let `u : Spec K' → Spec K` and B base change of small étale sites. Each étale K-scheme is
   a disjoint union of spectra of finite separable extensions
   (lem-weil-pbc-etale-fibre-discrete-separable-points), whose K-embeddings into `K's` land
   in `Ks`. Geometric fibres of `B(X)` and X correspond equivariantly along step 6; by
   lem-exc-etale-field-gsets, B is an equivalence preserving and reflecting coverings.
8. By lem-weil-pbc-site-equivalence-is-morphism-of-sites, precomposition along B is `u_*`
   (def-weil-pbc-direct-image), an equivalence; its left adjoint `u^{-1}` = `upperStar`
   (def-weil-pbc-inverse-image) is a quasi-inverse, so the unit `1 → u_* u^{-1}` is an
   isomorphism and gives the pullback isomorphism on global sections.
9. By lem-weil-pbc-equivalence-injective-resolutions, `u^{-1}` carries an injective
   resolution of G to one of `u^{-1} G`; step 8 makes the induced map of section complexes an
   isomorphism, hence `cohomologyMap` is bijective in every degree q (including `q = 0`), for
   every torsion G (def-weil-pbc-cohomology-pullback). Naturality in G is
   lem-weil-pbc-cohomology-pullback-functorial. No completeness, discreteness or residue
   characteristic condition is used.
-/
theorem denseHenselianField_etaleComparison
    (K K' : Type u) [Field K] [Field K'] [Algebra K K']
    (Γ : Type a) (Γ' : Type b)
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Γ']
    [vK : Valued K Γ] [vK' : Valued K' Γ']
    [HenselianLocalRing vK.v.integer] [HenselianLocalRing vK'.v.integer]
    (hK : ∃ x : K, x ≠ 0 ∧ vK.v x ≠ 1)
    (hK' : ∃ x : K', x ≠ 0 ∧ vK'.v x ≠ 1)
    (h_dense : IsDenseInducing (algebraMap K K'))
    (Ks : Type v) (K's : Type w) [Field Ks] [Field K's]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra K' K's] [IsSepClosure K' K's]
    [Algebra K K's] [IsScalarTower K K' K's]
    [Algebra Ks K's] [IsScalarTower K Ks K's] :
    (∃ e : Gal(K's / K') ≃ₜ* Gal(Ks / K),
      ∀ (σ : Gal(K's / K')) (x : Ks), algebraMap Ks K's (e σ x) = σ (algebraMap Ks K's x)) ∧
    ∀ (G : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      G.IsTorsion → ∀ q : ℕ,
      Function.Bijective (cohomologyMap
        (Spec.map (CommRingCat.ofHom (algebraMap K K'))) G q) ∧
      ∀ (H : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}),
        H.IsTorsion → ∀ (φ : G ⟶ H) (x : Sheaf.H G q),
        cohomologyMap (Spec.map (CommRingCat.ofHom (algebraMap K K'))) H q
            (Sheaf.H.map φ q x) =
          Sheaf.H.map
            ((upperStar AddCommGrpCat.{u + 1}
              (Spec.map (CommRingCat.ofHom (algebraMap K K')))).map φ) q
            (cohomologyMap (Spec.map (CommRingCat.ofHom (algebraMap K K'))) G q x) := by
  sorry

end AlgebraicGeometry.Etale
