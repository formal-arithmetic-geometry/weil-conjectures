/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.ModuleHomComplex
import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Sheaf.CategoryTheory.RingedSiteDualityMaps

/-!
# Derived biduality for perfect ring complexes

Source: Stacks Project, `more-algebra.tex`, Tag 07VI (blueprint:
lem-trf-perfect-complex-derived-biduality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace DerivedCategory

/--
Source: Stacks Project, `more-algebra.tex`, Tag 07VI, lemma-dual-perfect-complex
(blueprint: lem-trf-perfect-complex-derived-biduality).

For a commutative ring `B`, a perfect object `C` of `D(B)` has perfect derived
internal Hom into `B`, and its canonical evaluation map to the double derived
internal Hom is an isomorphism. The canonical map is taken for the given braiding
of `D(B)`; the statement holds for every braiding instance.

Proof (the node's steps):

1. By `def-pc-perfect-ring-complex` choose a bounded cochain complex `P` of finitely
   generated projective `B`-modules, zero outside `[a, b]`, and `e : Q P ≅ C`. View
   `B`-modules as module sheaves on the one-object site with the bottom topology (as in
   `def-pc-perfect-rhom-base-change-map` for `B → B`); evaluation at the object and the
   constant construction are inverse and identify complexes, quasi-isomorphisms,
   localizations and the K-injective derived Hom. Write `H` for the product total Hom
   complex (`def-sc-module-total-hom-complex`).
2. Put `E = H(P, B[0])`. In degree `r` only the factor `E^r = Hom_B(P^{-r}, B)` can be
   nonzero, with differential `d_E^r φ = (-1)^{r+1} φ ∘ d_P^{-r-1}`; so `E` vanishes
   outside `[-b, -a]` and has finitely generated projective terms
   (`lem-sf-finite-projective-dual`). By `lem-pod-projective-hom-evaluation-model`,
   `Q E ≅ RHom_B(Q P, B) ≅ RHom_B(C, B)`, so the dual is perfect: the first clause.
3. `P` and `E` are bounded above and termwise projective, so
   `lem-pod-projective-hom-evaluation-model` makes `H(P, B[0]) → H(P, I(B[0]))` and
   `H(E, B[0]) → H(E, I(B[0]))` quasi-isomorphisms (their localizations are invertible,
   and a map with invertible localization is a quasi-isomorphism by the cohomology
   factorization of `def-weil-abstract-derived-category`); here `I` is the K-injective
   resolution of `def-pur-derived-internal-hom`. Thus `Q H(E, B[0])` represents the double
   derived dual with the representative identifications of
   `lem-sfb-ringed-site-duality-maps`, whose bidual clause needs no K-flatness.
4. Under these comparisons `lem-sfb-ringed-site-duality-maps` represents the canonical
   bidual map by `δ_P : P → H(E, B[0])`, `x ↦ (φ ↦ (-1)^{p|φ|} φ(x))` for `x ∈ P^p`.
   Only `|φ| = -p` contributes, so in degree `p` it is `(-1)^p` times the evaluation
   `P^p → (P^p)^{**}`, an isomorphism by `lem-sf-finite-projective-dual`. The sign makes
   `δ_P` a chain map: for `φ ∈ E^{-p-1}`, `d_E φ = (-1)^p φ ∘ d_P`, hence
   `(d δ_P(x))(φ) = -(-1)^p δ_P(x)(d_E φ) = (-1)^{p+1} φ(d_P x) = δ_P(d_P x)(φ)`.
   The degreewise inverses form an inverse chain map, so `δ_P` is a chain isomorphism
   and its localization is invertible.
5. The canonical bidual map is natural and the representative comparisons are natural
   in both variables: `b_C ∘ e = RHom(RHom(e, B), B) ∘ b_{Q P}`. Here `b_{Q P}` is
   invertible by Step 4 and the other two factors are images of isomorphisms, so `b_C`
   is invertible: the second clause. The zero ring, the zero complex and an odd shift of
   a finite projective module obey the same formulas (in odd degree the component is
   `-1` times the evaluation).
-/
theorem perfectComplexDerivedBiduality
    {B : Type u} [CommRing B]
    [HasDerivedCategory.{u} (ModuleCat.{u} B)]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} B))]
    {C : DerivedCategory (ModuleCat.{u} B)}
    (hC : IsPerfectRingComplex C) :
    IsPerfectRingComplex
      ((ihom C).obj (𝟙_ (DerivedCategory (ModuleCat.{u} B)))) ∧
      IsIso (MonoidalClosed.toIhomIhomUnit C) := by
  sorry

end DerivedCategory
