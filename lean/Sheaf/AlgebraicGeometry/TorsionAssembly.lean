/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import WeilConjectures.SixFunctors.BaseChange.Derived
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf

/-!
# Torsion coefficient assembly for proper base change

Source: Stacks Project, Tag 095T, and Tag 0A4B, proof paragraphs 1–3;
blueprint `sec-proper-base-change/sk-thm-properbasechange`
(blueprint: lemma-weil-pbc-torsion-assembly).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a cartesian square with `f` proper and arbitrary `g`, the specified derived
exchange on a torsion abelian sheaf placed in degree zero is an isomorphism, as is its
map on every cohomology sheaf. Exactness of inverse image identifies the latter map with
`g⁻¹ Rᵖf_* F → Rᵖf'_* g'⁻¹ F`; higher direct images mean cohomology of derived direct image.
Source: Stacks Project, Tag 095T; Tag 0A4B, proof paragraphs 1–3
(blueprint: lemma-weil-pbc-torsion-assembly).

Proof, following the node's nine steps:
0. By `lem-weil-pbc-derived-plus-iso-on-cohomology`, reduce to exchange on all cohomology
sheaves. Exactness of inverse image (`prop-weil-pbc-inverse-image-exact`,
`lem-weil-pbc-exact-functor-bounded-below`) identifies these with higher direct images.
1. For a sheaf killed by a prime, apply `lemma-weil-pbc-prime-proper-base-change`.
2. If `n = r n'` kills `G`, with `r` prime, use the short exact sequence
`0 → G[r] → G → G/G[r] → 0`. Its kernel is killed by `r`, and its quotient by `n'`,
since multiplication by `n'` factors through `G[r]` and the quotient map is epic.
3. This sequence gives a distinguished triangle (`lem-sf-derived-ses-triangle`). Both
composites of derived direct image and inverse image are triangulated, by
`lem-weil-pbc-derived-direct-image-triangulated` and
`lem-sf-exact-functor-derived-triangulated`. Exchange gives a morphism of these triangles
by `lem-weil-pbc-derived-exchange-triangulated`.
4. Apply their long exact cohomology sequences (`lem-sf-derived-homology-long-exact`),
the commuting ladder (`lem-weil-pbc-derived-cohomology-ladder`) and the five lemma
(`lem-weil-pbc-five-lemma`) to transfer the result from the kernel and quotient to `G`.
5. Induct on the number of prime factors of `n`. For `n = 1`, `G` is zero; otherwise
Steps 1–4 reduce to fewer prime factors.
6. Write the torsion sheaf as the colimit of `F[n]`. Properness implies quasi-compactness
and quasi-separatedness (`pqf-lem-proper-basic`), so higher direct images commute with
this colimit (`lemma-weil-pbc-direct-image-filtered-colimit`). Inverse image commutes
with colimits (`lem-weil-pbc-inverse-image-preserves-colimits`), giving the source-side
cohomology comparison isomorphism. Negative degrees vanish.
7. The base changed morphism is proper (`lem-weil-pbc-proper-base-change`); apply the
same argument to the target side, since inverse image preserves the colimit and the
annihilation of `F[n]` by `n`.
8. Naturality of the specified exchange (`def-weil-pbc-derived-exchange`) identifies
exchange on cohomology of `F` with the colimit of the isomorphisms for `F[n]`, conjugated
by the comparison isomorphisms of Steps 6–7. Thus all cohomology maps are isomorphisms;
Step 0 gives the derived isomorphism. -/
theorem isIso_derivedBaseChangeMapPlus_torsion_assembly
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f] (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ∧
    ∀ p : ℤ, IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
