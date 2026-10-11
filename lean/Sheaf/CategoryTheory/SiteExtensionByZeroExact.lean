/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Exactness of extension by zero on a localized site

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Lemma 03DJ
(blueprint: lem-weil-pbc-site-extension-by-zero-exact)

This statement asserts preservation of short exact sequences by the constructed left
adjoint to restriction recorded by the restriction-adjunction dependency.
The proof follows the direct-sum
presheaf construction of 03DH--03DJ, sectionwise injectivity, exact sheafification,
and right exactness from the adjunction.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Extension by zero from the localized site is exact.

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Lemma 03DJ
(blueprint: lem-weil-pbc-site-extension-by-zero-exact).

The site is the precoverage encoding of `def-weil-pbc-sites-and-cohomology`.
Extension by zero is the constructed left adjoint recorded by
`lem-weil-pbc-site-restriction-adjunction`. The zero-morphism witness permits mapping
short complexes; it is a conclusion, not an additional hypothesis.

Proof:
1. By `def-weil-pbc-site-extension-by-zero-presheaf`, extension at `V` is the direct
   sum over maps `V → W`; its action on a morphism is the direct sum of the component
   maps, so the construction is additive.
2. A monomorphism of sheaves is sectionwise injective: the inclusion preserves
   kernels, using `lem-weil-pbc-sheafification-exact`, and presheaf evaluation is
   exact by `lem-weil-pbc-abelian-presheaves-evaluation-exact`. In the direct-sum map,
   each component of a finite-support kernel element therefore vanishes.
3. Exact sheafification (`lem-weil-pbc-sheafification-exact`) preserves the zero
   kernel, so the sheafified direct-sum functor preserves monomorphisms.
4. The last map of a short exact sequence is a cokernel of the first by
   `lem-weil-pbc-abelian-exact-epi-cokernel`. The sheafified direct-sum construction
   is left adjoint to restriction by `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`,
   hence preserves this cokernel by `lem-weil-pbc-left-adjoint-preserves-colimits`.
5. The monomorphism and its cokernel form a short exact sequence, by
   `lem-weil-pbc-abelian-exact-epi-cokernel`. Uniqueness of left adjoints identifies
   the sheafified direct-sum construction with the recorded extension-by-zero functor
   (`lem-weil-pbc-site-extension-by-zero-presheaf-adjoint` and
   `lem-weil-pbc-site-restriction-adjunction`). Transfer short exactness along that
   natural isomorphism. -/
theorem site_extensionByZero_exact
    {C : Type u} [SmallCategory C]
    (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (W : C) :
    ∃ (hL : (Functor.sheafPullbackConstruction.sheafPullback
      (Over.forget W) AddCommGrpCat.{u} (J.toGrothendieck.over W)
      J.toGrothendieck).PreservesZeroMorphisms),
      ∀ (S : ShortComplex (Sheaf (J.toGrothendieck.over W) AddCommGrpCat.{u})),
        S.ShortExact →
          (@ShortComplex.map _ _ _ _ _ _ S
            (Functor.sheafPullbackConstruction.sheafPullback
              (Over.forget W) AddCommGrpCat.{u} (J.toGrothendieck.over W)
              J.toGrothendieck) hL).ShortExact := by
  sorry

end CategoryTheory
