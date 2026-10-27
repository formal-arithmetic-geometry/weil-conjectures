/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.ModuliStackProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import Sheaf.TraceFormula.ProjectiveBundleProper
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine

/-! # Coarse moduli schemes for curves with abelian level structure

Source: Pikaart--de Jong, Moduli of curves with non-abelian level structure,
§2.3 preceding Theorem 2.3.2, Theorem 2.3.2(1), and §2.3.3
(blueprint: lem-sfb-abelian-level-coarse-moduli).

The stack is the recorded category of unpointed smooth projective genus-`g` families
with a full rank-`2g` frame in degree-one étale cohomology. No symplectic condition
or choice of roots of unity is imposed. The conclusion asserts coarse moduli only.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Abelian-level curves form a separated smooth finite-type DM stack and admit a
separated finite-type coarse moduli scheme over the given field.
Source: Pikaart--de Jong §2.3, Theorem 2.3.2(1), and §2.3.3
(blueprint: lem-sfb-abelian-level-coarse-moduli).

Proof:
1. `lem-sfb-unpointed-stable-coarse-projective` gives the smooth DM stable stack
and its open smooth-curve substack. `lem-sfb-stable-isom-finite-unramified`
gives finite type and finite diagonal. Restrict by the open-substack clause of
`lem-sfb-dm-open-finite-etale-permanence` to obtain these properties for smooth curves.
2. For a test family, `lem-trf-projective-bundle-proper` gives properness, and
`lem-sfb-smooth-proper-finite-cohomology-local-system` gives the finite locally
constant degree-one cohomology sheaf. `lemma-weil-pbc-prime-proper-base-change`
identifies its pullbacks with the cohomology of every base-changed family.
3. Locally trivialize that sheaf. The frame sheaf is then the constant finite
set of module isomorphisms from the rank-`2g` module, possibly empty.
`lem-galois-flc-representable` represents it by a finite étale scheme, compatibly
with pullback by `lem-galois-inverse-image-representable` and step 2. The fibre
of the forgetful functor is this discrete frame groupoid: transport a frame
along its specified family isomorphism; an arrow compatible with that isomorphism
is unique. Thus the forgetful functor is representable finite étale.
4. Apply the decoration clause of `lem-sfb-dm-open-finite-etale-permanence`.
This gives the smooth finite-type DM stack and its finite, hence proper, diagonal.
The atlas and proper-diagonal definitions below retain the actual projections.
5. A geometric automorphism preserving the frame acts identically on degree-one
cohomology. `lem-sfb-geometric-curve-level-faithfulness` then makes it the identity,
using `g ≥ 2`, prime level at least three, and invertibility on the base.
6. Restrict the projective stable coarse scheme to the smooth open using
`lem-sfb-coarse-moduli-open-restriction`. Apply
`lem-sfb-inertia-free-finite-cover-coarse` to the finite forgetful map and step 5.
The resulting scheme is finite over that open coarse scheme and represents the
level stack. This is the scheme-existence argument, not merely algebraic-space existence.
7. Take its representing equivalence as the coarse map. Composition identifies
maps to every algebraic space, and geometric fibres identify isomorphism classes
with scheme points. The identity atlas transfers finite type to the scheme;
its diagonal is the stack diagonal, so the scheme is separated. -/
theorem abelian_level_coarse_moduli (k : Type u) [Field k] (g : ℕ) (hg : 2 ≤ g)
    (ℓ : AbelianLevelPrime (Spec (.of k))) :
    IsDeligneMumfordModuliStack
      (BasedCategory.ofFunctor (AbelianLevelModuli.forget (Spec (.of k)) g ℓ)) ∧
    HasProperModuliDiagonal
      (BasedCategory.ofFunctor (AbelianLevelModuli.forget (Spec (.of k)) g ℓ)) ∧
    HasSmoothFiniteTypeModuliAtlas
      (BasedCategory.ofFunctor (AbelianLevelModuli.forget (Spec (.of k)) g ℓ)) ∧
    ∃ (C : Over (Spec (.of k)))
      (c : BasedFunctor
        (BasedCategory.ofFunctor (AbelianLevelModuli.forget (Spec (.of k)) g ℓ))
        (discreteModuli (yoneda.obj C))),
      IsCoarseModuliScheme
        (BasedCategory.ofFunctor (AbelianLevelModuli.forget (Spec (.of k)) g ℓ)) C c ∧
      IsSeparated C.hom ∧ LocallyOfFiniteType C.hom ∧ QuasiCompact C.hom := by
  sorry

end AlgebraicGeometry
