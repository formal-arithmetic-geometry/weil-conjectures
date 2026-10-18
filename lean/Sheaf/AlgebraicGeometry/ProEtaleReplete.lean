/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RepleteSheafTopos

/-!
# Repleteness of the pro-étale topos

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-prop-pe-replete/det-pe-replete-epimorphism.md`
(blueprint: det-pe-replete-epimorphism).
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry.Scheme

/-- Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-prop-pe-replete/det-pe-replete-epimorphism.md`, node `det-pe-replete-epimorphism`
(blueprint: det-pe-replete-epimorphism).

For every scheme, the topos of set-valued sheaves on its small pro-étale site is
replete: inverse sequences with epimorphic transition maps have epimorphic limit
projections at every natural-number index.

Proof:
1. Fix an inverse sequence `F` with epimorphic adjacent maps and an index `m`.
   By `det-pe-replete-definition` and the local-surjectivity criterion
   `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`, it suffices to lift each
   section `y` of `F_m` over an arbitrary site object `U` after a covering of `U`.
2. By `det-pe-wcb-cover`, cover `U` by affines `W_i = Spec D_i`, with each `D_i`
   w-contractible. By `det-pe-weak-contractible-equivalences`, each `W_i` is weakly
   contractible. This applies to arbitrary `U`, without quasi-compactness assumptions.
3. Apply `det-pe-replete-on-contractible` to the original sequence and each `W_i`.
   The map on sections of the limit projection at `m` is surjective there, so the
   restriction of `y` lifts to a section of the limit over `W_i`.
4. These separate lifts make the projection locally surjective, hence epimorphic by
   `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`. No compatibility on overlaps
   is required. Since the sequence and `m` were arbitrary, the topos is replete.
-/
theorem isReplete_proEtale (X : Scheme.{u}) :
    CategoryTheory.GrothendieckTopology.IsReplete.{u + 1, u, w} (ProEt.topology X) := by
  sorry

end AlgebraicGeometry.Scheme
