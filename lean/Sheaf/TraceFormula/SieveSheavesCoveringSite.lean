/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Sheaf.CategoryTheory.SmallSetOfCoveringFamilies

/-!
# Covering-family presentation of a sieve sheaf category

Source: Stacks Project, `literature/stacks-project/sites.tex`, Tags 03CI and 03A1,
with the arbitrary-sieve extension described in the node source
(blueprint: lem-trf-sieve-sheaves-covering-site).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/--
Source: Stacks Project, `literature/stacks-project/sites.tex`, Tags 03CI and 03A1,
with Tag 00ZM for sheafification (blueprint: lem-trf-sieve-sheaves-covering-site).

Proof plan, step by step. (1) Use `lem-trf-sieve-set-sheafification-exists` and
`lem-cbc-set-presheaf-sheafification-local-bijection` to obtain sheafification
and its local representation and local equality properties. (2) In the sheaf
category, limits are sectionwise; start with the terminal sheaf and sheafified
representables, and close under one sectionwise pullback for every cospan at
successive countable stages. The size convention gives a `w`-small full
pullback-closed category. (3) Define a family to cover when its lifting sieve
for every section is `J`-covering. Isomorphism, pullback, and composition follow
from the three topology axioms; the pullback argument uses the pullbacks built
in (2), and it also covers empty and repeated-index families. (4) Apply
`lem-weil-pbc-small-set-of-covering-families` to choose a `w`-small,
axiom-closed representative set. The generated sieve topology is equivalent
to local lifting, by the representative property and the three axioms. (5) The
adjunction and `lem-galois-yoneda-hom-bijection` identify maps from each
sheafified representable with sections, defining the functor from the original
site and fixing its action on arrows. (6) A covering sieve in the original site
maps to a covering sieve in the replacement by local representation and
pullback stability. (7) Conversely, local lifting of the identity section in
the replacement, followed by local representation and local equality, forces
the original sieve to cover; hence the functor preserves and reflects covers.
(8) The same section formula proves cover density, local fullness, and local
faithfulness. (9) Apply `lem-trf-sieve-dense-subsite-comparison` to obtain the
equivalence of the two sieve-sheaf categories; the coefficient category is
`Type w` and both sites are `w`-small. (10) Finally, a matching family on a
covering family is exactly a matching family on its generated sieve: pairwise
pullbacks make the factorization formula well-defined, and pullback stability
and uniqueness give the converse. Thus the generated-topology sheaves are
precisely the covering-family sheaves, and the replacement has the required
covering pullbacks.
-/
theorem exists_coveringSite_of_sieveTopology
    (D : Type w) [SmallCategory D] (J : GrothendieckTopology D) :
    ∃ (S : Type w) (_ : SmallCategory S) (K : Precoverage S),
      K.IsSiteForCoverings ∧
        Nonempty (Sheaf J (Type w) ≌ Sheaf K.toGrothendieck (Type w)) := by
  sorry

end CategoryTheory
