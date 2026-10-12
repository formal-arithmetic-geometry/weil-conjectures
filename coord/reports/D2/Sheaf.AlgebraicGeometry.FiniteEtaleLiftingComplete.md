## What changed

Replaced the single sorry in `AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_isAdicComplete`
with a complete Lean reduction following the complete Noetherian paragraph of Stacks Tag 0GS2
(https://stacks.math.columbia.edu/tag/0GS2, read directly; the local literature files are absent).
The existing target signature and docstring are unchanged.

The proof obtains a compatible finite étale infinitesimal system, applies the existing
`AlgebraicGeometry.algebraize_finite_over_proper`, transfers étaleness through its isomorphisms,
and applies a proper-source infinitesimal étaleness criterion. It then constructs the requested
finite étale over-object and composes the closed-fibre isomorphisms. A proved private equality
induction helper transports the isomorphism from I^1 to I; ordinary simplification cannot
traverse the dependent pullback expressions through the module boundary.

Two new modules state strictly intermediate obligations. The first constructs only the formal
system, with no completeness or properness hypotheses and no algebraization conclusion. The
second proves only étaleness of an already supplied morphism, with no lifting conclusion.
The existing algebraization theorem remains the actual bridge between these obligations.
The target node's proof, proof_deps and proof_origin were updated to match this reduction.
No existing definitions, statements, public imports, or target signatures were changed.

## Proved and sorry left

The item's sole sorry is closed:
`AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_isAdicComplete`.
`transport_closed_fibre_iso` is a proved private helper (no sorry).

Exactly two new named sorries are left in this delivery:

- `AlgebraicGeometry.exists_finiteEtale_infinitesimal_system`, node
  `lem-weil-pbc-finite-etale-infinitesimal-system`, module
  `Sheaf.AlgebraicGeometry.FiniteEtaleInfinitesimalSystem`.
- `AlgebraicGeometry.etale_of_infinitesimal_restrictions_of_proper`, node
  `lem-weil-pbc-etale-infinitesimal-restrictions-proper`, module
  `Sheaf.AlgebraicGeometry.EtaleOfInfinitesimalRestrictionsProper`.

Both have proofs exactly `by sorry`, complete natural-language arguments in their docstrings,
and matching DAG nodes. Existing imported obligations, including algebraization, are untouched.
All three modules compile locally without warnings. The target is a reduction to these
obligations, not an assertion that its transitive axiom census is already sorry-free.

## No longer needed

Removed direct proof imports from the target module:

- `Sheaf.AlgebraicGeometry.BaseChangeConventions`
- `Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods`
- `Sheaf.AlgebraicGeometry.FiniteThickeningCartesian`
- `Sheaf.AlgebraicGeometry.Thickening`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance`

These are direct-import cleanup, not global pruning: the infinitesimal-system obligation
still needs topological invariance, finite thickenings and their base-change constructions;
the étaleness criterion still needs the infinitesimal-neighbourhood theorem and the ideal
sheaf/base-change dictionary. No mathematical node or module is claimed globally unnecessary.
The following old direct `proof_deps` are no longer direct dependencies of the target
(their mathematical uses remain inside the two split obligations or their statement context):

- `def-pc-base-change`
- `def-sbc-first-order-thickening`
- `def-sbc-ideal-sheaf-powers`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-adic-complete-jacobson-radical`
- `lem-weil-pbc-closed-immersion-base-change`
- `lem-weil-pbc-etale-infinitesimal-neighbourhoods`
- `lem-weil-pbc-surjective-base-change`
- `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`
- `lem-weil-pbc-thickening-finite-cartesian`
- `lemma-weil-pbc-universal-homeomorphism-site-equivalence`

The algebraization theorem returns compatibility of its restriction isomorphisms, but this
part of its output is unused by this caller (the input cartesian system is still essential).

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The source route is retained, including
algebraization. The infinitesimal-neighbourhood theorem uses powers of a kernel ideal sheaf,
whereas algebraization supplies restrictions via base-change by A/I^(n+1). Their identification
and the properness/specialization globalization argument are grouped in the second obligation.
The first obligation groups the nilpotent-thickening construction and recursive choices of
compatible covers. Neither is a renamed target statement.

Edge cases checked mathematically before writing the new statements: I=0 gives identity
thickenings; I=A gives empty infinitesimal fibres (and completeness forces the zero ring
in the second obligation); an empty cover yields the empty system; empty X makes the
proper-source criterion vacuous. Without completeness the globalization criterion would be
false (a proper source could lie entirely away from V(I)); the hypothesis is retained.
No Noetherianity of A is needed in the first obligation, and the second explicitly assumes
locally Noetherian Y, exactly what its neighborhood theorem needs.

Blueprint/unit check: none of the replaced subordinate steps is a unit realization in
`dag/units/sk-thm-p1.json`; the finite-étale machinery and its algebraization route are retained.
Existing cross-unit tool usage is unchanged: local Noetherianity from local finite type and
proper base change are the same Mathlib tools as before. No new cross-unit tool is introduced.
The blueprint searches for compatible finite étale covers and infinitesimal restrictions
found no duplicate blueprint statement. Repository/source searches found no direct lifting
theorem. LeanSearch returned HTTP 500 for both new obligations and is recorded unavailable;
LeanFinder and grep ran successfully, with no exact match (grep found the existing
`IsAdicComplete.le_jacobson_bot`, which the second obligation cites).

## New nodes

`lem-weil-pbc-finite-etale-infinitesimal-system` records original plan steps 1–3:
nilpotent transition thickenings, topological-invariance lifting by recursion, and finiteness
across the thickening. It supplies the actual cartesian data required by algebraization.
Its module is `lean/Sheaf/AlgebraicGeometry/FiniteEtaleInfinitesimalSystem.lean`.

`lem-weil-pbc-etale-infinitesimal-restrictions-proper` records original plan steps 6–7:
identify ideal-power neighborhoods with the base-change fibres, apply the existing
neighborhood theorem, and force its open neighborhood to be all of the source using
properness and the Jacobson-radical consequence of completeness. Its module is
`lean/Sheaf/AlgebraicGeometry/EtaleOfInfinitesimalRestrictionsProper.lean`.

No change records are needed: no existing interface was changed.

## Second reading by D2

1. Compared the target module against the repository with `diff -u`: its existing theorem
   signature and docstring are byte for byte unchanged, as are all existing public imports.
   The only Lean changes are proof imports, a proved private equality-transport helper,
   the target proof, and two new intermediate theorem modules. No definition changed.
2. Compiled all three modules in import order through `lcompile.py --all`: no errors or
   warnings. Scanned their code: no forbidden trust mechanisms, no hollow definitions,
   no sorry in the target or private helper, and exactly the two reported named sorries.
   A scratch-copy `#print axioms` check gave only propext, Classical.choice, Quot.sound
   for the helper, and those plus sorryAx for the target and both open obligations.
3. Read both split statements, their complete docstring arguments, and matching nodes.
   Checked zero/unit ideals, empty source/cover, and the necessity of completeness for
   globalization. Both are true intermediate steps: one constructs only formal covers,
   the other detects etaleness of a supplied morphism. Neither restates the lifting target.
   Independently read Stacks 0GS2, 0A43 and 09ZW online. Additional LeanFinder searches
   for nilpotent quotient inverse systems and proper-source etale-locus detection, plus
   Mathlib grep and repository rg searches, found no duplicate or direct shorter theorem.
   Read the existing topological-invariance, finite-thickening, infinitesimal-neighbourhood,
   and algebraization interfaces. Neither remaining obligation closes by a short application:
   the first needs recursive dependent pullback data; the second needs the ideal-sheaf
   power/base-change dictionary and proper specialization argument.
4. Checked the reduction from the top: it actually applies the existing algebraization
   theorem and transfers etaleness through its supplied isomorphisms. The private helper
   is equality induction only. Proof-only imports are plain imports; imports retained
   in the new modules support their signatures or documented proof routes. Checked
   `dag/units/sk-thm-p1.json` realized fields: none of the moved subordinate steps is a
   unit realization, and the unit route remains intact. The report now explicitly lists
   every old direct proof dependency removed; none is claimed globally pruned.
5. Compared the existing node JSON: only proof, proof_deps and proof_origin changed.
   Every node's proof_deps is precisely the union of its proof-step uses. Both new nodes
   have the required source, searches, creation, blueprint, chapter/unit and Lean fields;
   their recorded Lean signatures match the module text verbatim, and all referenced
   dependencies exist. The target node describes the implemented reduction accurately.

Second reading changed only this report: completed the direct-dependency removal list and
recorded the independent checks. No Lean or node repair was needed.
