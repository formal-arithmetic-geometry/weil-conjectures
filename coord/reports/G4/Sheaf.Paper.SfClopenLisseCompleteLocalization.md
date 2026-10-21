## What changed

The assigned theorem is assembled from five independent results. Four are proved:
`sf_clopen_cover_geometry` (covering sieves refine to finite clopen partitions and
clopen components inherit categorical weak contractibility),
`sf_clopen_lisse_partition` (simultaneous finite free local models),
`sf_weakly_contractible_projective` (exact module evaluation and finite free
projectivity in the independent coefficient universe), and
`sf_clopen_coefficient_comparison` (normalized finite/completed coefficients and
exact ordinary restriction). The fifth isolates normalized derived quotient,
Roos completeness and objectwise Tor compatibility.

The existing definitions and structures were extracted verbatim to
`Sheaf.Paper.SfClopenRestrictionData`, publicly re-exported by the assigned module.
This avoids an import cycle between the theorem and its helper modules. The
interface block, including all bodies and signatures, is byte-identical to the
original; no target statement or mathematical definition changes. The change
record is `coord/changes/sf-clopen-interface-extraction.md`. There are no adapted
external consumers and no source-library changes.

The geometry proof constructs a section of a represented cover using terminal
set-sheaf evaluation, refines arbitrary sieves by finite affine families, pulls
back the disjoint coproduct components, and treats clopen inheritance by adding
the complement. The projectivity proof works directly through the module unit's
section correspondence, rather than importing an evaluation theorem whose
coefficient universe is fixed to the site universe. The coefficient proof uses
continuous/cocontinuous localization, sheafification of constants, and the actual
inverse limit cone; its section, transition and projection squares are proved.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.sf_clopen_lisse_complete_localization`
(node `lem-sf-clopen-lisse-complete-localization`). Its assembly proof has no holes.

Added one hole, in
`WeilConjectures.sf_clopen_derived_compatibility`
(node `lem-sf-clopen-derived-compatibility`, module
`Sheaf.Paper.SfClopenDerivedCompatibility`). This is the only `sorry` in the
packet. It is a separate clopen derived base-change result: it assumes only a
clopen and the normalized exact coefficient datum, and establishes the remaining
derived fields. It does not repeat the partition, free-model, weak-contractibility,
projectivity, or coefficient-existence conclusions of the assigned theorem.
Its docstring gives the construction and proof in words, including the all-complex
counit square and the augmented tower normalization.

The following new public theorems have complete Lean proofs:
`WeilConjectures.sf_clopen_cover_geometry`,
`WeilConjectures.sf_clopen_lisse_partition`,
`WeilConjectures.sf_weakly_contractible_projective`, and
`WeilConjectures.sf_clopen_coefficient_comparison`.
All private helpers are proved. No hole occurs in any definition or instance.
The combined `lcompile.py --all` check compiled all seven packet modules with no
errors or warnings; the slowest fresh file took 12.3 seconds. The unchanged
interface block and theorem signature were compared mechanically, and the updated
DAG dependency closure was checked for cycles (420 reachable nodes).

This is a decomposition: one original hole closed, one separate hole added,
net zero holes removed. The four geometric/coefficient parts are proved, but the
entire assigned result is not axiom-free until the derived lemma and any inherited
library holes are proved.

## No longer needed

The original direct proof imports removed from the assigned module are:

- `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted` (its definitions are
  already available through the unchanged public tower imports).
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
  (kept as a planned dependency of the separate derived lemma, not the assembly).
- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`
  (now a private import of the coefficient proof, and transitive in tensor calculus).
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
  (not used: no slice equivalence is needed; the reviewer removed the unused private
  import from the interface module. The coefficient argument uses
  `clopenRingRestriction` of `lem-pur-clopen-ringed-module-gluing`, now recorded as the
  proof dependency of `lem-sf-clopen-coefficient-comparison`).
- `Sheaf.AlgebraicGeometry.ProEtaleConstantModuleRestriction`
  (now privately imported by the lisse partition proof).
- `Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`
  (not used; the covering epi and section are proved directly).
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact`
  (not used; exact evaluation and projectivity are proved in the required universe).
- `Mathlib.CategoryTheory.Sites.LocallySurjective`,
  `Mathlib.CategoryTheory.Yoneda`, and `Mathlib.AlgebraicGeometry.Limits`
  (imported where the geometric proof actually needs them).

The direct dependency nodes
`lem-weil-pbc-proetale-finite-coproduct-evaluation`,
`lem-weil-pbc-proetale-weakly-contractible-evaluation-exact`, and
`lem-galois-yoneda-hom-bijection` are unnecessary for this route. Their generic
Mathlib APIs or the direct arguments above replace them. No existing module is
withdrawn: other parents may still require these nodes.

All nine obsolete top-level `tool_uses` entries were removed from the assigned
node because its proof now applies the five helper theorems. They were
`lem-pur-clopen-ringed-module-gluing`,
`lem-pur-finite-product-derived-tensor-calculus`,
`lem-weil-pbc-proetale-weakly-contractible-evaluation-exact`,
`lem-weil-proetale-weakly-etale-localization`,
`lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`,
`lem-weil-pbc-proetale-subcanonical`,
`lem-weil-pbc-proetale-finite-coproduct-evaluation`,
`lem-weil-pbc-morphism-factors-through-open-subscheme`, and
`lem-pe-constant-module-restriction-universes`. Several remain dependencies of
helper nodes; removing these direct approvals does not assert they are globally
unused. The new nodes record those uses explicitly. The blueprint assembly
remark has no prescribed proof-step route that this refinement bypasses.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The blueprint search for clopen statements found
`det-pe-wcb-clopen-partition`, whose hypothesis is a w-contractible ring and whose
conclusion is a chosen-cover partition. The new geometry theorem instead starts
from categorical terminal evaluation and also proves clopen inheritance in an
independent universe; the existing statement does not supply these inputs or
conclusions. The nearest blueprint ancestor remains `lem-fix-weil-operations`.

Two interface issues require explicit handling.
First, the original module's public conclusion asks for arbitrary independent
ring-sheaf universes, whereas the existing evaluation theorem is at a fixed
coefficient universe. The direct proof here handles exactly the requested
universe, and clopen inheritance changes universes by the generic weakly
contractible-site criterion. Second, the original module combines data and its
existence theorem, so a new derived helper using that data would create an import
cycle without the verbatim interface extraction.

The derived tensor-calculus theorem supplies comparisons for arbitrary universal
presentations and a representative counit square on K-flat inputs. It does not
immediately supply the assigned interface's square on every complex, nor its
actual quotient/tower normalizations. The separate derived node records that
remaining argument instead of silently weakening those fields.

## New nodes

`lem-sf-clopen-cover-geometry`: proved finite clopen refinement of any covering
sieve and inheritance of categorical weak contractibility by a clopen component.
The geometric construction includes empty opens and the empty scheme.

`lem-sf-clopen-lisse-partition`: proved common finite clopen free partition for a
finite family of finite-model lisse sheaves over a field. Finite intersection of
covering sieves includes the empty family; zero ranks are permitted.

`lem-sf-weakly-contractible-projective`: proved exact terminal evaluation and
projectivity of finite products of unit module sheaves, for arbitrary ring
sheaves in the specified universe. The empty product is covered by the biproduct
argument.

`lem-sf-clopen-coefficient-comparison`: proved normalized constant finite and
completed coefficient isomorphisms and exact ordinary restriction, for every
open subscheme, without a clopen or weak-contractibility hypothesis.

`lem-sf-clopen-derived-compatibility`: the only new hole, asserting normalized
clopen derived quotient/tower base change, preservation of completeness and the
same objectwise residue Tor interval. The source, edge cases, and full proof in
words are in its docstring and DAG node.

`def-sf-clopen-restriction-data`: records the verbatim interface extraction;
all definitions are real constructions with no holes. See
`coord/changes/sf-clopen-interface-extraction.md` for the old/new blocks and user
check.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
