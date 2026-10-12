## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.Modules.H.openFreeExtTransport` by a complete Lean proof
from three strictly smaller intermediate theorems. The existing signature,
universes, visibility, docstring, and public import are unchanged. The added
proof-only import is
`Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenRestrictionBijective`.

The argument now runs in the restriction direction. The degree-zero geometric
lemma supplies the free-object and coefficient isomorphisms and the cartesian
coefficient square. The homomorphism `Ext.restrictAddHom` is a real construction:
apply the exact restriction functor on Ext, precompose with the inverse
free-object isomorphism, and postcompose with the coefficient isomorphism.
Bijectivity makes its inverse the required transport. Injectivity of these
restriction maps proves all three equations for the inverses.

The second free-object isomorphism is explicitly constructed as
`(c.app (H.openFreeSheaf W)) ≪≫ GW.mapIso e`; it is not chosen independently of
`e`. The proof of `Ext.restrictAddHom_square` expands both restriction maps,
uses the assumed coefficient square and the generic exact-functor naturality
lemma, cancels the inverse cartesian free-object isomorphism, and reassociates
Ext composition. `Ext.restrictAddHom_comp` is fully proved from Mathlib.

All writes are confined to this sandbox. No existing dependency module, target,
definition, statement, or interface was adapted. No change record is required.
The parent DAG proof and its proof dependencies now describe this Lean argument.
All five delivery modules compile together without warnings after the width fix.
`deliver3.py U1 Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenExtTransport
--no-push` printed OK: compilation and preflight pass, with only the independent
second-reading section pending, as the worker brief requires. Nothing was pushed.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.H.openFreeExtTransport`
(node `lem-pc-open-free-ext-transport`). No sorry remains in the item module.

Added exactly three named public theorem holes, each in a separate module and
with a source, complete proof in words, and a matching DAG node:

- `AlgebraicGeometry.Scheme.Modules.H.openRestrictionData`
  (`lem-pc-open-restriction-data`, module
  `Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenRestrictionData`): only
  degree-zero sheaf isomorphisms and coefficient morphism squares; it asserts
  neither an Ext equivalence nor any Ext bijectivity.
- `AlgebraicGeometry.Scheme.Modules.H.openRestrictionExt_bijective`
  (`lem-pc-open-restriction-ext-bijective`, module
  `Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenRestrictionBijective`):
  bijectivity of the two *constructed* restriction homomorphisms. It asserts no
  scalar or base-change compatibility of independently chosen equivalences.
- `CategoryTheory.Abelian.Ext.mapExactFunctor_square`
  (`lem-pc-ext-exact-functor-square`, module
  `Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisExtFunctorSquare`): a general
  naturality identity for a natural isomorphism of composite exact functors.
  It mentions no schemes, rings, coefficient units, or Ext equivalences.

`CategoryTheory.Abelian.Ext.restrictAddHom_comp` and
`CategoryTheory.Abelian.Ext.restrictAddHom_square` have complete Lean proofs.
`CategoryTheory.Abelian.Ext.restrictAddHom` and
`AlgebraicGeometry.Scheme.Modules.H.openBaseChangeInclusion` are actual
constructions, with no admitted data or existence-witness choices. The transports
in the item's proof are inverses of bijections, which determine them uniquely.

This is a decomposition: one upper hole closed, three lower holes added, net
minus two holes before the project's pinned closure ledger calculation. It is
not an axiom-free proof of the full theorem. The statement and meaning of the
item are unchanged.

## No longer needed

No original library import or module is pruned. The original public import
`Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisFreeComplex` supplies
`H.openFreeSheaf` in the unchanged statement and must stay. Its short-exact
Mayer--Vietoris theorem is not used in this argument; only the represented free
sheaf construction is needed here.

The old direct proof dependencies on
`lem-weil-pbc-zariski-extension-by-zero-adjunction` and
`lem-weil-pbc-zariski-extension-by-zero-exact` move into the proof plan of the
bijectivity lemma. They are still needed for that argument and are not claimed
pruned. `lem-sc-ext-exact-adjunction` is used there as an already proved generic
tool; its source declaration is `CategoryTheory.Adjunction.extAddEquiv` in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective`.

All four old direct `proof_deps` are accounted for: in addition to the two
extension-by-zero nodes above, `def-pc-flat-cohomology-comparison` and
`lem-pc-free-mayer-vietoris-short-exact` supply constructions in the unchanged
signature and remain dependencies of the smaller geometric lemmas. The new
parent proof does not apply their theorems directly. They are not globally
pruned; the three replacement direct dependencies are the restriction-data,
restriction-map-calculus, and restriction-bijectivity nodes.

The rejected sandbox-only nodes
`lem-pc-open-free-ext-transport-scalar` and
`lem-pc-open-free-ext-transport-base-change`, and their corresponding modules
`MayerVietorisOpenExtScalar` and `MayerVietorisOpenExtBaseChange`, are excluded
from the delivery. Their files and earlier report are archived under
`scratchpad/earlier-attempt/`, outside the delivered trees. They never belonged
to the library, so removing them is not counted as library pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt claimed base-change compatibility for arbitrary independent
t and t'. That is false: under identity base change, canonical identifications
and integer coefficients in degree zero, identity and negation transports send
the unit to opposite elements. Negation commutes with all scalars, so adding
scalar compatibility would not repair the claim. The new proof transports the
same `e` through the cartesian natural isomorphism to construct `e'`.

Both rejected nodes depended on their parent, creating proof cycles. None of the
new nodes depends on `lem-pc-open-free-ext-transport`, either as a statement or
proof dependency; the parent now depends on the strictly smaller data,
restriction calculus, and bijectivity nodes.

The earlier docstrings copied the entire parent argument although their
statements lacked some of its conclusions. The new docstrings describe their
actual statements, with full proof plans and edge cases. Stacks Tags 00A7 and
01AK were checked and do state the relevant open-extension adjunction and
exactness. Tags 03DI and 03DJ state the localized-site versions, and 04J0 states
the ringed-site localization square. The generic Ext argument uses derived
functoriality, not a cohomology-to-Ext comparison.

Read `dag/units/sk-thm-picard-rr.json`; its `realized.statement` and sole
`realized.steps` entry are empty. No unit statement, unit route, or unit record
was changed. New blueprint provenance follows the parent's recorded ancestor
`lem-pc-cohomology-mayer-vietoris-ext-presentation` and includes the parent in
`via`. Blueprint searches for open restriction Ext, extension by zero, and
derived functors found no imported blueprint statement duplicating these
Zariski restriction specializations or the generic Ext-square calculation.

The library-plus-sandbox DAG audit encountered an existing cycle through
`lem-weil-pbc-sheaf-algebraic-structures-objects`. The delivery does not edit
those nodes. The baseline-only cycle is
`lem-weil-pbc-sheaf-algebraic-structures-objects` ->
`lem-weil-pbc-sheaf-algebraic-structures-ring-component` ->
`lem-weil-pbc-sheaf-algebraic-structures-objects`. A separate combined-graph reach
check confirms that none of the four new nodes can reach itself, and none of the
replacement parent dependencies can reach the parent. No new cycle is introduced.

Edge cases checked mathematically: empty opens, top opens, zero coefficients,
identity base change, and sign changes of the free-object identification. The
bijection statement tolerates arbitrary object isomorphisms because each change
only composes a restriction bijection with an isomorphism; compatibility requires
the specifically coherent `e'`, as used in the item. No flatness, finiteness,
nonemptiness, or quasi-coherence condition was introduced.

Searches were run through msearch in all three required kinds for every new
node; exact queries and results are logged in searches.jsonl. LeanSearch returned
HTTP Internal Server Error and is recorded as unavailable, not as no match.
The source generic Ext adjunction was read, as were Mathlib's Ext mapping and
composition APIs and the source derived natural-isomorphism/composition APIs.
The two old extension-by-zero statements alone do not expose the represented
free-sheaf identifications and cartesian coefficient coherence required by the
item; those unresolved geometric steps are isolated in degree-zero data and
restriction bijectivity rather than assumed for arbitrary transports.

## New nodes

`lem-pc-open-restriction-data`: the degree-zero geometry and coefficient squares
used by the item. Its module also defines the actual pullback inclusion by
`Limits.pullback.lift`, so no arbitrary existence witness is chosen.

`lem-pc-open-restriction-ext-bijective`: the exact open-extension Ext adjunction
specialized to the two explicit restriction maps. Its statement is insensitive
to changes of source and coefficient isomorphisms; it makes no compatibility
claim for those changes.

`lem-pc-ext-exact-functor-square`: the generic derived naturality lemma for four
exact functors and a natural isomorphism of their composites. It is a separate
proof task from the geometric data and bijectivity.

`lem-pc-ext-restriction-map-calculus`: the actual restriction homomorphism and
its two formal naturality calculations. Its three declarations are implemented;
only the generic functor-square lemma is used as an admitted dependency. The
node's main declaration is `Ext.restrictAddHom_square`; the other declarations
are recorded in its `lean.declarations` list. No additional hole is added here.

There are no change-record paths, since existing interfaces did not change.

## Second reading by U1

1. **Unchanged interfaces: PASS.** Compared every delivered module with the
repository. Only `MayerVietorisOpenExtTransport` exists on the baseline; its diff
adds one plain proof-only import and replaces the proof body. Its signature,
including all let-bound coefficients, scalar representations, both equivalences,
and all three compatibility equations, is byte-for-byte unchanged. The other
four modules are new. The parent JSON changes only `proof`, `proof_deps`, and
`proof_origin`. No target, existing definition, public import, or visibility was
changed, and no change record is needed.

2. **Lean proof and constructions: PASS with the three reported admissions.**
Compiled all five files through `lcompile.py --all` in import order: no errors or
warnings. Scanned the delivered sources: exactly the three named `:= by sorry`
theorems reported above, no forbidden declarations or attributes, and no
admission inside a definition. Read `restrictAddHom`, the pullback-lift definition
of `openBaseChangeInclusion`, and the full bodies of both calculus lemmas and
the parent. In particular, the last parent equation uses injectivity of q' and
the square lemma with the same e, d, c and d' as the first two equations; e' is
constructed from c and e. The transports are inverses of specific bijections.
The existential geometric data are eliminated within a proof of a proposition;
no definition extracts an arbitrary witness from the admitted existence theorem.
The scratch axiom probe compiled and checked all eight delivered public
declarations. `openBaseChangeInclusion`, `restrictAddHom`, and
`restrictAddHom_comp` use only `propext`, `Classical.choice`, and `Quot.sound`.
The other five additionally use `sorryAx`, exactly as expected from the three
reported holes. No other axiom appears.

3. **Split statements: PASS as a decomposition.** Read each of the three new
admitted signatures, its full proof docstring, and its node. `openRestrictionData`
asserts only object/functor identifications and degree-zero scalar/unit squares.
The coefficient-unit square follows from composition of pullback adjunctions;
the open immersion is what makes forgetting module pullback an abelian-sheaf
restriction isomorphism. `openRestrictionExt_bijective` asserts bijectivity of
the explicitly defined maps for arbitrary object identifications: exact
extension by zero, its restriction adjunction and the represented-open identity
give the canonical bijection, and changing identifications composes it with
isomorphisms. It does not claim coherence for arbitrary independent transports.
`mapExactFunctor_square` is purely categorical naturality of the termwise
isomorphism after localization, including its shift comparison, and has neither
geometry nor bijectivity assumptions. Each is strictly a part of the parent
argument, not a renamed parent statement. Checked degree zero, empty and top
opens, zero coefficients, identity base change, and changing e or e' by a sign.
Arbitrary signs preserve bijectivity; the parent square uses coherent e'.
Read Stacks Tags 00A7, 01AK, 03DI, 03DJ, 04J0 and 01F7 directly and the existing
free-sheaf construction. New independent LeanFinder searches used the phrases
“naturally isomorphic exact functors”, “represented by an open”, and “forget
module pullback”; also searched `lean/Sheaf`, `lean/WeilConjectures`, Mathlib Ext
Map/SmallShiftedHom, and the upstream exact-functor comparison APIs. The closest
results are `Ext.mapExactFunctor_hom`, `Scheme.Modules.restrictFunctorIsoPullback`,
and the derived natural-isomorphism/composition comparisons, not the three
complete statements. Closing the generic square requires additional comparison
calculations, rather than a direct existing theorem application. The other two
remain geometric proof tasks. The delivery closes one hole and adds three;
net -2 before the pinned closure ledger, a decomposition rather than a full
axiom-free proof.

4. **Route and pruning: PASS.** The argument restricts Ext first, then inverts
those maps and proves the compatibility equations by injectivity. The generic
calculus has a genuine proof from Mathlib associativity and functoriality,
using the isolated generic square only where required. Every added import is
used: Ext.Map in the generic signatures and construction, the square module
only in the calculus proof, Data and RestrictionMap in the bijectivity signature,
and Bijective only in the parent proof. The original FreeComplex public import
is needed for `openFreeSheaf` in the parent signature. All four old direct
proof dependencies are now explicitly accounted for in “No longer needed”; no
library module is claimed pruned. Read `dag/units/sk-thm-picard-rr.json`: its
realized statement is empty and its sole realized step is empty. The delivery
changes neither that record nor the unit's route.

5. **DAG agreement: PASS.** Read all five node records. The parent steps match
the Lean obtain/construction/injectivity argument and cite exactly the three
new direct proof dependencies. The calculus node records its construction,
postcomposition lemma and square lemma; its only admitted dependency is the
generic functor square. The two geometric nodes retain the extension-by-zero,
free-sheaf and pullback constructions in their proof plans. Each new node has
source, step uses and their proof-dependency union, proof origin, three search
records (the unavailable LeanSearch service is explicitly recorded), creation
and blueprint provenance, chapter/unit, and Lean attachment. The new nodes do
not depend on the parent. Corrected the four new nodes' `lean.statement` fields
to the literal multiline signatures in their Lean files.

Second-reading changes: no Lean proof or statement needed repair. Completed the
old-dependency accounting in the report, made the four new signature records
verbatim, and added this independent review and the current axiom probe.
