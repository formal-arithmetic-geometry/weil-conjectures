## What changed

Preserved the signature and existing docstrings of
`AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_inverse_homotopies_spread`.
Its proof now spreads the two endomorphism homotopies successively, restricts the
first to the common affine neighbourhood, and explicitly conjugates the restricted
inverse through natural comparisons to obtain the required direct restriction.
The only new import in the assigned module is the proof-only import of
`Sheaf.AlgebraicGeometry.PerfectOpenStalkHomotopySpread`.

Added four modules, each with one public statement and its DAG node:
`PerfectOpenStalkReverseComponentsLift`, `PerfectOpenStalkRetractMapEquality`,
`PerfectOpenStalkChainMapEquality`, and `PerfectOpenStalkHomotopySpread`.
The chain-map equality theorem is proved by induction over the finite support
interval from single-term equality, with zero-source arguments outside the interval.
The single-homotopy theorem is proved by lifting components, comparing the stalks
of null-homotopic maps, shrinking equality, and using `Homotopy.equivSubZero`.
All comparison helpers are private and completely proved; no data definition
chooses an arbitrary witness from an unproved existence theorem.

All five files compile locally within the 60-second per-file limit.
Named sheaf-level comparison isomorphisms avoid expensive definitional comparisons
of nested complex restrictions. Local heartbeat options have explanatory comments.
No existing definition, statement, public import, or other group's module changed.

## Proved and sorry left

Closed the assigned module's one hole:
`AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_inverse_homotopies_spread`.
There are no sorries left in that module.

Also proved the new declarations
`AlgebraicGeometry.Scheme.exists_perfect_open_stalk_chain_map_eq`
(node `lem-sc-perfect-open-stalk-chain-map-equality`) and
`AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_homotopy_spread`
(node `lem-sc-perfect-open-stalk-homotopy-spread`).

Exactly two new holes remain, each the complete proof of a named public theorem:

- `AlgebraicGeometry.Scheme.exists_perfect_open_stalk_reverse_components_lift`
  in `PerfectOpenStalkReverseComponentsLift`, node
  `lem-sc-perfect-open-stalk-reverse-components-lift`: only reverse components
  and their stalk comparison; no differential or homotopy equations.
- `AlgebraicGeometry.Scheme.exists_open_stalk_retract_map_eq`
  in `PerfectOpenStalkRetractMapEquality`, node
  `lem-sc-perfect-open-stalk-retract-map-equality`: equality of endomorphisms of
  one finite retract sheaf; no complex, boundedness or homotopy.

This is a decomposition: one original hole closed, two strictly lower holes added,
not a complete axiom-free proof of the geometric spreading argument. The original
statement is not restated as a new holed theorem. The combining proofs include
finite-support induction, null-homotopy identities, subtraction, further restriction,
and natural-isomorphism conjugation.

## No longer needed

No original imports removed and no original dependency branch pruned. The old
internal-Hom finite-presentation dependency remains below the component-lifting
and finite-retract equality nodes. The existing finite-free stalk homotopy modules
were inspected but are not imported: their complexes are finite free on the scheme,
with a different support interface, and their stalk operation is pullback to
`Spec` of the stalk, whereas this item uses finite retracts on slice sites and
`openModuleStalkFunctor`. They were not dependencies of this item to begin with.
No quasi-isomorphism detection, stalk chain-map lifting, or alternate perfect
locus theorem is used in the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or unit route was changed. The unit
`sk-prop-av-cube` has no realized entries that this reduction bypasses.
The original internal-Hom theorem does not itself provide the open-site
finite-retract component lifting and equality interfaces. These were isolated
explicitly rather than assumed to follow by a single application.

Checked Stacks Tags 09RE, 0BC7 (2), and 01CP on their official pages because the
referenced local Stacks source files are absent on this machine. The finite
calculation and finite-type germ injectivity supply the two remaining steps.
LeanFinder, Loogle, Mathlib grep, and library searches found no exact replacement;
LeanSearch returned Internal Server Error, recorded as unavailable.
Blueprint searches for homotopy and finite calculation found no duplicate of
these open-site finite-retract interfaces. The nearest ancestor recorded in the
parent node remains `thm-sc-theorem-of-cube`.

Edge cases checked: empty support intervals (the finite-degree induction is empty
and all sources vanish), zero ranks, negative support degrees, and identity
restrictions. No intersection of affine opens is assumed affine: an affine
subneighbourhood is chosen only after the shrinking argument. No Noetherian
hypothesis, quasi-isomorphism hypothesis, or nonzero-rank condition is introduced.
Finite projective retracts remain essential for uniform finite-component descent;
the statements do not assert this for arbitrary infinitely generated sheaves.

## New nodes

`lem-sc-perfect-open-stalk-reverse-components-lift` records lifting the finitely
many reverse-degree components and their natural stalk comparison without equations.
Its module contains the first remaining hole.

`lem-sc-perfect-open-stalk-retract-map-equality` records the finite matrix zero-germ
argument for a single sheaf retract, without any complex. Its module contains
the second remaining hole.

`lem-sc-perfect-open-stalk-chain-map-equality` is proved from the single-term
statement by finite-neighbourhood intersection and support bounds. Its interface
keeps the two restrictions explicit, avoiding costly elaboration of their equality.

`lem-sc-perfect-open-stalk-homotopy-spread` is proved from reverse-component
lifting and chain-map equality via Mathlib's null-homotopy API. It is applied twice
in the assigned theorem. All new nodes keep the parent's chapter and unit, and
the parent's proof and proof dependencies now follow the actual Lean argument.
No change records are necessary because every existing signature and visibility
is preserved and all added imports in existing modules are proof-only.


## Second reading by M4

1. Interface: PASS. Compared the delivered existing module with the repository
   using diff and checked the complete existing theorem signature byte for byte,
   including its hypotheses, let-bound restriction, and both conclusions. Only
   private proved helpers, proof-local options, a proof-only import and the proof
   body are added. No existing definitions or public imports change; there are no
   forced adaptations or change records. Restored the original single space before
   the theorem's proof delimiter.

2. Proof: PASS as a decomposition. Compiled all five modules in import order with
   lcompile.py: 2.6, 4.8, 15.7, 17.4 and 18.7 seconds respectively, with no errors
   or warnings. A scratch module importing all five printed the axioms of all five
   public theorems: each uses only propext, Classical.choice, Quot.sound and
   sorryAx. Static inspection found precisely the two reported named theorem
   holes, no forbidden declarations and no holes in definitions. The private
   homotopy and restriction-isomorphism constructions are explicit; obtaining
   witnesses inside existential theorem proofs does not define arbitrary public
   data from an unproved existence theorem. The delivery tool also checks the
   axioms of private declarations. The scratch module was removed before delivery.

3. Split statements: PASS. Read both full signatures, both docstring proofs and
   their nodes against [Stacks Tag 01CP](https://stacks.math.columbia.edu/tag/01CP),
   [Tag 09RE](https://stacks.math.columbia.edu/tag/09RE) and
   [Tag 0BC7](https://stacks.math.columbia.edu/tag/0BC7). Finite-free sandwich maps
   reduce lifting and equality to finitely many scalar germs; the open-site
   equivalence and stalk-ring isomorphisms provide the natural comparison.
   Checked zero retracts, empty support intervals, negative degrees, identity
   restrictions and arbitrary non-Noetherian rings. Component lifting requires
   no differential equations; retract equality has no complex or homotopy.
   Both are strictly smaller than inverse-homotopy spreading, and both are used.
   Independent LeanFinder search for vanishing of a finite locally free sheaf
   morphism near a zero germ, Loogle search for germ equality, Mathlib grep for
   finite/free stalk APIs, and library searches found scalar germ APIs but no
   direct theorem with these interfaces. In particular InternalHomGermZeroFiniteType
   still has a hole and requires an additional finite-type/internal-Hom interface;
   FiniteFreeStalkMapEquality uses pullback to Spec of the stalk and finite free
   sources, rather than this module's openModuleStalkFunctor and finite retracts.
   Neither hole can be closed by a short application of an existing declaration.

4. Route and pruning: PASS. Read the argument top down: spread the two homotopies
   in succession, restrict the first, and conjugate the inverse via natural
   restriction comparisons. Read the single-homotopy subtraction/null-homotopy
   reduction and the finite-support equality induction. The proof uses Mathlib's
   existing homotopy API rather than creating another homotopy-equation hole.
   Imports are confined to the signature modules and the actual proof APIs;
   every proof-only dependency has a plain import. No original branch is pruned:
   def-pc-perfect-complex and def-sc-open-module-stalk-functor are used throughout,
   and lem-weil-pbc-stalk-internal-hom-finite-presentation remains in the two lower
   nodes' proof plans. Thus every old proof dependency remains reachable in the
   new DAG. The unit sk-prop-av-cube has empty realized statement/step entries;
   its record and route are unchanged. One old hole closes and two new holes are
   added: net minus one hole, explicitly a decomposition, not a complete proof.

5. Nodes: PASS. Checked all five Lean statements against their lean.statement
   records using the project's declaration parser, and checked that proof_deps
   equals the union of proof-step uses. The parent node follows the successive
   spreading and conjugation argument; the new proved nodes follow the finite-set
   induction and null-homotopy reduction. Every new node has its source, searches,
   creation record, blueprint ancestry, chapter, unit and Lean record. The parent's
   unrelated fields are unchanged. No signature or definition change is concealed
   in the metadata.

Second-reading changes: restored exact existing-signature whitespace and added
this independent review with source checks, fresh searches, compilation timings,
axiom results and explicit dependency/net-hole accounting. No mathematical proof
repair was needed; the two documented geometric holes remain open.
