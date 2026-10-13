## What changed

Replaced the sorry in `AlgebraicGeometry.principalOpenCech_subset_coordinates`
without changing its statement or public imports. The proof constructs `b_n` by
composing the forgotten `τ_n` with the isomorphism of an explicit insertion map.
Function extensionality and the assumed differential equation prove the chain
relation; cancellation of `τ_n.hom` with `τ_n.inv` proves the augmentation relation
from the singleton insertion formula.

Added `PrincipalOpenCechSubsetInsertion`: increasing enumeration, the basic-open
product formula, the equality of tuple intersections with the corresponding
preimages, explicit additive section transport, individual coordinate insertion
through `Pi.single`, `extendXIso.inv`, and `ιTotal`, and their finite sum. All its
proofs and data are complete. In particular the comparison map is constructed,
not selected from an unproved existence statement. The inverse in
`PrincipalOpenCechSubsetInsertionBijective` uses only bijectivity of that fixed map,
which uniquely determines the inverse.

Added three proof-only imports for bijectivity, the differential formula, and the
augmentation formula. All five modules compiled together with lcompile.py, with
no errors or warnings. The new statements were checked mathematically for r=0,
r=1, zero coefficients, repeated indices with equal opens, empty intersections,
and unbounded coefficient complexes. No finite support in coefficient degree is
assumed: finiteness is solely in the nonzero Čech columns.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.principalOpenCech_subset_coordinates`
(node `lem-sc-principal-open-cech-subset-coordinates`). This is a decomposition,
not a sorry-free proof: one upper hole is closed and three lower holes are added.

The three remaining holes, each in its own new module, are:

- `AlgebraicGeometry.principalSubsetInsertion_bijective`, node
  `lem-sc-principal-open-cech-subset-insertion-bijective`.
- `AlgebraicGeometry.principalSubsetInsertion_differential`, node
  `lem-sc-principal-open-cech-subset-insertion-differential`.
- `AlgebraicGeometry.principalSubsetInsertion_augmentation`, node
  `lem-sc-principal-open-cech-subset-insertion-augmentation`.

Each asserts a distinct property of the fixed explicit insertion. None has a
comparison complex T, an isomorphism τ, or an assumed differential of T. The
original theorem combines these properties by actual Lean proof. The construction
module contains no sorry. No other existing module was adapted.

## No longer needed

No imports or existing dependency modules are pruned. The original section
transport and alternating-total dependencies remain necessary both for the
unchanged signature and for the explicit construction. The existing node's direct
proof dependencies are replaced by the three property nodes; those still reach
the original construction dependencies. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous missing-object failure has cleared: both original dependencies now
compile from the published build. The earlier sandbox contained only the original
sorry and a blocker report.

The parent proof plan provides no existing declaration for its finite regrouping,
differential-coordinate check, or singleton comparison. These are the three
smaller statements now exposed. An arbitrary chain isomorphism cannot be assumed
to preserve augmentation; the new augmentation statement is therefore about the
fixed explicit insertion, not an arbitrary isomorphism.

The cited Stacks TeX file is not present in this checkout. The source was read
online at https://stacks.math.columbia.edu/tag/08C1 and
https://stacks.math.columbia.edu/tag/01FM, together with the actual definitions in
`AlternatingCechTotalComplex.lean` and Mathlib's restriction equivalence.
LeanSearch returned an Internal Server Error; actual LeanFinder, Loogle, and grep
searches are recorded in searches.jsonl. No unavailable search is counted as a
negative mathematical result.

## New nodes

`def-sc-principal-open-cech-subset-insertion` records the explicit increasing-tuple
insertion construction and its proved open and section identifications.

`lem-sc-principal-open-cech-subset-insertion-bijective` records the finite
product-to-total bijectivity argument, independent of differentials and augmentation.

`lem-sc-principal-open-cech-subset-insertion-differential` records the signed face
and coefficient differential calculation on the explicit finite-sum insertion.

`lem-sc-principal-open-cech-subset-insertion-augmentation` records the degree-zero
singleton restriction calculation on that same explicit insertion.

No change record is needed: all existing signatures, definitions, and visibility
are unchanged. The three new theorem docstrings give their sources and complete
proofs in words. The parent node now records the Lean combination argument.

## Second reading by V3

1. **Unchanged interface: PASS.** Compared the delivered coordinate module with
   the repository using diff. The entire existing theorem signature is byte for
   byte identical, including all degree transports and the augmentation conclusion.
   Only its proof and three plain proof imports changed. No existing definition,
   public import, visibility, or other module changed; no change record is required.
2. **Proof and data: PASS.** Independently compiled all five modules in import
   order through lcompile.py, with no errors or warnings. The sole three sorries
   are exactly the named bijectivity, differential, and augmentation theorems listed
   above; the explicit construction contains no sorry. Checked every declaration
   for prohibited constructs. The insertion is the finite sum of constructed maps,
   and AddEquiv.ofBijective chooses only the uniquely determined inverse of that
   fixed map. Checked the axioms of all delivered declarations using a scratch
   #print axioms probe; only the permitted standard axioms and sorryAx occur.
3. **Split statements: PASS as decomposition.** Read each full statement and its
   natural-language proof against the actual increasing-tuple differential,
   extension-by-zero, totalization, restriction equivalence, and augmentation.
   Bijectivity concerns only the fixed graded map; the differential and singleton
   formula are separate properties, with no T, tau, or existential comparison.
   They are strictly parts of the original argument, rather than a restatement.
   Tested r=0 (empty product and zero total), r=1 (one transported coefficient
   complex and no horizontal term), and a two-element subset (horizontal signs
   + then -, vertical sign -). Repeated opens retain independent indices; zero
   modules and empty intersections cause no exception. Each diagonal has only
   r possibly nonzero columns, even for unbounded J. All three holes have source,
   complete proof docstrings, and matching nodes. Independently searched with
   LeanFinder for finite ordered enumerations and finite-column total products,
   Loogle for orderEmbOfFin, and grep for total differential/inclusion identities;
   also searched both Lean library roots and the upstream checkout. Results supply
   primitives, not these fixed-map properties. PrincipalCechTotalRegroup_comm is
   about a different subset bicomplex and requires column comparison isomorphisms
   and their horizontal compatibility, which are not available here. None of the
   remaining three holes can be closed in a few minutes using the declarations
   found. Search outputs are recorded by msearch.py.
4. **Route and pruning: PASS.** The upper proof constructs b from tau and the
   explicit insertion isomorphism, proves the chain equation by the coordinate
   differential, and cancels tau before applying the augmentation identity.
   All three new imports are proof-only and used. The two original dependency
   modules remain needed for the original signature and the new construction;
   neither is pruned. The old direct proof_deps are now reached transitively,
   as explained under No longer needed. Inspected sk-thm-picard-duality.json:
   this item realizes no unit statement or step, and the unit route is unchanged.
5. **Nodes: PASS.** The existing node differs only in proof, proof_deps, and
   proof_origin. Its steps match the actual Lean combination. Each new node has
   source, proof steps, matching dependency union, proof_origin, recorded searches,
   status split, created.item/group/date, blueprint origin, chapter/unit, and Lean
   attachment. The new property statements agree with their Lean signatures.

**Second-reader changes.** Corrected the last sentences of the differential
property's proof docstring and the matching DAG proof step. Comparing maps into a
coproduct is not justified merely by its universal property: the corrected argument
checks each single-coordinate source, reassembles its target summands, then uses
finite-sum additivity for arbitrary inputs. No Lean statement, construction, proof
term, import, or hole count changed. One original hole is closed and three lower
holes are added: net -2, a decomposition rather than a sorry-free proof.
Sources independently checked online: [Stacks 08C1](https://stacks.math.columbia.edu/tag/08C1)
and [Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM).
