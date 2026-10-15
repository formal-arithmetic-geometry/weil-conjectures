## What changed

Proved both original theorems in
`lean/Sheaf/AlgebraicGeometry/TruncationExchangeCouple.lean`.
`exists_triangle` now uses the distinguished triangle of consecutive standard
t-structure truncations. The proved homology-bijection API identifies its third
object with the prescribed layer, with the exact normalization required by the
statement. Transporting that triangle supplies the original projection and
boundary without changing either definition.

The exchange theorem constructs both exact couples from the long exact homology
sequences of the image triangles. Proved private helpers transport short-complex
exactness across the indexing equalities, identify the couple accessors, and
establish the three naturality squares and the page-identification formula.
The connecting-map square is a direct calculation using shift compatibility.

Removed the seven original proof-only imports listed below. The second reading
also removed the initially added, redundant proof-only import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`; its APIs are
already available through the retained imports. Both public imports, all
existing signatures, and all existing definitions are unchanged. Updated only
`proof`, `proof_deps`, and `proof_origin` of
`lem-weil-pbc-truncation-couple-morphism` to describe the implemented route.
No other modules, interfaces, or unit-level steps changed.

## Proved and sorry left

Closed both original holes:

- `CategoryTheory.TruncationExchange.exists_triangle`.
- `AlgebraicGeometry.Etale.truncation_exchange_couple_morphism`.

No sorry remains in the item, and no holes were added or split off. All private
helpers are proved. Separate `#print axioms` checks for both theorems returned
only `propext`, `Classical.choice`, and `Quot.sound`. The delivered module compiles
cleanly through `lcompile.py` (4.3 seconds on the final local compile).

The argument covers every integer truncation index and bidegree, including
negative degrees and zero layers. Outside the layer degree, the isomorphism test
uses vanishing homology on both sides; it adds no nonvanishing, boundedness,
properness, or torsion assumptions. The shifted-couple interface's zero shifts
are handled explicitly by equality transports, rather than assumed to be
definitional equalities.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`.
- `Sheaf.CategoryTheory.TruncationTriangle`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
- `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.Algebra.Homology.ExactCouple.Basic`.

Also removed the redundant new direct import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus` during the second
reading. A scratch compile without this import succeeded (4.5 seconds).

The proof no longer uses the complex-level truncation-triangle node
`lem-weil-pbc-truncation-triangle`, the separate inverse-image exactness node
`prop-weil-pbc-inverse-image-exact`, or the cohomology-ladder node
`lem-weil-pbc-derived-cohomology-ladder`. The canonical standard-t-structure
triangle and direct naturality calculation replace those planned dependencies.

The other old `proof_deps` removed are
`def-weil-pbc-derived-inverse-image`, `def-weil-pbc-triangles-with-shift`, and
`def-weil-pbc-direct-image`. These definitions remain available through the
retained public imports wherever the unchanged statements and definitions need
them; they are not separate steps of the implemented proof. Together with the
three nodes above, this lists every old `proof_deps` entry removed.

The other removed imports duplicate APIs already available through the unchanged
public imports. In particular, `DerivedComparison` is unnecessary: the actual
exchange transformation's shift-compatibility instance is the proved
`Etale.commShift_derivedBaseChangeMapPlus` in `BaseChange.Derived`.
Definitions still needed by the statement remain in its dependency closure.
This report identifies dependencies removed from this item's proof; it makes no
claim that another target cannot still need the same modules or nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature defect was found. The planned descent from
complex-level truncation triangles was unnecessary: the standard t-structure
already gives the required distinguished triangle, and the source library proves
the homology-bijection and isomorphism-detection lemmas needed to normalize it.
This is a shorter route below the unit level; the unit's realized statements and
steps are preserved.

The earlier concern about choosing data from the unproved `exists_triangle`
is resolved by proving that theorem itself. Projection and boundary retain their
original definitions. The layer identification used in the proof is obtained
from a bijection on morphisms, so its prescribed homology map determines it.
No arbitrary object is extracted from an unproved existence assertion.

No new nodes, change records, forced adaptations, or outstanding proof obligations.

## Second reading by F1

1. **Interface: pass.** Compared the complete delivered module against the
   repository version, including all 21 existing declarations. Every existing
   signature and visibility is byte-for-byte unchanged, and every existing
   definition body is unchanged. Only the two original theorem proofs, their
   explanatory docstrings, proof imports, and new private helpers differ. No
   target, adapted module, or change record is part of this delivery.
2. **Proof and axioms: pass.** Independently compiled the delivered module with
   `lcompile.py --all`, with no errors or warnings (4.4 seconds). Compiled a
   scratch copy with `#print axioms` for both original theorems; each lists only
   `propext`, `Classical.choice`, and `Quot.sound` (4.3 seconds). The source has no
   `sorry`, forbidden axiom or implementation override, or hollow definition.
   The projection and boundary now choose from a proved existence theorem; the
   layer identification in that proof is determined by a bijection on morphisms.
3. **Split statements: pass, none.** Neither new holes nor split-off public
   statements were introduced. Read all private helpers: their equalities and
   exactness assertions follow from explicit isomorphism transports, long exact
   homology sequences, and naturality. Checked the degree arithmetic at arbitrary
   integers (including zero and negative indices): alpha preserves total degree,
   f raises it by one, and the shifted-interface zero shifts cancel. For zero
   layers the homology-isomorphism argument still applies; no nonzero-object
   premise is used.
4. **Route and pruning: pass after report correction.** Read the imported APIs,
   searched Mathlib and both library roots, and independently queried LeanFinder
   for the consecutive-truncation triangle with normalized cohomology projection.
   The search found the general t-structure triangle APIs already used, with no
   theorem supplying this normalized triangle and exact-couple conclusion in one
   step. The upstream connecting-map naturality lemma is an alternative to the
   short direct shift calculation, which needs no additional import. Removed the
   redundant new proof-only Plus import after a successful scratch compile
   without it; both public imports are needed by existing
   statements and definitions. Compared `dag/units/sk-thm-properbasechange.json`
   and its realized statement and three steps: this node is below those steps,
   and the construction changes none of them. Completed the list of removed
   proof dependencies above; all seven removed direct imports were already listed.
5. **DAG: pass.** The only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`. Read each proof step against its Lean implementation and
   checked the declaration records of its dependencies. The set of `proof_deps`
   is exactly the union of the steps' `uses`. The node explains the concrete
   `commShift_derivedBaseChangeMapPlus` instance used instead of the older
   `DerivedComparison` API. No new node requires a statement or source review.

Second reading removed one redundant proof-only import and completed this
report with the three omitted removed-node names and this independent review.
No Lean proof repair was necessary.
