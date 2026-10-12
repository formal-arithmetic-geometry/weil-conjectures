## What changed

Replaced the original hole in `AlgebraicGeometry.Etale.derivedGlobalGerm_exchange`
with a real right-derived extensionality reduction. The source and target natural
transformations are compared after precomposition with the global-sections unit.
The underived equality rewrites the common localized composite, and the two
factorization statements identify the derived sides with that composite.

Added three modules, each containing one strictly smaller compatibility theorem:
`UnderivedGlobalGermExchange`, `DerivedPulledGlobalGermFac`, and
`DerivedGlobalGermUnitFac`. Their statements have full proofs in words and DAG nodes.
Existing definitions and declaration signatures are unchanged. Proof-only imports
in the item and the cohomology-pullback import in the target factorization are plain
`import`. Removed unused public imports from the new modules.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Etale.derivedGlobalGerm_exchange` (one of one original
holes). This is a decomposition, not a completed proof: it still depends on three
new holes and therefore on `sorryAx`.

Holes added, all public named theorems with exactly `:= by sorry`:

- `AlgebraicGeometry.Etale.underivedGlobalGerm_exchange`, node
  `lem-weil-pbc-underived-global-germ-exchange`, module
  `Sheaf.AlgebraicGeometry.UnderivedGlobalGermExchange`.
- `AlgebraicGeometry.Etale.derivedPulledGlobalGerm_fac`, node
  `lem-weil-pbc-derived-pulled-global-germ-fac`, module
  `Sheaf.AlgebraicGeometry.DerivedPulledGlobalGermFac`.
- `AlgebraicGeometry.Etale.derivedGlobalGerm_unit_fac`, node
  `lem-weil-pbc-derived-global-germ-unit-fac`, module
  `Sheaf.AlgebraicGeometry.DerivedGlobalGermUnitFac`.

There is no hole inside a definition and no new choice of data. The three remaining
statements separate an underived identity from each independent derived unit
calculation. The report does not count the decomposition as positive net progress:
the submitted local hole count is one closed and three added (net minus two), and
only the maintainer's pinned sorry ledger determines closure and whole-library totals.

## No longer needed

Removed the item's direct import of
`Sheaf.AlgebraicGeometry.DerivedExchangeTermwise` and the proof-dependency node
`lem-weil-pbc-derived-exchange-termwise`. The source-side factorization instead uses
the already proved bounded-below unit formula
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app` of
`WeilConjectures.SixFunctors.BaseChange.Derived` (recorded under
`lemma-weil-pbc-derived-exchange-replacement`). No arbitrary unbounded K-injective
representative is needed in this reduction.

The old dependency `lem-weil-pbc-cohomology-pullback-derived-unit` is retained below
`lem-weil-pbc-derived-global-germ-unit-fac`; its module is imported there for the
proof. Thus the item's former direct import of
`Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit` is replaced by that indirect
proof dependency, not claimed as a pruned closure module.

The false proposed `DerivedGlobalGermExchangeTransport` module was deleted from the
sandbox delivery. The unchanged `DerivedGlobalGerm` sandbox copy was removed from
the delivery. No claim is made that the removed direct dependency is unreachable
from every other target; pruning figures require the pinned ledger.

## Where the brief, the DAG or earlier work was wrong

The first worker's `derivedGlobalGerm_exchange_transport` concluded δ=ε for arbitrary
natural transformations of the appropriate type, with no compatibility hypothesis.
It is false. On the identity square over Spec of a separably closed field, one can
take zero and the canonical derived germ: on the constant integer sheaf in degree
zero the latter sends 1 to its nonzero germ. The lemma would equate those maps.
The original target proof used this false lemma and did not use its three concrete
compatibility imports. The first report also omitted all required new-node records.
Those faults have been repaired, and the false statement is not delivered.

## Second reading by T3

1. Compared the delivered existing module with the read-only repository using `diff`
   and independently compared the exact theorem-signature substrings in Python:
   byte-for-byte equal. The unchanged definition module was excluded. No statement,
   definition, target, or data construction is altered. Verdict: pass.
2. Compiled all four delivered modules through `lcompile.py` in import order, with
   no errors or warnings. Inspected the Lean for forbidden declarations and holes:
   only the three named theorem bodies above remain `sorry`. Explicit scratch
   `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` for the remaining dependencies. Verdict: valid reduction with declared
   open dependencies; no unsupported claim of a completed proof.
3. Read each split statement and its proof in words. Checked zero sheaves and zero
   complexes (both sides vanish), identity squares and identity inverse images
   (the formulas reduce to the canonical units/germs), and arbitrary noninjective
   bounded below representatives (the units are never inverted). None assumes
   invertibility of a global germ, properness, torsion, algebraic closedness, or
   cartesianness for the intermediate commutative-square formulas. The underived
   formula is the mate/terminal-section identity; each derived formula is a single
   unit computation, strictly less than the full target. Repeated semantic,
   type-pattern and text searches with different queries; LeanSearch returned an
   internal server error, recorded honestly. LeanFinder/Loogle supply related
   generic formulas, not these canonical composites. Searched both library roots
   and Mathlib, and inspected the bounded derived exchange unit formula and the
   cohomology-pullback derived-unit proof. Verdict: no duplicate found; three
   genuine smaller gaps, with nodes and complete docstring arguments.
4. The proof now combines the three statements directly using Mathlib's
   `Functor.rightDerived_ext`, evaluates the resulting natural-transformation
   equality at K, and simplifies only associators, unitors, and compositions.
   The source computation uses the upstream bounded-below factorization rather
   than the general K-injective transport. Removed redundant imports in new
   modules and documented both old dependency nodes above. Read
   `dag/units/sk-thm-p1.json`, including `realized`: this node is a subsidiary
   compatibility lemma, not a realized unit statement or step. All realized nodes
   and the chapter/unit route stay in place. Verdict: pass, below-unit reduction.
5. Wrote the three new nodes with their verbatim Lean signatures, sources,
   natural-language proofs, dependency unions, actual search records, creation
   records, blueprint ancestry, chapter and unit. Updated only `proof`,
   `proof_deps`, and `proof_origin` of the existing node to describe the actual
   extensionality reduction. The target factorization retains the old
   cohomology-pullback dependency and the source factorization cites the upstream
   replacement/unit formula. Verdict: node records agree with the submitted Lean.

Changes by the second reader: removed the false unconstrained transport theorem;
wrote the real extensionality reduction; removed the linter suppression and used
`have` for the local proposition instance; pruned unused imports; added all missing
node records; corrected the hole accounting and dependency report. The remaining
factorizations require substantial functorial comparison calculations; none was
claimed closed by a speculative short proof.

## New nodes

`lem-weil-pbc-underived-global-germ-exchange` records the underived mate identity,
with its own module and proof on terminal sections and stalk representatives.

`lem-weil-pbc-derived-pulled-global-germ-fac` records only the source-side unit
factorization, using the existing bounded-below derived base-change formula.

`lem-weil-pbc-derived-global-germ-unit-fac` records only the target-side unit
factorization, using the existing cohomology-pullback derived-unit identification.

No change record is needed: all existing signatures and definitions are unchanged,
and all new imports in the existing module are proof-only.
