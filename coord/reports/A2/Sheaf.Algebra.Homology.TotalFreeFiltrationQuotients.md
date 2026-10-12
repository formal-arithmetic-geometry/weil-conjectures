## What changed

The original signature of `CochainComplex.TotalFreeFiltration.quotients` is unchanged.
Its complete Lean proof now reduces the two conclusions to three independently stated
steps of the original argument, in three new modules. Retractions use only degreewise
splittings. Each cokernel theorem treats one fixed stage and one supplied endpoint basis,
with explicit resulting degrees `degree i - j`. The proof chooses endpoint bases at
`j = n / 2`, distinguishes the two remainders modulo two, proves the corresponding
stage equality by `omega`, and supplies the required basis and cokernel isomorphism.
All four delivered modules compile together using `lcompile.py --all`.
The original node's proof and dependencies now describe this reduction.

## Proved and sorry left

Closed the hole in `CochainComplex.TotalFreeFiltration.quotients` (node
`lem-pc-derived-total-filtration-quotients`) by a decomposition, not a complete
sorry-free proof of the mathematical result. One original hole is closed and three
holes are added; the net hole count is therefore -2.

The delivery leaves exactly these named holes:

- `CochainComplex.TotalFreeFiltration.step_retraction`, node
  `lem-pc-derived-total-filtration-step-retraction`, in
  `Sheaf.Algebra.Homology.TotalFreeFiltrationStepRetraction`.
- `CochainComplex.TotalFreeFiltration.cokernel_even`, node
  `lem-pc-derived-total-filtration-cokernel-even`, in
  `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelEven`.
- `CochainComplex.TotalFreeFiltration.cokernel_odd`, node
  `lem-pc-derived-total-filtration-cokernel-odd`, in
  `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelOdd`.

Each is a strict part of the original proof, with a complete construction argument
in its docstring and DAG node. None simply restates the original conjunction.
No definition, existing signature, or visibility changed.

## No longer needed

None: the filtration-term module remains necessary for the statements and definitions.
The new statements avoid requiring freeness or short exactness for retractions, and
avoid degreewise splittings and other endpoint decompositions for individual cokernels.
The old direct proof dependency `lem-pc-derived-total-filtration-stable` is
replaced by the three new proof dependencies, but remains used transitively
and by the unchanged public import. No existing dependency module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG had no separately stated declarations for its projection/retraction and
cokernel-identification steps. The existing stable-terms module defines the filtration
but does not prove these steps. The new nodes expose precisely these missing pieces.
LeanFinder found alternating constant complex and total inclusion results, Loogle
found single-degree functor and evaluation lemmas, and grep found no total-cokernel
result; none gave the needed explicit filtration quotient identifications.
The unit record has no realized nodes here, so this decomposition preserves the unit route.

Edge cases were checked in the mathematical statements: at j=0 the preceding sum is
empty; at n=0 the map out of the zero submodule has the zero retraction. An empty
endpoint basis gives a zero quotient. The zero ring gives zero modules. Arbitrary
integer endpoint degrees are shifted by -j, without a boundedness restriction.

## New nodes

`lem-pc-derived-total-filtration-step-retraction` isolates degreewise column
projection and the supplied splitting retraction. It does not assume endpoint
freeness or short exactness.

`lem-pc-derived-total-filtration-cokernel-even` identifies the cokernel at stage
2j with the shifted first endpoint basis. It has no assumption about other bases.

`lem-pc-derived-total-filtration-cokernel-odd` identifies the cokernel at stage
2j+1 with the shifted third endpoint basis. It has no assumption about other bases.

Each new theorem has its own module and node. There are no change records or forced
adaptations, since all existing interfaces remain identical.

## Second reading by A2

1. Compared all four modules with the repository. Only `quotients` existed there;
   its signature, variables, visibility, public import, and docstring are unchanged.
   Removed an extra space before `:=` so the signature is byte-for-byte identical.
   The other three modules are new theorem-only modules. No definition changed,
   no change record or forced adaptation is needed, and no target statement changed.
2. Compiled all four modules in import order with `lcompile.py --all`: no errors
   or warnings. A scratch copy with `#print axioms` for all four declarations
   reported exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The three reported named theorems are the only remaining holes. There are no
   forbidden declarations, attributes, or holes in definitions. The total-stage
   construction uses the upstream stability theorem only for its proof field;
   this delivery introduces no choice of data from an unproved existence theorem.
3. Read each new theorem, its complete docstring argument, and its matching node.
   Each is a strict part of the original argument, not a renamed restatement.
   Checked the zero stage, empty previous-column sum, zero or empty endpoints,
   and negative endpoint degrees. The odd retraction on the new full column is
   the splitting retraction followed by the first arrow, transported through e;
   on the old lower image it is identity by `Splitting.f_r`. The cokernel maps
   commute with differentials because horizontal terms land in earlier columns
   (or the zero positive column at j=0), and endpoint vertical differentials vanish.
   Compared the argument with [Stacks Tag 09KP](https://stacks.math.columbia.edu/tag/09KP).
   Independent searches used column projections/direct-sum components and splitting
   retractions, rather than only the original quotient query. LeanFinder found
   `DirectSum.component.lof_self` and `DirectSum.toModule_lof`; Loogle found
   `CategoryTheory.ShortComplex.Splitting.f_r`; grep found the splitting helpers
   and total-complex inclusions. These support individual constructions but do not
   identify the concrete `term` submodules or their complex cokernels. Repository
   searches found no duplicate; the first-quadrant spectral-sequence result and
   cellular-filtration consumer do not supply these statements. Closing any of the
   three holes still requires the explicit column/submodule identifications.
4. Read the proof top down: retractions use only splitting; quotient bases are
   selected at n/2, and the two parity cases use the corresponding endpoint with
   degree d-j. All three proof imports are used and private to the proof. The
   public term import is required by the signature. The old stable-term dependency
   remains necessary transitively, so no module is pruned. Checked the unit's
   `realized` record: its statement and step lists are empty here; the decomposition
   changes none of its route or data. This is one closed hole and three added holes,
   a decomposition with net -2, not a sorry-free mathematical proof.
5. Checked node proof steps, dependency unions, sources, creation records,
   blueprint provenance, chapter/unit, searches, and verbatim new Lean signatures.
   Existing-node changes are confined to the permitted proof fields. All agree
   with the Lean reduction and the three remaining named holes.

Second-reading changes: restored exact signature whitespace, corrected a duplicated
word in the odd node's proof-origin note, clarified the retained old dependency,
and added the independent checks and search evidence above. No proof argument,
statement, definition, or import needed repair.
