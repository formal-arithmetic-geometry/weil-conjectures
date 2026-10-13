## What changed

Proved `AlgebraicGeometry.internalHom_overEquiv` with its signature unchanged.
Private helpers construct the comparison by restricting local linear maps along
`Over.post U.overEquivalence.inverse`. Component linearity, restriction compatibility,
and naturality in both module arguments are proved directly. Mathlib's equivalence
of functor categories supplies the inverse underlying additive natural transformation.
Linearity of that inverse is checked after transporting each object through the slice
equivalence; naturality and the semilinearity of the module restriction maps complete
that calculation. Pointwise bijectivity gives module isomorphisms, which assemble into
an isomorphism of module presheaves and lift to sheaves through `fullyFaithfulForget`.
No imports, statements, or definitions visible to other modules changed. The second
reader updated the existing node’s proof steps and proof origin to describe the
implemented argument; its proof dependencies are unchanged.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.internalHom_overEquiv`
(node `lem-sc-internal-hom-over-equiv`). All three private helpers are fully proved.
No holes remain and no holes were added. This is a proof, not a decomposition.

## No longer needed

None. Both existing public imports are required by the statement. The original
proof dependency `def-pur-sheaf-hom` remains necessary, and no planned module is bypassed.
The unit `sk-thm-picard-duality` has no realized statement or step on this node;
its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No error in the existing statement or plan. The detailed inverse construction uses
Mathlib's fully faithful whiskering along an equivalence rather than manually defining
its inverse components. The empty open and zero modules require no exceptions:
all arguments are categorical and use no nonemptiness or nonzero hypothesis.
Searches: LeanFinder returned generic site adjunctions and condensed-module internal Hom,
Loogle found `Over.post` and its equivalence instance, and source grep found no existing
internal-Hom comparison for `overEquiv`. LeanSearch was unavailable (Internal Server Error).
An exploratory objectwise-isomorphism split was discarded before delivery: arbitrary
objectwise comparisons are not necessarily natural. The delivered proof uses the fixed
explicit transport map throughout.

## Second reading by E2

1. Interface: compared the complete module against the repository with `diff` and
   checked the existing theorem signature byte for byte with a direct assertion.
   Verdict: unchanged signature, visibility, docstring, universe and public imports;
   only private proof helpers and the proof body were added. No change record is needed.
2. Proof: independently compiled the delivered module with `lcompile.py`, without
   errors or warnings. Scanned the entire delivered Lean source for sorry and forbidden
   declarations: none. A scratch copy checks `#print axioms` for the comparison map,
   both bijectivity helpers and the public theorem: each uses only `propext`,
   `Classical.choice` and `Quot.sound`, with no `sorryAx`. Verdict: fully proved.
   The comparison is explicitly
   constructed; the inverse comes from fully faithful whiskering and is uniquely
   determined, with no choice from an unproved mere-existence statement.
3. Split statements: none. Read the private helpers in full: injectivity uses faithful
   whiskering, and surjectivity transports linearity along an object-preimage
   isomorphism, using semilinearity of both module restriction maps. Empty opens,
   zero source and zero target require no extra assumptions. No holes are added.
4. Route and pruning: checked the internal-Hom source, the upstream restriction
   isomorphism, the definition of `overEquiv`, and searched with the alternative
   terms `homObj.*equivalence`, `homObj.*whisker`, and `internalHom.*overEquiv`.
   No shorter existing comparison was found. The upstream `overHomObjIso` concerns
   restriction to a slice, not passage from the slice to an open subscheme.
   Both public imports are used in the public signature. The sole old proof dependency
   `def-pur-sheaf-hom` remains used. No node or module can be pruned from this proof.
   Checked `dag/units/sk-thm-picard-duality.json`: this node realizes no unit statement
   or proof step, and no unit route is bypassed.
5. DAG: checked the existing node’s statement, Lean record and dependency definition
   against the proof. Updated its proof steps to record faithful/full whiskering,
   transport of scalar compatibility, pointwise bijectivity, and definitional
   naturality, and set its proof origin to E2. Its statement, Lean signature and
   proof dependencies remain unchanged. No new nodes are needed.

Changes by the second reader: the existing DAG node’s proof description and origin,
and this review report. No Lean change was necessary. Closed one original hole,
`AlgebraicGeometry.internalHom_overEquiv`; added zero holes and split off zero statements.
