## What changed

Completed AlgebraicGeometry.sheafAlgebraHomUnderlying_eq without changing its signature,
visibility, or the data of any definition. Private generic helpers express equality of
ofPresheaf constructions with equal module structures, equality of sheaves from their
presheaves, and equality of functors detected after faithful forgetting. Restriction of
scalars leaves the underlying abelian presheaf functor unchanged. No imports change.

## Proved and sorry left

Closed AlgebraicGeometry.sheafAlgebraHomUnderlying_eq
(blueprint: def-pc-derived-rhom-algebra-module). The sectionwise module equality uses
Module.ext' and the already proved sheafAlgebraHom_underlying_linear. Proof irrelevance
identifies the semilinearity witnesses. Faithfulness then identifies the functor maps.
No holes added; no decomposition.

The only remaining sorry is AlgebraicGeometry.derivedRHomAlgebraModule_underlying
(blueprint: def-pc-derived-rhom-algebra-module), unchanged. Its remaining work includes
making the degree-zero Hom-complex comparison natural and descending through localization.

## No longer needed

None. All original imports are retained; the node already has no proof dependencies.
The objectwise homComplex_single_iso and derivedInternalHom_single_comparison were read
while investigating the remaining derived comparison, but are not imported or used here.
They are not claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. Direct functor extensionality makes Lean repeatedly unfold
large sheaf structures. The private faithful-forgetting lemma keeps the transport argument
generic. The derived comparison remains a genuine obligation; an objectwise isomorphism
alone does not supply naturality.

## Second reading by T3

1. Compared the delivered module with the repository version. Existing declaration signatures and definition data are unchanged; only the proof of `sheafAlgebraHomUnderlying_eq` and private helpers were added.
2. Compiled the module and inspected its remaining hole. The only `sorry` is `derivedRHomAlgebraModule_underlying`; no forbidden declarations or hollow definitions were introduced. The completed theorem uses only the existing sectionwise linearity result and proof irrelevance.
3. The completed statement is unchanged and the private helper arguments are true: equal module structures give equal `ofPresheaf` constructions, and faithful forgetting detects functor equality. No new public statement was split off.
4. The proof follows the unit route through the explicitly constructed Hom functor and its restriction of scalars; no proof dependency or import was removed.
5. DAG proof metadata matches the delivered proof, and the remaining derived comparison obligation is reported unchanged.

Changed only the report and the proof of `sheafAlgebraHomUnderlying_eq`; no pruning was available.
