## What changed
Replaced the rejected restatement auxiliary theorem with the strict intermediate theorem
`affineTensorPullbackHomologyStalkIso_counit_coordinate`.  It isolates the geometric
localization identity up to the inverse ordinary pullback counit and the supplied
representative isomorphism.  The target theorem applies this theorem and closes the
remaining composition by functoriality of homology and stalk maps.

## Proved and sorry left
`affineTensorPullbackHomologyStalkIso_coordinates` is proved.  One sorry remains in
`affineTensorPullbackHomologyStalkIso_counit_coordinate`; it is the affine localization
identity, strictly a component of the target argument and not the target statement.

## No longer needed
The previous auxiliary theorem
`affineTensorPullbackHomologyStalkIso_coordinates_aux`, which duplicated the target,
is removed.  No imports, planned dependency nodes, or modules beyond that rejected
restatement are needed.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt split off the complete target equation under another name.  That is
not a reduction.  The corrected split stops before the final representative map and
proves the final assembly directly with `Functor.map_comp`.

## New nodes
None; the existing node `new-lem-pc-affine-tensor-pullback-stalk-coordinates-at`
records the intermediate affine localization identity and its source proof plan.

## Earlier second reading (a previous round; superseded)
The original public definition remains in its original module and the target proof compiles. The remaining hole is the strict inverse-counit localization component; the final supplied isomorphism is assembled by `Functor.map_comp`.

## Second reading by M2
1. Compared the delivered module with the repository version. Existing declaration
   signatures are unchanged; only the intermediate theorem and proof bodies differ.
2. The target proof is a direct composition argument. The sole remaining `sorry` is a
   named public theorem with source documentation and a matching DAG node; no hollow
   definition or forbidden declaration was introduced.
3. The split theorem states only the inverse-counit localization component, strictly
   weaker than the target and needed for the final composition; it is not a restatement.
4. The proof uses the existing affine base-change import and `Functor.map_comp`; the
   rejected duplicate auxiliary theorem was removed and the unit route is retained.
5. The DAG node's declaration, statement, source, proof dependency, and split status
   match the Lean theorem.

Changed during this reading: added this review record; no Lean declarations or DAG
content required repair.
