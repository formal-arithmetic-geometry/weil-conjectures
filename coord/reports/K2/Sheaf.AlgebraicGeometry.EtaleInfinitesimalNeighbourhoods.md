## What changed
Added a pointwise intermediate theorem (left as a named sorry) and proved the target by taking the supremum of the pointwise étale opens and applying étale locality on the source.

## Proved and sorry left
The target `etale_on_open_of_etale_infinitesimal_neighbourhoods` is proved. The intermediate theorem `etale_infinitesimal_pointwise` remains sorry.

## No longer needed
No imports or DAG dependencies were pruned; all existing imports remain required by the pointwise intermediate statement.

## Where the brief, the DAG or earlier work was wrong
The global open is most directly constructed as the supremum of pointwise opens using `Scheme.Opens.iSupOpenCover`; the DAG's informal union argument omitted this API detail.

## New nodes
`lem-weil-pbc-etale-infinitesimal-pointwise`.

## Earlier second reading (a previous round; superseded)
The pointwise reduction and supremum construction compile in the sandbox; the remaining sorry is isolated in the new pointwise node.

## Second reading by K2

1. Compared the delivered module with the repository version. The theorem signature is byte-for-byte unchanged; only the proof, its pointwise helper import, and the new helper module/node are added.
2. Compiled both modules with `lcompile.py --all`; both compile cleanly. The only remaining `sorry` is the named theorem `etale_infinitesimal_pointwise`, recorded by node `lem-weil-pbc-etale-infinitesimal-pointwise`. No forbidden declarations or hollow definitions were introduced.
3. The split-off pointwise statement is true and exactly the needed intermediate conclusion, with a complete source-based proof description and matching DAG node. It is not duplicated elsewhere in the library. The main theorem's proof uses the pointwise theorem and the standard `iSupOpenCover` locality API.
4. The route preserves the unit's pointwise-to-global structure. The DAG proof and `proof_deps` were updated to match the implemented pointwise reduction and supremum cover. The target's unused proof-only imports were pruned: BaseChangeConventions, EtaleOpenOfSmoothZeroFibreDimension, EtaleSmoothZeroDimensionalFibres, FormallySmooth, SmoothArtinianLiftingAtPoint, Thickening, and Topology.KrullDimension.
5. No target or existing declaration statement changed. The main theorem is proved; the pointwise theorem remains the sole split-off statement.

Changed the target node's proof metadata and pruned the imports listed above. No mathematical statement was changed.
