## What changed
Proved `schemeMVOrdinaryOpenCounit_square` from a sectionwise component theorem. Added the sectionwise theorem as a named split obligation.

## Proved and sorry left
`schemeMVOrdinaryOpenCounit_square` is proved. `schemeMVOrdinaryOpenCounit_square_app` remains as the sole named `sorry`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned sectionwise calculation was too large to close directly within this delivery, so it was isolated as a component-level theorem.

## New nodes
`lem-pc-mayer-vietoris-ordinary-open-counit-square-section`.

## Earlier second reading (a previous round; superseded)
The main theorem compiles; the remaining sectionwise theorem is explicitly named and recorded as a new DAG node.

## Second reading by U4

1. Compared the delivered module with the repository: the theorem signature is unchanged; only its proof and a proof-only import differ.
2. Compiled both sandbox modules with lcompile.py; compilation succeeds. The main theorem has no sorry; the named component theorem is the only remaining sorry.
3. The component statement is a genuine section component of the parent equality and has the same hypotheses and objects; no definition or target statement changed.
4. The proof follows the unit route through the underived comparison and open counits; no imports were removable.
5. The DAG records the component theorem and its source, proof plan, and dependencies.

Changed the proof to use extensionality and the named sectionwise obligation.
