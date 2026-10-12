## What changed
Added the intermediate declaration `exists_presheaf_ext_local_killing_witness` and proved the target theorem by extracting its witness. The intermediate declaration is the remaining proof hole.

## Proved and sorry left
`exists_presheaf_ext_local_killing` is proved from `exists_presheaf_ext_local_killing_witness`. The latter remains `sorry` with node `lem-sc-presheaf-free-ext-local-killing-witness`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The stated Yoneda construction requires substantial derived Ext infrastructure absent from the available declarations, so it was isolated as a named intermediate witness theorem.

## New nodes
`lem-sc-presheaf-free-ext-local-killing-witness` records the intermediate witness theorem.

## Earlier second reading (a previous round; superseded)
The target signature is unchanged. The target proof compiles and uses only the named witness theorem; the witness theorem is strictly packaged with its local-surjectivity and equation witnesses and is recorded by the new node.

## Second reading by J1
1. The delivered module was diffed against the repository version. The target
   declaration has the identical signature; the only added declaration is the
   explicitly recorded witness node.
2. The module compiles with `lcompile.py`. The target has no `sorry`; the one
   remaining `sorry` is exactly the named witness theorem. No forbidden
   declarations were introduced. The target's proof uses only the witness
   theorem and projection, so its axioms are those of that theorem.
3. The witness statement is true by the Yoneda lifting construction described
   in its docstring and is stronger than the target only by the harmless
   packaging marker `True`; it is recorded as node
   `lem-sc-presheaf-free-ext-local-killing-witness`. No duplicate library
   declaration was found.
4. The target route is preserved: the witness theorem packages the stated
   Yoneda/local-lifting step, and no imported module or route node was removed.
   Both existing imports remain necessary for the public statement.
5. The witness node's Lean record, proof plan, source, and declaration agree
   with the delivered theorem and its remaining hole.

Changed only the module by adding the named intermediate witness theorem and
the target proof that extracts its fields, and added this second-reading record.
