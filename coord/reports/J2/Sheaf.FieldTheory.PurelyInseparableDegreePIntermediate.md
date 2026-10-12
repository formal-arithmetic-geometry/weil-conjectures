## What changed

Proved `IsPurelyInseparable.exists_degree_p_intermediate` from the final-step consequence of
`IsPurelyInseparable.exists_pth_root_tower`. The proof derives primality from positive
characteristic, rules out the trivial extension using `hdeg`, and packages the tower's final
step into the requested conjunction. Updated the node proof and proof dependencies to match.

## Proved and sorry left

The declaration `IsPurelyInseparable.exists_degree_p_intermediate` is proved. No `sorry` was
added or left in the delivered module.

## No longer needed

The direct proof steps using `lem-weil-pbc-field-degree-multiplicativity` and the separate
finite purely inseparable extension definition are unnecessary: those properties are already
included in the final-step consequence of `lem-weil-pbc-purely-inseparable-pth-root-tower`.

## Where the brief, the DAG or earlier work was wrong

The DAG's detailed three-step route duplicated information already supplied by the tower
node's final consequence. No statement was changed.

## Earlier second reading (a previous round; superseded)

Second reader: pending review by the J2 lead. The proof uses the existing tower declaration,
keeps the target signature unchanged, and its conclusion is exactly the requested statement.

## Second reading by J2

1. Compared the delivered module with the repository version. The theorem signature and all
   existing declarations are byte-for-byte unchanged; only the theorem proof differs.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. There are no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations in the delivered file.
   The theorem's only remaining `sorryAx` dependency comes from the imported tower theorem.
3. Checked the target and node statement clause by clause. The proof supplies exactly the stated
   intermediate field, generator, finiteness, pure inseparability, strict degree inequality,
   generation, p-th-power witness, and relative degree; no statement was added or weakened.
4. Checked pruning. The proof uses only `exists_pth_root_tower`; the multiplicativity and
   separate finite-purely-inseparable dependencies are no longer needed and are removed from
   `proof_deps`. The tower's final-step route and unit `sk-thm-p1` remain in use.
5. Checked the node metadata and source documentation. The node proof and `proof_origin` match
   the implemented route, and no new split-off statements or nodes were introduced.

Changed the report only by recording this second reading; no Lean statement or definition was
changed.
