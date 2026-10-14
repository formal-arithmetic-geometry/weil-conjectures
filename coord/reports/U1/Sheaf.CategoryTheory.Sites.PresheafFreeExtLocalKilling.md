## What changed

Kept the repaired unpadded witness statement and proof, and documented in the
module docstring that its conclusion contains the vanishing equation directly.
The prior landing already removed the upstream review's existential proof
witness and `True` padding; this delivery preserves that corrected signature.

## Proved and sorry left

Both public declarations are proved, with no `sorry` left:

- `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness`
- `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`

The private helpers `epi_locally_surjective` and
`exists_presheaf_cover_lift` are also proved.

## No longer needed

None. All existing imports and proof dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1428 correctly identified the former padded witness statement
as weakened. The repository now contains the corrected direct vanishing
equation, and the caller applies it directly. The earlier retry was rejected
only because its module was byte-for-byte unchanged; this delivery includes a
module-docstring change while retaining the repaired theorem and proof.

## Second reading by U1

1. Compared the delivered module with the repository version. The two public
   theorem signatures and all helper types are byte-for-byte unchanged; only
   the explanatory module docstring was added.
2. Compiled the module alone and with the sandbox import closure using
   `lcompile.py`; both passed with no errors or warnings. Searched the module
   for forbidden declarations and `sorry`; none remain. The proof uses only
   the existing Ext effacement theorem and elementary constructions.
3. Checked the witness and conclusion statements against their DAG nodes and
   the source description. The vanishing equation is stated directly, with
   no existential proof witness or vacuous proposition, and the positive-degree
   hypothesis is retained. No new split-off statements were introduced.
4. Reviewed the proof route and imports. It follows the node route through
   `Ext.exists_epi_comp_eq_zero`, the locally-surjective image argument, and
   the presheaf cover lift; all imported declarations are used, so no pruning
   is available.
5. Confirmed the unit route remains intact: the public conclusion applies the
   witness theorem directly, and the DAG proof dependencies still point to
   `lem-sc-ext-epi-effacement` and the witness node. No DAG or statement change
   is required.

Changed only the module documentation and this second-reading report section;
no proofs, declarations, imports, or nodes were altered.
