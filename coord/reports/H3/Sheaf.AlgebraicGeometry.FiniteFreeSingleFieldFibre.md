## What changed

Added proof imports and proved `nonempty_homotopyEquiv_single_field_fibre` by combining two strictly simpler named intermediate results: preservation of the single cohomology condition under field pullback, and the field-complex homotopy normal form.

## Proved and sorry left

The target theorem is proved by a complete Lean term. The two intermediate theorems `single_field_fibre_homology` and `homotopyEquiv_of_single_field_homology` remain as named `sorry` declarations, with source and proof descriptions in their docstrings and DAG nodes.

## No longer needed

None of the existing proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The imported plan omits the explicit algebraic splitting and the pullback homology comparison as Lean declarations; these are recorded as two intermediate nodes.

## New nodes

`new-field-fibre-homology` and `new-field-complex-homotopy-normal-form` are strict subclaims used by the target proof.

## Second reading by H3

1. **Interface unchanged.** Compared the delivered target module with the repository version; the existing theorem signature is byte-for-byte identical. The two added modules contain only the explicitly split intermediate declarations.
2. **Compilation and proof hygiene.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. The target has no `sorry`, while the two split declarations are the only named `sorry`s. No forbidden commands or hollow definitions occur.
3. **Statements and nodes.** Checked both split statements against their Lean declarations and DAG nodes. They are strict subclaims of the target, with source/docstring descriptions and matching `lean`, `proof`, and `proof_deps` records; no duplicate upstream declaration was found.
4. **Pruning and route.** The target proof uses both split declarations, preserving the unit route. The added imports are proof-only plain imports; no existing proof dependency was removed.
5. **Unit and DAG consistency.** The target and both split nodes remain in `sk-thm-picard-perfect`, and the target's proof follows the recorded pullback-then-field-normal-form route. No statement or definition change was made.

I found no repair necessary. I only added this second-reading record; the delivered Lean files and DAG nodes are unchanged.
