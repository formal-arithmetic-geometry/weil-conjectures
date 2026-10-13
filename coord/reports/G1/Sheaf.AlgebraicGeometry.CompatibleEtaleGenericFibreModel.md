## What changed

Replaced the sorry in `AlgebraicGeometry.exists_compatible_etale_generic_fibre_model`
with a complete Lean proof from one strictly smaller intermediate statement.
Added a proof-only import of `Sheaf.AlgebraicGeometry.EtaleGenericResidueFieldModel`.
All existing signatures and public imports are unchanged; no definition was added or changed.

The new model statement is independent of X and contains only the geometric spreading
construction and its residue-field identification. The delivered proof constructs the
fibre comparison isomorphism using two pullback-pasting isomorphisms and a pullback map,
proves the embedding and exact range, and explicitly constructs the comparison after
an arbitrary field extension with its required commuting equality. It compiles without
warnings through lcompile.py. The original node's proof dependencies now follow this proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_compatible_etale_generic_fibre_model`
(node `lem-sbc-compatible-etale-generic-fibre-model`), by reduction to the spreading lemma.
No sorry remains in the assigned module.

Added and left: `AlgebraicGeometry.exists_etale_generic_residue_field_model`
(node `lem-sbc-etale-generic-residue-field-model`), exactly one named public theorem
with `:= by sorry`. Its source and complete construction are in its docstring and node.

This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
The categorical fibre comparison, embedding, range, and field-extension compatibility
are proved with no additional holes. All existential witnesses are eliminated within
proofs of propositions; no data definition chooses a witness from an unproved existence
statement.

## No longer needed

No original imports were removed: the three original Mathlib imports are required by
the unchanged statement. The new model module uses `Mathlib.AlgebraicGeometry.ResidueField`
in place of the unnecessarily broad `Mathlib.AlgebraicGeometry.Fiber` import. No existing module or node is claimed pruned from the target closure.

`lem-weil-pbc-finite-separable-primitive-element` is no longer a direct proof dependency
of the assigned node; it remains a dependency of the new spreading node and is therefore
not pruned. No separate dependencies for fibre embedding, exact range, pullback pasting,
or geometric field extension are needed: Mathlib proves all of this glue.

## Where the brief, the DAG or earlier work was wrong

The original plan's steps 2 and 3 were substantial steps without named declarations.
Step 3 is now fully proved; steps 1 and 2 are precisely the remaining model statement.
The existing finite-separable spreading theorem requires a Noetherian domain, and
GenericPointedEtaleExtension requires an integral scheme; neither handles arbitrary
nonreduced irreducible S as required here. No extra hypotheses were added.

The unit record sk-prop-normal-form has empty realized statement and step lists, so the
new route bypasses no realized unit step. Edge cases checked in the model construction:
nonreduced S uses its prime nilradical rather than a domain hypothesis; degree-one L
uses the same monic construction; an empty S has no IrreducibleSpace instance. The
categorical proof makes no choice of a point of X or its fibre and applies to empty X.

## New nodes

`lem-sbc-etale-generic-residue-field-model`, in
`lean/Sheaf/AlgebraicGeometry/EtaleGenericResidueFieldModel.lean`, isolates the monic
polynomial spreading construction of Stacks Tag 0551 and a compatible generic residue
field isomorphism. It has no X, fibre inclusion, range condition, or quantifier over
further field extensions. Its proof is the first two steps of the original argument.
The old node is updated only in proof, proof_deps and proof_origin. The new node
also reuses `lem-weil-pbc-etale-residue-polynomial-lift` for its denominator-clearing step. No change record
or forced adaptation is required.


## Second reading by G1

1. **Interface unchanged: pass.** Diffed the delivered assigned module against the
   repository and compared its theorem signature byte for byte. The only Lean changes
   there are the theorem proof and a plain proof-only import. All original public
   imports remain necessary for its signature. The second module is new. No existing
   definition, declaration signature, visibility, or target statement changes.
2. **Proof and trust: pass.** Both modules compile locally in import order without
   errors or warnings. Scratch copies with `#print axioms` report exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both the parent
   and the split lemma. There is exactly one remaining hole, in the named
   public spreading theorem listed above. No forbidden declaration, hollow definition,
   or data-valued choice from an unproved existence statement is present. The parent
   eliminates the existential model inside a proof of a proposition.
3. **Split statement: pass as a decomposition.** The remaining statement removes X,
   the fibre embedding/range, and the further-field-extension compatibility. The parent
   proves those clauses by pullback pasting and projection equations, so this is a real
   reduction, not a restatement. Read Stacks Tag 0551's monic quotient construction.
   Checked nonreduced irreducible bases (prime nilradical), degree-one extensions, and
   empty X; empty S cannot satisfy IrreducibleSpace. Independent leanfinder search for
   separable extensions realized as generic residue fields, loogle search
   `Algebra.Etale, Ideal.ResidueField`, msearch grep for residue-field isomorphisms and
   irreducible etale models, and local library searches found no exact replacement.
   `exists_etale_neighbourhood_prescribed_residueField` and
   `Algebra.exists_etale_residueField_equiv` give prescribed points but do not supply
   the required genericity of the entire model. The other spreading/irreducible-open
   results impose domain, integral, or Noetherian hypotheses unavailable here. Closing
   the new hole is therefore not a short application of an existing theorem.
4. **Route and pruning: pass.** Read the parent proof from the top downward. Mathlib
   supplies the pullback isomorphisms, embedding, exact range, and base-change equality;
   the only new imported statement is the genuinely smaller geometric construction.
   No shorter route found. The old primitive-element proof dependency remains below
   the new node and is correctly reported as no longer direct but not pruned. No module
   is claimed pruned. Read `sk-prop-normal-form.json`: its realized statement and both
   realized step lists are empty, so this reduction bypasses no realized unit step.
5. **DAG agreement: pass after repair.** The parent node changes only proof,
   proof_deps, and proof_origin and records the residue model followed by the actual
   categorical proof. The new node has its source, statement dependencies, proof plan,
   searches, status, creation/provenance, chapter/unit, and exact Lean statement. Its
   denominator-clearing step now cites the existing residue-polynomial-lift node rather
   than silently rebuilding that part of the library.

Second reading changed the new theorem's natural-language proof to state the correct
specialization direction: flat going down gives q contained in every prime Q, hence q
is generic. Added the existing denominator-clearing lemma to the new node's proof
step and proof_deps and named it in the docstring. Replaced the new module's unused Fiber import with
ResidueField. The compiled categorical proof and
all theorem signatures are unchanged. One hole closed and one hole added: decomposition,
net zero holes; no additional hole closed during second reading. No change record needed.
