## What changed

Proved `AlgebraicGeometry.Scheme.restricted_scalar_cone_split` in
`Sheaf.AlgebraicGeometry.RestrictedScalarConeSplit`, with its signature and public imports
unchanged. Three proved private helpers implement the existing node's proof plan:
`derived_map_scalar_identity` passes scalar-identity compatibility through an exact
functor's derived localization; `sheaf_restriction_scalar_identity` checks compatibility
sectionwise from the two section families and their top-section equality;
`scalar_zero_of_iso_biproduct_shifts` transports annihilation through shifts, finite
biproducts, and the supplied isomorphism. The theorem maps the distinguished triangle,
rotates it, and applies Mathlib's `exists_iso_binaryBiproduct_of_distTriang`.

The module compiles through `lcompile.py` with no errors or warnings. The proof works
uniformly for an empty indexing type: `biproduct.hom_ext` has no components to check.
No new modules, public declarations, instances, definitions, or imports were introduced.
The existing DAG plan and its empty `proof_deps` remain accurate: all three steps are
proved locally with the Mathlib machinery already available through the statement import.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.restricted_scalar_cone_split`
(node `lem-sc-restricted-scalar-cone-split`).

All three private helpers are proved. No `sorry` remains in this module; no holes were
added or split off. This is a proof, not a decomposition. The theorem and all three helpers have only `propext`, `Classical.choice`, and
`Quot.sound` in their axiom lists; no upstream `sorryAx` enters this proof.

## No longer needed

None. The sole public import `Sheaf.AlgebraicGeometry.DerivedGlobalScalar` is required
by the statement. No proof imports were added or removed. The original node had no
planned proof-dependency nodes or modules to prune; its three proof steps are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The brief's predicted triangulated argument is
implemented directly. No arbitrary witness of an unproved existence theorem is chosen:
the localization preimage is Mathlib's proved essential-surjectivity construction and
is used only inside the proof. No target, intermediate statement, definition, or public
visibility was changed. The unit route is unchanged.


## Second reading by S3

1. **Interface: pass.** Read the repository and sandbox modules and their full diff.
   The sole existing declaration, `AlgebraicGeometry.Scheme.restricted_scalar_cone_split`,
   has a byte-for-byte identical signature. Its docstring, public visibility, local
   instance attributes, and sole public import are unchanged. All additions are three
   private proved helpers and the replacement of the original proof body. No definitions,
   target statements, change records, or other modules were changed.
2. **Proof and axioms: pass.** Compiled the delivered module with `lcompile.py` without
   errors or warnings, then compiled a scratch copy with `#print axioms` for the theorem
   and all three helpers. Each lists exactly `propext`, `Classical.choice`, and `Quot.sound`.
   No `sorry`, forbidden axiom or implementation directive, or hollow definition occurs.
   The derived compatibility helper first checks complexes degreewise, then cancels the
   localization comparison isomorphism, then transports through Mathlib's proved
   essential-surjectivity isomorphism. No data comes from unproved mere existence.
3. **Split statements: pass (none).** No new public statements, modules, nodes, or holes.
   Read each private helper: top-section compatibility determines every restricted local
   section via the section-family equations; scalar identities commute with morphisms,
   and linear shifts preserve annihilation. Projection extensionality proves the finite
   biproduct assertion even for empty J; a singleton and zero scalar require no extra
   hypotheses. The helpers prove strictly smaller parts of the original argument.
4. **Route and pruning: pass.** Read `DerivedGlobalScalar`, Mathlib's derived linear
   instances and `exists_iso_binaryBiproduct_of_distTriang`, and searched the library for
   scalar restriction and derived scalar compatibility (including the launcher grep
   search for derived functor linearity). No shorter existing full assertion was found.
   The proof already uses Mathlib's splitting lemma directly after rotating the mapped
   triangle: its third map is the negative shift of the proved zero first map.
   The only import defines terms in the unchanged signature and cannot be pruned.
   The old `proof_deps` is empty, so `## No longer needed` is complete. Read
   `dag/units/sk-thm-picard-duality.json`: this auxiliary node realizes no unit statement
   or step, and no unit route or `realized` field is changed.
5. **DAG agreement: pass.** Read `lem-sc-restricted-scalar-cone-split` in full.
   Its three steps match respectively the sectionwise and localization helpers,
   annihilation on shifted finite sums, and rotation followed by splitting.
   The empty `proof_deps` and existing sourced `proof_origin` correctly describe this
   entirely local/Mathlib proof; no node edits are necessary.

Second reading changed only this report: made the axiom result precise and recorded
these checks. No Lean repair was needed. One existing docstring detail is unnecessary:
Mathlib already returns the isomorphism in the desired direction, so the actual proof
uses it directly rather than inverting it. The mathematical argument is unchanged.
