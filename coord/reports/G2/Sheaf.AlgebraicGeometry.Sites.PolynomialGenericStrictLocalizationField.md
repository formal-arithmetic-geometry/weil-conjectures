## What changed

Proved `AlgebraicGeometry.Scheme.polynomial_generic_strictLocalization_field` in
`Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField`, with its
statement and public imports unchanged. The existing private theorem
`AlgebraicGeometry.Scheme.residueFieldHomOfOver_eq` identifies the two canonical
residue-field scalar maps, reused through proof-only
`import all Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel`. Finite residue transcendence degree gives a
natural number a with m ≤ a; polynomial smoothness and dimension allow application
of `smooth_strict_local_field_model_core`. Its local domain has dimension m-a=0,
so is a field. The bijective residue map, composed with the core's residue-field
isomorphism, gives the required spectrum of the explicit relative separable closure.

The scalar maps are constructed from the actual scheme morphisms using
`SpecToEquivOfField` and `Spec.preimage`; their compatibility equations are proved.
The existing node's proof, proof dependencies and proof origin now follow this route.
No definitions, public signatures or consumers were changed. The unit record has
empty realized statement/step lists; no unit statement or route was bypassed.

Repair validation: the proof compiled without warnings in 2.6 seconds.
`#print axioms AlgebraicGeometry.Scheme.polynomial_generic_strictLocalization_field`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. The temporary audit
command was removed from the delivered file. The construction and truncated
subtraction also cover m=0 without a positivity assumption.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.polynomial_generic_strictLocalization_field`
(node `lem-sc-polynomial-generic-strict-localization-field`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
This is a proof, not a decomposition, and its transitive axioms contain no sorry axiom.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel`, replaced by its geometric core.
- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal`, whose upstream
  local structures are unnecessary here.
- `WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField`, unused by this proof.
- `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`, replaced by the core
  residue-field equivalence and Mathlib separable-closure instance.

This proof no longer needs the original dependency
`lem-sc-smooth-strict-local-field-model` / `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel`,
or its coefficient-field branch:
`lem-sc-smooth-strict-local-field-model-coeff` /
`Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeff`,
`new-lem-sc-smooth-strict-local-field-model-coeff-data` /
`Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffData`, and
`new-lem-sc-smooth-strict-local-field-model-coeff-fraction-trdeg` /
`Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffFractionTrdeg`.
It also no longer directly needs
`lem-weil-pbc-strict-henselization-local-structure` /
`Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`: the core supplies
locality and the residue-field equivalence, and Mathlib supplies separable closedness.
These are dependencies pruned from this proof, not claims of global unreachability;
other consumers may still need them. No module is withdrawn. Removed the duplicate private declaration
`AlgebraicGeometry.Scheme.residueFieldHomOfOver_eq_local` from the returned delivery;
the existing scalar-map equality is reused instead.

## Where the brief, the DAG or earlier work was wrong

The original plan requested the full coefficient-field model and a separate
strict-henselian local-structure theorem. Its generic case only needs the core's
dimension and residue-field clauses; no lifting of a coefficient field is required.
The return correctly identified a duplicate private scalar-map theorem. The previous
reading overlooked that a proof-only `import all` allows reuse of the existing
private theorem. The duplicate is removed, its use is redirected to the existing
theorem, and the DAG proof text records this reuse. No definition or public
interface repair is needed. The previous second reading was removed because it
reviewed the superseded duplicate helper; the independent reader must review this
repair anew. The blueprint's generic
strict-localization step is retained, including the case m=0.

## Second reading by G2

1. Compared the sole delivered Lean module with the shared repository using `diff`.
   The existing theorem signature is byte-for-byte identical; its docstring,
   visibility, options and all four public imports are unchanged. Only proof imports
   and the former `sorry` body differ. No definitions or other modules are delivered,
   so no change record or forced adaptation is required. Read the G2 return dated
   2026-10-17 04:19 UTC: the duplicate private helper is absent, and the proof now
   uses the existing `Scheme.residueFieldHomOfOver_eq` through `import all`.
   Verdict: passes statement and interface preservation.

2. Independently compiled the delivered file through `lcompile.py`: clean, 2.5 s.
   Compiled the scratch copy containing `#print axioms` as well: the target uses
   exactly `propext`, `Classical.choice`, and `Quot.sound` (2.4 s). Scanned the
   delivered source: no `sorry`, forbidden declaration or kernel-bypass token;
   all lines fit 100 columns. Checked the actual core signature: the proof supplies
   smoothness, integrality, finite type, quasi-compactness, dimension, the geometric
   point equation and both scalar-map compatibilities. Its extracted domain and
   local structures are precisely those used for the residue field. The final
   contravariant `Spec.mapIso` has the required orientation. The field L is the
   explicitly defined relative separable closure, not an arbitrary witness chosen
   from an unproved existence theorem. Verdict: a complete proof with no residual
   axiom dependency or hollow construction.

3. There are no new declarations, split-off statements, modules or nodes. The
   ledger count is one original hole closed and zero added. Searched the library
   for generic strict-localization/field results and scalar-map equalities, and ran
   `msearch.py ... grep` for field strict-henselization results. The existing
   `StrictHenselizationField` result assumes an already given field base and does
   not directly solve the polynomial case. Read the reused scalar-map lemma:
   it equates exactly the two canonical maps in this proof. Checked m=0: the
   truncated subtraction still vanishes without positivity. For m>0, m<=a is
   used in the same dimension argument, with no missing genericity assumption.
   Verdict: no duplicate or disguised split, and the edge case is retained.

4. Read the finite residue transcendence-degree theorem and the smooth strict-local
   core, and the blueprint proof's local calculation and exceptional q=2 generic
   stalk paragraphs in `main-20261015/.../thm-sc-affine-torsion-cd.proof.md`.
   The existing core already gives the dimension and residue equivalence needed;
   the coefficient-field model would add unused work. The concrete scalar maps
   establish that its hypotheses refer to the actual structural maps. Proof-only
   imports are plain imports (including `import all`); the unchanged public imports
   provide the statement's objects and predicates. The report names both original
   proof dependencies omitted by this route and all removed direct imports.
   `dag/units/sk-prop-sf-cbc.json` has empty realized statement and step lists, and
   this remains the blueprint's generic strict-localization step. Verdict: route
   preserved and pruning accurately described as local, not global withdrawal.

5. Compared the delivered node JSON with the repository: only `proof`,
   `proof_deps`, and `proof_origin` change. Its two dependency ids resolve to
   `finite_trdeg_residueField` and `smooth_strict_local_field_model_core`, exactly
   the non-elementary project theorems applied by the proof. The final field and
   spectrum step names the Mathlib facts actually used. The recorded proof source
   matches the blueprint paragraphs read above. Verdict: the DAG agrees with Lean.

This second reading changed only this report, adding the independent checks above.
No further proof repair was necessary after the duplicate-helper repair.
