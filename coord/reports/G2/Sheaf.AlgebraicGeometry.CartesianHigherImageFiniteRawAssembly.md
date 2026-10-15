## What changed

Proved `AlgebraicGeometry.Etale.exists_cartesianHigherImage_finite_raw_assembly` in
`Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly`, preserving its complete
signature and both original public imports. Added proof-only imports of
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal` and
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc`.

The private helper `cartesian_map_eq` identifies the canonical projection using the pullback
universal property. `cartesian_map_comp` combines horizontal exchange pasting with inverse-image
associativity, using naturality to move the coefficient comparison. The private
`pulled_cartesian_map_comp` transports this composition law to a fixed base. A proof-irrelevant
congruence helper handles `D.map_comp` without expensive unfolding of the derived functors.
`rawTransition` is exactly the displayed unshifted map, and `rawTransition_comp` proves its
composition law. All helpers are fully proved; the definition contains actual morphisms.

Choose the individual witnesses from `hkill`, apply Mathlib `IsCofiltered.wideCospan`, and
factor the common transition through each individual killing map. The shift functor preserves
composition, and postcomposing a zero morphism gives zero. This also covers the empty family:
`wideCospan` supplies a witness over the fixed object without a nonemptiness assumption on `J`.
No geometric hypothesis beyond the displayed categorical constructions is needed in this
assembly step. The limiting-proof binder is retained unchanged and explicitly referenced locally.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.exists_cartesianHigherImage_finite_raw_assembly`.
There are no sorries left in the module and no holes added elsewhere (1 closed, 0 added).
This is a complete proof, not a decomposition.

Single-file compilation succeeds in approximately six seconds with no warnings.
`#print axioms AlgebraicGeometry.Etale.exists_cartesianHigherImage_finite_raw_assembly`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`; the temporary print command
was removed afterward. Lines are at most 100 characters. The existing statement is unchanged.

## No longer needed

None. Both original public imports are required by the statement: the transition constructions
and `abelianComparisonFree`. Both new proof-only imports are used explicitly. No new node,
module, axiom, or unproved dependency is introduced, and no existing DAG route is replaced.

## Where the brief, the DAG or earlier work was wrong

The assigned module has no matching DAG node in this checkout: searching all `dag/nodes`
for its module name and its declaration returns no record, and its original docstring has
no blueprint tag. The parent node
`lem-sc-cartesian-higher-image-finite-raw-class-vanishing`, step 3, describes exactly this
assembly argument. Its unit `sk-thm-vanishing` has no realized node for this helper, so the
proof preserves the unit route. No existing node was edited merely to work around the
missing attachment.

The informal description mentions identity laws, but this proof only needs composition and
Mathlib's finite wide-cospan theorem. Individual witnesses are hypotheses, so affine descent,
cohomology continuity, and class-compatibility theorems are unnecessary as proof inputs here.
The source read was Stacks Tag 0EYM, construction of transition maps and their composition,
and its second proof. Library search found the already-proved horizontal pasting and
inverse-image associativity declarations; Mathlib search found `IsCofiltered.wideCospan`
and `IsCofiltered.cospan`.

## Second reading by G2

1. **Interface: PASS.** Compared the sole delivered module with the repository using
   `diff -u`, and separately compared the complete existing theorem signature as text:
   it is byte-for-byte identical. Both original public imports and all hypotheses remain.
   The added imports are proof-only. No other module or definition used by targets changes.
2. **Proof and axioms: PASS.** Independently compiled the delivered module in 6 seconds
   through `lcompile.py`, with no warnings. Compiled a scratch copy with `#print axioms`
   for all seven declarations (the target, five private lemmas, and `rawTransition`): each
   reports only `propext`, `Classical.choice`, and `Quot.sound`. Source scanning found no
   `sorry` or forbidden declaration. The transition definition constructs the displayed
   composite; the only witness choices use the proved hypothesis `hkill` and Mathlib's
   proved wide-cospan lemma. No object is chosen from an unproved existence theorem.
3. **Split statements and edge cases: PASS.** None were split off; all private helpers
   are proved. Checked that both projection equations identify the composite pullback
   projection, and that exchange pasting, naturality, and inverse-image associativity
   yield the exact raw transition composition. The congruence step uses `D.map_comp`
   and proof irrelevance. Mathlib's `wideCospan` supplies commuting factorizations into
   the fixed index for every finite family, including the empty family. Singleton
   families, zero classes, empty affine test objects, and degree zero require no extra
   assumption or separate argument.
4. **Route and pruning: PASS.** Read the imported constructions and the upstream
   horizontal-pasting and inverse-image-associativity lemmas. Repeated searches with
   Loogle (`"IsCofiltered", "Finite"`), Lean Finder (commuting cones over a finite
   family of arrows), and `rg` for cartesian transition composition. No existing raw
   composition theorem replaces the private calculation; `wideCospan` is the direct
   finite assembly API. Both public imports are needed by the signature, and both
   proof-only imports supply explicitly used lemmas. No original import or node is
   pruned. Read `sk-thm-vanishing.json`: its `realized` entries are untouched, and the
   parent node's elementary common-stage step is followed.
5. **DAG correspondence: PASS with existing attachment gap.** Independently searched
   `dag/nodes` for the module and declaration: neither has a matching node. Read
   `lem-sc-cartesian-higher-image-finite-raw-class-vanishing`: its third proof step
   specifies precisely this finite wide-cospan assembly, and its `proof_origin` already
   records that API. Its other dependencies belong to constructing individual
   witnesses in the parent theorem and are not pruned by this helper proof. There are
   no delivered node records or split-off statements to reconcile. The missing helper
   attachment is recorded above; no unrelated DAG metadata was changed.

Changed only the theorem docstring to describe the actual composition and wide-cospan
argument, removing its inaccurate claim that identity laws are used, and appended this
review. No proof repair was needed. Confirmed net holes: 1 closed, 0 added; none left
in this module.
