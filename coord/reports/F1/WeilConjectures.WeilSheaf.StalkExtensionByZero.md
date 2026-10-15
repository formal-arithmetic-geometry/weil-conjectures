## What changed

Proved `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_extensionByZero` in
`lean/WeilConjectures/WeilSheaf/StalkExtensionByZero.lean`, with its signature unchanged.
Added proof-only imports of `WeilConjectures.WeilSheaf.OpenImmersionRestriction` and
`WeilConjectures.WeilSheaf.StalkUpperStar`. Both pass the import-direction check.

The proof uses the existing Weil-sheaf isomorphism `j^* j_! G ≅ G`, the existing
Frobenius-compatible pullback-stalk comparison, and the existing comparison between
geometric points over the same finite point. The geometric point obtained from the
chosen point of U and the chosen point of X need not coincide; their projections do,
which is exactly the hypothesis of `nonempty_equiv_stalkAt`. The open immersion
preserves the residue degree, so all three equivalences use the same local Frobenius.
Their composition gives the claimed equivalence.

Added the proved private helper `stalkAt_eq_of_degree_eq` to transport a stalk across
an equality of degrees while retaining its dependent Frobenius compatibility proof.
It is just equality elimination. No definition, existing signature, public import,
or other module was changed.

Single-file compilation is clean (approximately 3.2 seconds). An additional scratch
compile of the exact source with `#print axioms` checks both the new proof and
`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.extensionByZero`: each uses only
`propext`, `Classical.choice`, and `Quot.sound`. There are no transitive sorry axioms
in either checked theorem. The argument requires no nonzero stalk, nonempty U,
positive degree side condition, or finite-type hypothesis beyond the original
signature; zero sheaves and empty opens are covered by the same constructions.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_extensionByZero`.

Proved 1 of 1 original sorries. Added 0 sorries and split off 0 obligations. No
`sorry` remains in the item module or in any new declaration. The private helper
`stalkAt_eq_of_degree_eq` is completely proved. This is a proof, not a decomposition.

## No longer needed

None: no original import was removed, no module was withdrawn, and no existing DAG
node is claimed pruned. Each of the two added proof imports supplies a theorem used
in the proof. No `Sheaf.*` intermediate statements or new modules are needed.

The section-colimit and sheafification argument need not be rebuilt for this item:
the established restriction isomorphism and stalk comparison API already provide
its geometric and Frobenius compatibility content. In particular the downstream
`WeilConjectures.WeilSheaf.ExtensionByZero` cannot be imported here (it imports the
item), and its stronger finite-type hypotheses are unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The source docstring points to
`lem-cbc-proetale-extension-zero`, but that node states the general finite-coefficient
pro-etale extension-by-zero theorem, not this adic Weil-sheaf Frobenius comparison.
There is no node whose primary `lean.module` is this item; matches for the module
and declaration in the DAG are transitive `lean_audit` entries of other nodes.
Consequently no unrelated node proof or unit route was rewritten. The item is
proved using existing library declarations, without introducing a new obligation.

During development, a local `let` alias for the extended sheaf caused Lean to
unfold large pullback and Frobenius constructions when comparing functor objects.
Diagnostics identified the excessive reductions. Keeping the extended-sheaf
expressions syntactically identical, explicitly expanding the local geometric-fiber
map alias at composition, and explicitly transporting the degree resolves this: the final source compiles
under the default limits, with no diagnostic or heartbeat overrides.

## Second reading by F1

1. **Interfaces and accidental changes: PASS.** I compared the delivered module
   against the repository version. Every existing declaration signature, including
   the target theorem and the two exactness instances, is byte-for-byte unchanged.
   The only additions are two proof-only imports, one private proved helper, and
   the replacement of the target theorem's `sorry` by its proof. No definition,
   public import, visibility, or downstream interface changed.

2. **Proof and axioms: PASS.** The module compiles with the required single-file
   compiler and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. A scratch compile with `#print axioms` reports only
   `propext`, `Classical.choice`, and `Quot.sound` for both the newly proved stalk
   equivalence and the punctual-purity theorem that uses it.

3. **Statements and search: PASS.** The target statement is unchanged and is
   proved directly by composing the existing upper-star stalk comparison, the
   restriction isomorphism for extension by zero, and the geometric-point stalk
   comparison. The private degree-transport helper is equality elimination only;
   it adds no public obligation or split-off statement. Searches found no existing
   declaration duplicating the target theorem or this helper.

4. **Pruning and route: PASS.** Both added imports are used by the proof and are
   plain proof imports. No original import or proof dependency is unused, and no
   module can be pruned from this item. The route keeps the established
   restriction/upper-star unit route and avoids the downstream extension-by-zero
   module, which would introduce a cycle.

5. **DAG and report agreement: PASS.** The repository has no primary DAG node for
   this module or theorem; the occurrences are audit references with empty node
   lists, so there is no node record to update. The report records one original
   hole closed, no holes added, and no split obligations. The final source and
   report agree on all declarations and imports.

The second reading changed only this report by adding the required review record;
no Lean source or DAG file was changed during review.
