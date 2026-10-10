1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-zero-scheme-locally-principal.json`: split statement, three proof steps, and corrected split metadata.
- `dag/nodes/sec-picard-framework/lem-pc-invertible-sheaf-instance.json`: closed project lemma `AlgebraicGeometry.Scheme.Modules.IsInvertible.sheafOfModules_isInvertible` (Mathlib search: no match).
- `dag/nodes/sec-picard-framework/lem-pc-invertible-common-free-generator.json`: closed project lemma `AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator₂` (Mathlib search: no match).

2. Attachments:

- `AlgebraicGeometry.Scheme.Modules.IsInvertible.sheafOfModules_isInvertible` belongs to the new bridge node.
- `AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator₂` belongs to the new common-trivialization node.

3. WANTED: none.

4. The earlier attachment was rejected because the item hypotheses use `AlgebraicGeometry.Scheme.Modules.IsInvertible`, while `Hom.isLocallyPrincipal_zeroLocus` requires `SheafOfModules.IsInvertible`. I checked `ProjectionFormula.lean` and added the exact conversion theorem as a closed node. I also checked the source declaration at `ZeroLocus.lean:90-98` and added its common affine-trivialization lemma as a closed node; this is the non-elementary existence input in the proof. The existing `lem-pc-zero-scheme-ideal-local` node was read and its statement supplies exactly the affine ideal equality used in the final step.

## Review by F1

I read `ZeroLocus.lean` around lines 479-576 and `ProjectionFormula.lean` around lines 110-124. Step 1 uses the conversion node verbatim for M and N, so the theorem's sheaf-level typeclass assumptions are actually present. Step 2 applies `exists_isFreeGenerator₂` with W equal to the top open, checks that its hypotheses are the point membership and the two sheaf-level invertibility instances, and then uses the free-generator definition to obtain the coefficient b. Step 3 applies the existing affine-ideal node with exactly U, eM, eN, and b; its quoted statement is the equality required by `IsLocallyPrincipal`. I checked the item on the zero morphism as well: b=0 gives the principal zero ideal, so no nonzero-morphism assumption was introduced. `citations.json` quotes are verbatim portions of the cited node statements.

## Second reading by F1

- Item statement: checked against `ZeroLocus.lean`, `Hom.isLocallyPrincipal_zeroLocus`, lines 570-576; the scheme, two invertible modules, and arbitrary linear morphism hypotheses and locally-principal conclusion agree.
- Step 1: checked against `lem-pc-invertible-sheaf-instance` and `ProjectionFormula.lean`, lines 122-124; its statement gives precisely the two sheaf-level invertibility instances required downstream.
- Step 2: checked against `lem-pc-invertible-common-free-generator` and `ZeroLocus.lean`, lines 571-575; the cited statement supplies the affine neighborhood and both free generators, and obtaining `b` from the free-generator property is elementary.
- Step 3: checked against `lem-pc-zero-scheme-ideal-local` and `ZeroLocus.lean`, lines 571-576; its hypotheses match `U`, `eM`, `eN`, and the coefficient equation, and the resulting equality is exactly the local-principal witness.
- `lem-pc-invertible-sheaf-instance`: checked as a statement-only closed project lemma against `ProjectionFormula.lean`, lines 122-124; dependencies and typeclass meanings are explicit, with recorded Mathlib searches.
- `lem-pc-invertible-common-free-generator`: checked as a statement-only closed project lemma against `ZeroLocus.lean`, lines 90-98; all objects and hypotheses are introduced, with recorded Mathlib searches.
- No new node duplicates an existing DAG fact; the affine ideal fact is cited from existing `lem-pc-zero-scheme-ideal-local`.
- Edge cases checked: the zero morphism yields `b = 0` and the principal zero ideal; a field and the empty scheme satisfy the same local witness formulation; no assumption on nonzeroness or positive dimension is used.
- Changes: none to mathematical statements or proof dependencies. The delivery dry run passed citation, Mathlib-search, duplicate, DAG, and preflight checks.
