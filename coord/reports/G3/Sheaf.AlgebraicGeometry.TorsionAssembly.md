## What changed

Proved `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_torsion_assembly` in
`Sheaf.AlgebraicGeometry.TorsionAssembly`, with the original signature and all three public
imports unchanged. Added proof imports of `TorsionSheafCharacterizations`, `DerivedForget`,
and `AbTorsionSheaf`. Updated its docstring and DAG proof to match the implementation.

The source library already performs the prime-factor induction, five-lemma transfer, and
filtered-colimit passage. Its `hasTorsionBaseChange_of_isProper` applies to arbitrary
module coefficients with torsion cohomology. Lift the abelian sheaf along the proved
forgetful equivalence for `ULift ℤ`, check torsion via the existing characterizations, and
apply that theorem to the single complex. The proved comparison for the derived exchange
and the single-functor comparison transport the specified map back to abelian sheaves.
Mapping this isomorphism through every homology functor proves the second conjunct.

The unit route is retained inside the source-library theorem: `ProjectiveLine` uses the
projective-line case and reduction; `Reduction` uses `hasTorsionBaseChange_of_forall_prime`;
`Coefficients` uses `Devissage`, which contains the prime-factor induction and filtered
colimit passage. No unit statement or step is bypassed. No definitions, instances, target
statements, or other modules changed.

Validation: the complete proof compiled locally, then compiled again after pruning the
unused imports. The required delivery dry run provides the final compile and axiom probe.
The theorem still depends on the existing upstream proof obligations; no claim is made
that its transitive axiom closure is already sorry-free.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_torsion_assembly`
(node `lemma-weil-pbc-torsion-assembly`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
This is a proof from existing declarations, not a decomposition into new obligations.

## No longer needed

Removed these nine direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.ProperBasic`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Removed the following direct DAG proof dependencies (the source library's reused theorem
continues to provide its own internal proof dependencies):

- `lem-weil-pbc-derived-plus-iso-on-cohomology`
- `prop-weil-pbc-inverse-image-exact`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-torsion-etale-sheaf`
- `def-weil-pbc-abelian-etale-sheaves`
- `lem-sf-derived-ses-triangle`
- `def-weil-pbc-derived-categories`
- `lem-weil-pbc-derived-direct-image-triangulated`
- `def-weil-pbc-derived-inverse-image`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-weil-pbc-derived-exchange-triangulated`
- `def-weil-pbc-triangles-with-shift`
- `lem-sf-derived-homology-long-exact`
- `lem-weil-pbc-derived-cohomology-ladder`
- `lem-weil-pbc-five-lemma`
- `pqf-lem-proper-basic`
- `lemma-weil-pbc-direct-image-filtered-colimit`
- `lem-weil-pbc-inverse-image-preserves-colimits`
- `lem-weil-pbc-proper-base-change`

The retained module-coefficient proper-base-change theorem already incorporates the exact
sequence, triangulated, cohomology-ladder, five-lemma, properness, and filtered-colimit
arguments. They need no separate proof in this item. Global reachability of their modules
is for the maintainer's closure ledger; this delivery prunes the direct imports above.

## Where the brief, the DAG or earlier work was wrong

The node calls its dependency `lemma-weil-pbc-prime-proper-base-change`, but that node's
actual attached Lean declaration `hasTorsionBaseChange_of_isProper` is already the general
module-coefficient theorem, not only the prime case. Repeating the planned assembly would
duplicate its existing proof. The original DAG plan and docstring also omitted the
already proved abelian/module exchange comparison and torsion characterization that make
the reuse immediate. The revised proof records these facts without changing the statement.

Importing `BaseChangeTheorems.Proper` would create a cycle through this item; the proof
uses the lower `ProjectiveLine` theorem and `DerivedForget` comparison directly. All three
new proof imports were checked for import-cycle compatibility.

## Second reading by G3

1. **Diff and statements:** Compared the delivered module and node with the repository
   versions. The theorem signature is byte-for-byte unchanged; only the proof, docstring,
   proof dependency list, and proof imports changed. No target or definition changed.
   **Verdict: pass.**
2. **Proof and axioms:** Compiled `TorsionAssembly.lean` with `lcompile.py`; it has no
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses the
   existing module-coefficient theorem and the proved forgetful-equivalence comparison;
   the scratch-copy `#print axioms` probe reports exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` from existing open upstream obligations. The equivalence
   used to choose the lift and the derived exchange comparison both have only the three
   standard axioms. **Verdict: pass.**
3. **Statements and split-offs:** No statements were split off and no new theorem or
   definition was added. The existing torsion characterization and equivalence declarations
   are used with their original strength; no duplicate Mathlib or library statement was
   introduced. **Verdict: pass.**
4. **Pruning and route:** Removed nine proof-only imports and the corresponding direct DAG
   dependencies that the implementation does not use. The projective-line, reduction, and
   coefficient-devissage route remains inside `hasTorsionBaseChange_of_isProper`, so the
   unit route is retained. **Verdict: pass.**
5. **DAG agreement:** The node proof steps and `proof_deps` now name the declarations used
   by the Lean proof, and the proof origin records the source-library reuse. No new node or
   change record is required. **Verdict: pass.**

Changed after this reading: corrected the namespace of the existing forgetful-equivalence
instance in the DAG proof text (`AlgebraicGeometry.Etale`, not `DerivedForget`), corrected
"both new imports" to "all three new proof imports", and added this independent review.
No Lean code, statement, or definition change was needed.
