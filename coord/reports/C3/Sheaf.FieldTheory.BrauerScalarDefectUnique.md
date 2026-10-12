## What changed

Proved `Field.brauerScalarDefect_unique` in
`lean/Sheaf/FieldTheory/BrauerScalarDefectUnique.lean`, keeping its original signature,
visibility, and public import. The existing three-step DAG route is implemented in Lean,
without any new public statements or new modules.

Repair of the return at head `36809eb0a`: generalized the duplicate private helper
`Field.locallyConstant_galois_eval` to
`Field.locallyConstant_integral_galois_eval (K L : Type*) [Field K] [Field L]
[Algebra K L] [Algebra.IsIntegral K L] (x : L)`. Its conclusion is local constancy
of evaluation on `L ≃ₐ[K] L` for any integral field extension, including inseparable
extensions and fields in different universes. The matrix-entry proof specializes it
to `L = SeparableClosure K`. This is a genuine generalization, not a renamed copy.
The existing helper in `Sheaf.FieldTheory.BrauerScalarDefectLifts` is private and
cannot be referenced from an importing module; no interface of that module changes.

The private helpers prove equality of matrix sizes using finrank, compare the splittings
using the already proved `Matrix.exists_unit_conj_of_algEquiv`, and show the quotient of
lifts is scalar by tensor-product induction and
`Matrix.GeneralLinearGroup.center_eq_range_scalar`. Open Galois stabilizers make the
matrix gauge locally constant, and injectivity of the positive-size scalar embedding
makes the scalar function locally constant. The gauge multiplication calculation proves
the scalar one-coboundary identity. A constructed homogeneous one-cochain then has
boundary equal to the difference of the two cycles; the kernel identification and
`HomologicalComplex.toCycles_comp_homologyπ` prove equality of their homology images.

Added proof-only imports: `WeilConjectures.Mathlib.RingTheory.MatrixAlgebra`,
`Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic`,
`Mathlib.Tactic.Group`, and
`Mathlib.Tactic.Abel`. Every added import is used.

Read the Stacks source in `etale-cohomology.tex`, labels
`section-brauer-groups`, `equation-two-cocycle`, `theorem-brauer-delta`, and
`section-continuous-group-cohomology` (Tags 03R1, 03R6, 03R7, 0DVG), and the proved
upstream matrix Skolem-Noether implementation. The scalar-defect orientation and the
homogeneous differential are exactly those of the existing declaration.

## Proved and sorry left

Closed: `Field.brauerScalarDefect_unique`
(node `lem-sc-brauer-scalar-defect-unique`), the sole original sorry.

No sorry remains in the item, and no sorry was added anywhere. This is a complete proof,
not a decomposition. All private helpers and the constructed one-cochain are proved.
The scalar function is chosen from the proved centre-of-GL result, and the conjugating
matrix is chosen from the proved upstream Skolem-Noether theorem; neither choice uses
an unproved existence theorem.

The final file compiles cleanly through `lcompile.py`. A separate axiom check reports
exactly `propext`, `Classical.choice`, and `Quot.sound` for
`Field.brauerScalarDefect_unique`. Edge cases include matrix size one, arbitrary field
characteristic, non-normalized lifts at the identity, and trivial Galois action. The generalized helper requires only integrality, not separability or normality. Zero
size is excluded by the original hypotheses and is used only to establish injectivity
of scalar matrices via their (0,0) entry.

## No longer needed

None of the baseline imports or DAG dependencies is removed. The second reader removed
the redundant added proof import `Mathlib.LinearAlgebra.Dimension.Constructions`;
its finrank facts are already available through the retained matrix-algebra import. The original public
`Sheaf.FieldTheory.BrauerScalarDefect` import remains necessary for the statement.
No new dependency containing sorry is introduced. Neither
`Sheaf.FieldTheory.GaloisUnitsHomogeneousComparison` nor
`Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent` is needed: the required
continuous one-cochain and homology calculation are proved locally from Mathlib.
The Brauer-faithfulness modules are also not used.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private separable-closure evaluation theorem
already proved in `Sheaf.FieldTheory.BrauerScalarDefectLifts`. The repair generalizes
that helper to arbitrary integral field extensions and specializes it at its use.
No existing public statement, definition, or unit route needed correction. The DAG's three original
steps are realized by proved private helpers. The apparently shorter route through
`brauerScalarDefect_eq_of_brauerEquivalent` would be circular, since that declaration
imports and applies the present uniqueness theorem. The proof uses the independently
proved matrix Skolem-Noether declaration instead.


## Second reading by C3

1. Compared the complete delivered module with the repository using `diff -u`.
   The sole existing declaration `Field.brauerScalarDefect_unique` has a byte-for-byte
   identical signature, visibility, and docstring. The original public import is kept;
   all added imports are private proof imports. No existing definition or target changed.
   Verdict: pass.
2. Read every helper and the final proof, compiled the delivered file with `lcompile.py`,
   and compiled a scratch copy with `#print axioms Field.brauerScalarDefect_unique`.
   It reports exactly `propext`, `Classical.choice`, and `Quot.sound`. There is no sorry,
   forbidden declaration, or hollow definition. `oneCochain` constructs its actual
   continuous equivariant function. Both choices of matrix and scalar use proved
   existence theorems, not unproved existence. Verdict: pass.
3. No statement is split off and no new public statement or node is introduced.
   Checked the generalized integral-extension evaluation helper against the private
   separable-closure helper in `BrauerScalarDefectLifts`: its explicit integral-extension
   hypotheses genuinely generalize that result. Reviewed size one, arbitrary
   characteristic, non-normalized identity lifts, and trivial action. Positive size
   supplies the diagonal entry for scalar injectivity; `scalar_of_same_conj` itself
   does not need positivity. Verdict: pass.
4. Searched the library for evaluation, scalar injectivity, coordinate comparison,
   and coboundary homology lemmas, and independently queried LeanFinder for continuous
   homogeneous cocycles differing by a differential. The returned abstract group
   cohomology and presheaf H1 results do not supply this continuous H2 statement.
   The upstream proved `Matrix.exists_unit_conj_of_algEquiv` is used directly.
   The analogous local helpers in other modules are private; the public homogeneous
   comparison would introduce an unnecessary larger route. Read the Stacks local
   source at `lemma-central-simple-algebra-pgln`, `equation-two-cocycle`, and
   `section-continuous-group-cohomology`: the proof respects the existing scalar-defect
   orientation and implements the degree-one differential with the correct signs.
   The unit `sk-thm-br` route is unchanged; this is a lower-level uniqueness result.
   No old proof dependency is pruned. Verdict: pass after removing a redundant import.
5. Read `lem-sc-brauer-scalar-defect-unique` and its definition dependency alongside
   the Lean code. Its three proof steps match `matrixSize_eq` and Skolem-Noether,
   `exists_locallyConstant_brauer_lift_comparison`, then `gauge_defect` and
   `homology_eq_of_coordinates_coboundary`. Its `proof_deps` retains the definition
   used when unpacking both realizations, and its source-backed agent `proof_origin`
   matches the expanded argument. No node edit is necessary. Verdict: pass.

Changed only the redundant added proof import
`Mathlib.LinearAlgebra.Dimension.Constructions` and this report. A scratch compile
without that import passed. No proof body, existing statement, definition, or DAG route
was changed. Closed one original hole; added zero holes.
