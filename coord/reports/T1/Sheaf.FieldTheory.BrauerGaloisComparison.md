## What changed

Replaced the sorry in `Field.nonempty_equiv_brauerGroup_galoisUnitsH2` by a compiling
quotient construction. The target signature, universes, definitions, and public imports
are unchanged. Added proof imports of `WeilConjectures.Algebra.Central.ReducedNorm` and
three new statement modules. The second reading removed the redundant TensorProduct.Basic
import from the new scalar-defect definition module. The proved upstream separable-closure splitting theorem
supplies a positive matrix splitting. The remaining matrix-lift theorem supplies an
actual continuous homogeneous cycle. Its homology image is unique by faithfulness.
Lean then descends this unique-class function through Brauer equivalence, proves
injectivity by quotient induction, proves surjectivity using crossed-product
realization, and builds the equivalence with `Equiv.ofBijective`.

Added the concrete, sorry-free module `Sheaf.FieldTheory.BrauerScalarDefect`, defining
`Field.galoisUnitsCocycleValue` by evaluation of Mathlib's cycles inclusion and the
relation `Field.HasBrauerScalarDefect` by a matrix splitting, locally constant matrix
lifts, an actual homogeneous cycle, and explicit conjugation and scalar-defect equations.
No object is defined by choosing a witness from an unproved mere existence theorem.
The class chosen in the main proof is determined uniquely, using the faithful relation.

Updated the parent node's proof, proof dependencies, and proof origin to follow the
Lean construction. The unit `sk-thm-br` and its route through field Brauer vanishing
are unchanged. Its realized lists contain no nodes at this comparison level.

Validation: all five sandbox modules compile in import order using `lcompile.py`.
The final delivery dry run performs the static and axiom checks as well.

## Proved and sorry left

Closed the one original hole:
`Field.nonempty_equiv_brauerGroup_galoisUnitsH2`
(node `lem-sc-brauer-galois-units-comparison`). Its proof is complete in Lean **from
three new intermediate statements**, so this is a decomposition, not an unconditional
Brauer/Galois comparison proof. One hole closed and three holes added gives net -2 holes.

Every remaining sorry in the delivery is exactly `:= by sorry` in a named public theorem:

- `Field.exists_brauerScalarDefect_lifts`, module
  `Sheaf.FieldTheory.BrauerScalarDefectExists`, node
  `lem-sc-brauer-scalar-defect-exists`: construct locally constant matrix lifts and a
  homogeneous scalar-defect cycle for an already supplied splitting.
- `Field.brauerScalarDefect_eq_iff`, module
  `Sheaf.FieldTheory.BrauerScalarDefectFaithful`, node
  `lem-sc-brauer-scalar-defect-faithful`: independence of choices, matrix-amplification
  invariance, and faithfulness via matrix Hilbert 90.
- `Field.exists_csa_brauerScalarDefect`, module
  `Sheaf.FieldTheory.BrauerScalarDefectSurjective`, node
  `lem-sc-brauer-scalar-defect-surjective`: crossed-product realization of a continuous
  degree-two class.

Each is a strictly specified part of the original argument; none asserts an equivalence
between the whole Brauer quotient and cohomology. Each has the source, proof in words,
and its own node. There are no sorries in the definitions or main comparison module.

## No longer needed

Removed the redundant `Mathlib.RingTheory.TensorProduct.Basic` import from the new
`Sheaf.FieldTheory.BrauerScalarDefect` module; its tensor-product notation and declarations
are already available through the remaining imports. Both original public imports of
the comparison remain needed for its statement. There were no old proof imports or
old proof-dependency nodes to prune. The Galois cohomology definition node remains needed transitively by
all three new statements and the concrete relation. The original three mathematical
steps are retained; the separable-closure splitting part is discharged by the existing
proved upstream theorem rather than restated as a new hole. No unit step is bypassed,
and no existing node or module is claimed to have become globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original node's three substantial proof steps had no stated proof dependencies
apart from the cohomology definition. Thus its plan could not be instantiated merely
by importing existing step declarations. Searches by LeanFinder, Loogle, and ripgrep
found no degree-two Brauer comparison, scalar-defect construction, faithfulness theorem,
or crossed-product realization. LeanSearch was unavailable (Internal Server Error).
The upstream `ReducedNorm` module does prove matrix splitting over the separable closure
and pointwise inner conjugacy; the former is now used directly. Pointwise inner conjugacy
alone does not supply locally constant lifts or their homogeneous cycle, so that gap
remains explicitly in the first new theorem.

Read Stacks Tags 03R6, 03R7 and 0DVG. Checked the cochain convention against Mathlib's
continuous homogeneous complex: a degree-two cycle includes into invariant iterated
continuous maps, and its evaluation is at `(1,g,g*h)`. Checked that TopModuleCat homology
uses the algebraic kernel and image quotient, rather than a Hausdorff completion.

Edge cases: positive n is essential because zero-sized matrices cannot split a nonzero
central simple algebra. For a split algebra the standard splitting, constant identity
lifts, and zero additive homogeneous cycle satisfy the displayed equations and represent
zero. Repeating A in the faithfulness lemma gives uniqueness by reflexivity of Brauer
equivalence. Changing lifts by scalar units changes only a coboundary. No assumption of
perfectness, characteristic zero, algebraic closedness, or a finite absolute Galois group
was added. Matrix lifts use the separable closure, so imperfect fields remain covered.
The conjugation convention is `g(M)=b_g⁻¹ M b_g`; composing it yields exactly the order
`b_g*g(b_h)` in the scalar-defect equation. The possible inverse convention for crossed
products is addressed by choosing the opposite algebra when necessary, not by changing
the class to be realized.

The parent node's pre-existing created.item is a module name rather than a node id, so
`blueprint_refs.py ancestor` reports None. New nodes retain the explicit nearest
blueprint ancestor already recorded on the parent, `lem-sc-brauer-zero`, and name this
comparison in their `via` chain.

## New nodes

`def-sc-brauer-scalar-defect` defines the explicit realization relation and homogeneous
cycle evaluation, in `Sheaf.FieldTheory.BrauerScalarDefect`. Its definitions contain no
sorry and introduce no new cohomology model.

`lem-sc-brauer-scalar-defect-exists` states the matrix-lift construction for a specified
positive splitting, in `Sheaf.FieldTheory.BrauerScalarDefectExists`. The splitting itself
is provided by the proved upstream theorem in the main module.

`lem-sc-brauer-scalar-defect-faithful` states independence and faithfulness of the explicit
relation, in `Sheaf.FieldTheory.BrauerScalarDefectFaithful`. This provides both unique
class selection and descent/injectivity on the quotient.

`lem-sc-brauer-scalar-defect-surjective` states crossed-product realization of any class,
in `Sheaf.FieldTheory.BrauerScalarDefectSurjective`. This is used for surjectivity of the
quotient map. All new nodes inherit the parent's chapter and unit. No definition or
existing statement was changed, so no change record is required.


## Second reading by T1

1. **Visible declarations unchanged: PASS.** Diffed the sole existing delivered module,
   `BrauerGaloisComparison`, against the repository. Its entire original declaration
   header, universes, docstring, and two public imports are byte-for-byte unchanged;
   only its proof and four plain proof imports were added. The other four modules are
   new. No existing definition or target statement changes, and no change record is
   needed. The existing parent node differs only in `proof`, `proof_deps`, and
   `proof_origin`.

2. **Kernel and holes: PASS as a decomposition.** Independently compiled all five
   modules in import order with `lcompile.py`. Added explicit `#print axioms` commands
   for all six delivered declarations to a temporary copy and compiled it through
   the same launcher, then removed the copy. `HasBrauerScalarDefect` and
   `galoisUnitsCocycleValue` use only `propext`, `Classical.choice`, and `Quot.sound`.
   The comparison and the three named open theorems additionally use `sorryAx`.
   The only three sorries are the listed public theorems, each with body `by sorry`;
   there are no forbidden trust declarations or hollow definitions. The local
   chosen value in the main proof comes from `uniqueClass : ∃! x, R(A,x)`; choosing
   the crossed-product algebra occurs only in a proposition proof.

3. **Split statements: PASS.** Read Stacks Tags [03R6](https://stacks.math.columbia.edu/tag/03R6),
   [03R7](https://stacks.math.columbia.edu/tag/03R7), and
   [0DVG](https://stacks.math.columbia.edu/tag/0DVG), together with Mathlib's
   `ContCohomology.Basic`, `Continuous.Basic` coinduced action and differential, and
   `ModuleCat.Topology.Homology`. The latter really uses the algebraic image, not its
   closure. Invariant homogeneous cochains evaluate at `(1,g,g*h)` to the stated
   inhomogeneous cocycle. The three statements separately supply lifts for a given
   splitting, independence/faithfulness for given realizations, and realization of
   a given class. None is the original equivalence under a new name. Their hypotheses
   include precisely a field, finite-dimensional central simple algebras, and (for
   lifts) a positive splitting size; no perfection or characteristic restriction.
   Tested the split-algebra/zero-class case with identity lifts and zero additive
   cocycle, the reflexive A=B case giving uniqueness, and the excluded n=0 case.
   Composing g(M)=b_g⁻¹ M b_g with h gives conjugation by b_g*g(b_h), so the
   defect order is consistent. Arbitrary separable-closure splittings use only
   finitely many coefficients of a K-basis and hence descend to a finite Galois
   extension. The finite quotient permits locally constant lifts. Tensoring with
   the opposite algebra cancels equal classes for faithfulness; crossed products
   realize either convention by taking the opposite algebra if necessary.
   Each open theorem has its source and proof in words and a matching node.
   Independently searched LeanFinder with "projective semilinear descent central
   simple algebra second cohomology continuous crossed products", Loogle with
   `IsBrauerEquivalent`, and ripgrep with crossed-product/factor-set/Schur-multiplier
   and Brauer/cohomology terms across Mathlib and both source roots. These found
   Brauer definitions and degree-one Hilbert 90, but no theorem closing one of these
   three degree-two statements. No split theorem can be closed in a short repair.

4. **Route and pruning: PASS after import repair.** Read the upstream positive-size
   matrix-splitting theorem in `ReducedNorm`, then followed unique-class construction,
   quotient descent, representative induction for injectivity, and crossed-product
   surjectivity in the actual proof. This uses an already proved splitting result
   rather than adding a fourth hole. Each remaining main-module proof import is used.
   All imports of the three statement modules are public because their signatures
   use the scalar-defect relation. Removed the redundant TensorProduct.Basic import
   from the new definition module after a successful compile without it. No node
   from the parent's old `proof_deps` was dropped: the cohomology definition remains
   needed transitively. `dag/units/sk-thm-br.json` has empty realized statement and
   step lists at this level; its field-vanishing route is preserved.

5. **DAG agreement: PASS.** Checked every new node's statement against its Lean
   signature, including the explicit realization equations and cocycle evaluation.
   The parent proof uses the three new lemmas and the upstream splitting declaration
   recorded on `lem-sc-c1-brauer-trivial`; its proof-dependency list is their union.
   New nodes have source, proof plan, search records (including the unavailable
   LeanSearch service), creation, blueprint ancestry, chapter/unit, and Lean records.
   The definition node has empty proof and proof dependencies. The concrete relation
   contains real data and no chosen unproved existence witness. The mathematical
   plans of the open lemmas remain plans, not claimed Lean proofs.

Changed in this second reading: removed one redundant import and corrected the report's
pruning account; no proof, statement, definition body, node, or hole count was changed.
One of one original holes is closed conditionally, three are split off, net minus two.
