## What changed

Proved `WeilConjectures.SemilinearSections.semilinearProjectionBelowFactorization`
without changing its statement or the meaning of any existing definition. The
proof combines tensor compatibility of actual reduction with the invertible
below-level singleton evaluation mate. A private categorical lemma constructs the
required isomorphism and checks the projection equation using naturality and the
adjunction unit equation. Uniqueness of left adjoints transports the construction
to the scalar adjunction supplied in the statement.

Added `SemilinearTensorReductionCochain`, `SemilinearTensorReductionCore` and
`SemilinearSingletonEvaluationMate`, all under `Sheaf.Paper`. The first introduces
`SystemTensorReductionModels`, containing only the tensor fields of `Data`, and
proves ordinary/cochain reduction compatibility. The second proves the derived
reduction identity from those fields. These reuse the existing proved ordinary,
cochain and derived tensor-reduction arguments with the unused internal-Hom
assumptions removed. The third proves the singleton mate invertible by the actual
ordinary singleton unit square, normalized derived-mate comparison and uniqueness
of adjoints. All helper proofs are complete.

The static command-change advisory for the assigned module comes from the
private helper's explicitly closed generic section. Its variables and universes
are scoped; the existing declaration has the identical signature.

Only the assigned existing module and its node are changed. No existing shared
definition, source-library module, public import or declaration signature changes.
The original combined tensor proof was profiled after exceeding 60 seconds.
Restricting unfolding of the large tensor definitions helped elaboration but did
not suffice, so its ordinary/cochain part and its derived part are separate
modules. They compile individually within the required limit.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.SemilinearSections.semilinearProjectionBelowFactorization`
(node `lem-coef-semilinear-projection-below-factorization`).

Added zero holes. Every theorem in the three new modules is proved; there is no
`sorry` in any delivered Lean file. This closes 1 of 1 assigned holes and splits
off zero unproved statements. Existing lower library declarations are used as
provided by the stage-3 dependency contract.

## No longer needed

Removed the unused exploratory import of `SystemDerivedEvaluation` from the
new singleton module, and the unused `SystemEvaluationFlat`,
`KFlatTotalTensorModel` and source `ExactFunctor` imports from the new cochain
module. No original Lean import
was removed: the original public import of
`Sheaf.Paper.SemilinearDerivedCalculus` is retained for the unchanged statement.

The assigned node no longer directly needs
`lem-pur-derived-change-of-rings` / `OrdinaryDerivedChangeOfRings`,
`lem-pur-system-singleton-scalar-extension` / `SystemSingletonScalarExtension`, or
`lem-weil-pbc-site-derived-tensor-descent` /
`SiteDerivedTensorDescentIndependentCoefficients`. The proof does not establish a
K-flat singleton tensor representative or reassociate it directly. Instead it
uses tensor compatibility of the actual reduction and a tensor-free singleton
mate. The former node's other old proof dependencies are reached through the
new tensor/mate APIs only where needed; they are not asserted globally unused.
No source-library declaration or module is withdrawn.

The full-`Data` modules `SystemOrdinaryTensorReduction`,
`SystemCochainTensorReduction`, and `SystemTensorReductionFormula` are not imported:
the needed arguments are proved for the smaller tensor-only interface. Those
existing modules and their declarations remain available to their other users.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing derived tensor-reduction theorem has the right equation but requires
full `Data`, including the internal-Hom comparison whose construction consumes
this item. Applying it here would require precisely the comparison currently
being constructed. Its proof uses only the tensor fields, so extracting that
proof to a smaller interface removes the circular requirement.

The node's original generator calculation is valid mathematics, but it duplicates
the ordinary/cochain tensor-reduction calculation. After this calculation is
available without internal-Hom assumptions, the remaining projection
factorization is a categorical unit/naturality argument. The singleton mate uses
actual transitions and unit-normalized comparisons; invertibility of a
cartesian reduction is never assumed. Identity indices, zero rings, zero objects
and empty sites require no extra hypotheses.

## New nodes

`def-coef-semilinear-tensor-reduction-models` records the smaller tensor-only model
interface in `SemilinearTensorReductionCochain`. Its fields are parameters and
contain no data holes or arbitrary existence choices.

`lem-coef-semilinear-tensor-reduction-cochain` records the proved ordinary and
cochain tensor-reduction identity for that interface, including the actual
ordinary adjoint and its degreewise cochain map.

`lem-coef-semilinear-tensor-reduction-core` records the proved localized tensor
identity on arbitrary derived systems, using flat-term K-flat representatives
and naturality.

`lem-coef-semilinear-singleton-evaluation-mate` records the proved tensor-free
invertibility of scalar extension of the singleton unit followed by actual
reduction, for any specified left adjoints.

Each new node includes its source, full proof in words, actual Mathlib searches
and blueprint ancestry. No change record is needed: no existing interface or
statement was repaired.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
