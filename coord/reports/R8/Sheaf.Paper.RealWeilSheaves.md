## What changed

Filled both proofs in `Sheaf.Paper.RealWeilSheaves`, preserving every public statement
and definition. The every-basis comparison uses the existing continuous-linear-coefficient
API and lifts finite index types to the vector-space universe. Proved private helpers
show that algebraic embeddings preserve and reflect spectral continuity, transport the existing
compact matrix-descent theorem to an arbitrary algebraic closure, and apply stable-lattice
existence to continuous matrices over a generic finite coefficient field.

For the finite-model criterion, choose a finite basis, descend the geometric matrices,
adjoin the entries of the degree-one matrix and its inverse, and construct the entire
Weil representation over that finite field. The degree equation shows every group element
is a geometric element times an integer power of the lift. The isometric coefficient embedding
reflects continuity. The existing stable-lattice theorem supplies a full free lattice of the
right rank. The converse expands arbitrary linear coefficients in the chosen finite basis.

## Proved and sorry left

Holes closed: `AlgebraicGeometry.WeilGroup.isLisse_iff_everyBasis` and
`AlgebraicGeometry.WeilGroup.isLisse_iff_finiteModel` (2 of 2).
Holes added: none. Remaining holes in the item: none. No split-off statements.
The finite-model proof uses the existing `Padic.exists_stable_lattice`, whose own
named dependencies remain the responsibility of their assigned items.

Validation: `lcompile.py` compiled both completed proofs in 14.7 seconds. Three redundant
`change` tactics reported by the unused-tactic linter were then removed; the delivery command
repeats compilation, axiom checks, and server preflight for the final packet.

## No longer needed

Removed four unused private imports:
`Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath`,
`Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`,
`Sheaf.Paper.FibreFunctorBasepointTransport`, and
`Sheaf.FieldTheory.FiniteFieldAbsoluteGalois`.
The proof takes compactness and the degree-one lift from the existing Weil-group structure;
it does not construct the arithmetic exact sequence or local Frobenius anew. No module is
withdrawn, and all adopted source declarations remain intact. The item remains needed by
its existing DAG parents, including `prop-wf-weil-sheaf-representation-equivalence`.

The following modules leave this item's import closure (read from the current Lean imports):

- `Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticExactSequence`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport`
- `Sheaf.FieldTheory.FiniteFieldAbsoluteGalois`
- `Sheaf.Paper.AdicFibrePathExtension`
- `Sheaf.Paper.AlgebraicFibrePathConstruction`
- `Sheaf.Paper.CoefficientFibreComparisonNaturality`
- `Sheaf.Paper.FibreFunctorBasepointTransport`
- `Sheaf.Paper.FibreFunctorBasepointTransportData`
- `Sheaf.Paper.FibreFunctorLinearTransport`
- `Sheaf.Paper.IntegralFibrePathConstruction`
- `Sheaf.Paper.IntegralFibreScalarComparison`
- `Sheaf.Paper.LocalizedFibrePathTransport`
- `Sheaf.Paper.RationalFibrePathConstruction`
- `Sheaf.Paper.RationalFibrePathScalarSquare`
- `Sheaf.Paper.RationalFibreScalarComparison`
- `WeilConjectures.AlgebraicGeometry.GaloisPointGeometricComparison`
- `WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit`
- `WeilConjectures.AlgebraicGeometry.Sites.GaloisModule`
- `WeilConjectures.CategoryTheory.Sites.Point.DiscreteModule`
- `WeilConjectures.CategoryTheory.Sites.Point.GroupAction`
- `WeilConjectures.Mathlib.FieldTheory.KrullTopology`
- `WeilConjectures.RepresentationTheory.DiscreteModule.Basic`
- `WeilConjectures.RepresentationTheory.DiscreteModule.CohomologicalDimension`
- `WeilConjectures.RepresentationTheory.DiscreteModule.Induction`
- `WeilConjectures.RepresentationTheory.DiscreteModule.Sylow`
- `WeilConjectures.RepresentationTheory.DiscreteModule.Transport`

The modules leaving the current targets' import closure are: none; this item is not yet
imported from `TargetsCheck`, so no global pruning claim is made.
This is an import reduction; the pinned sorry ledger remains the authority for project progress.
The finite-model argument follows existing steps 2–3 of `sk-d-real-weil`, using compact
matrix descent and stable-lattice existence.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The proof explicitly selects the spectral topology
on the intermediate field, avoiding competition with the inherited subtype topology during
typeclass inference. Their agreement follows from the proved isometry and continuity lemmas.
Compactness of `W.geometric` is already a field
of the existing Weil-group structure, so this proof does not reconstruct fundamental groups.
Lecture 19, Proposition 1.1.9 and the finite-field enlargement argument on pp. 4–5 were read.
The empty finite basis is permitted throughout. No stability under the degree-one lift is
assumed or concluded; in particular a rank-one nonunit Frobenius is allowed.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
