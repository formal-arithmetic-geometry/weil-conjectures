## Worker report

The module `Sheaf.TraceFormula.GenericFibreClosedChain` states
`AlgebraicGeometry.exists_generic_fibre_closed_chain`.  It also defines the two
canonical ring maps needed to make the field extensions explicit:
`AlgebraicGeometry.functionFieldBaseRingHom` from `K` to `X.functionField`, and
`AlgebraicGeometry.residueFieldBaseRingHom` from `K` to `X.residueField x`
(the latter was replaced at maintainer review by the project's existing
`Scheme.Hom.residueFieldAlgebraMap`; see the last section).
Their data is the composite of the inverse of `Scheme.ΓSpecIso`, the structural
map, and respectively the generic-point germ or the residue map; neither is a
choice from an existence theorem.  The theorem proof is exactly `sorry`.

The node hypotheses and clauses render as follows.

- “`K` is a field” is `{K : Type u} [Field K]`.
- “`X` is a nonempty integral scheme” is `{X : Scheme.{u}} [IsIntegral X]`;
  `IsIntegral.nonempty` supplies the required nonemptiness.
- “`X` is locally of finite type over `K`” is
  `[X.Over (Spec (.of K))]` together with
  `[LocallyOfFiniteType (X ↘ Spec (.of K))]`.
- The function field at the generic point is Mathlib's `X.functionField`, and
  its structural `K`-algebra is the map
  `functionFieldBaseRingHom`.  The finite natural number `r` and its meaning
  are the first existential clause:
  `@Algebra.trdeg K X.functionField _ _
  ((functionFieldBaseRingHom (K := K) (X := X)).toAlgebra) = (r : Cardinal)`.
  This expresses the finite transcendence degree required by the chain in the
  source.
- The closed endpoint is `x : X` with
  `x ∈ closedPoints (X : Type u)`, Mathlib's singleton-closed predicate.
- The chain is `ξ : Fin (r + 1) → X`.  Index `0` is
  `genericPoint X`, and `Fin.last r` is `x`.  For every `i : Fin r`,
  `ξ i.castSucc ⤳ ξ i.succ` is the specialization clause
  `ξ_i ∈ closure {ξ_{i-1}}`, and the adjacent inequality is the required
  distinctness clause.  The `Fin` indexing includes the case `r = 0`.
- “`κ(x)` is finite over `K`” is
  `@Module.Finite K (X.residueField x) _ _
  (residueFieldBaseRingHom (K := K) (X := X) x).toAlgebra.toModule`, using
  Mathlib's `Scheme.residueField`.

The statement dependencies read and used are the recorded Mathlib notions:
`Field`; `AlgebraicGeometry.IsIntegral`; `AlgebraicGeometry.LocallyOfFiniteType`;
`IsGenericPoint`/`genericPoint`; `Scheme.functionField` (the stalk at the generic
point); `TopCat.Presheaf.stalk` for that stalk; `closedPoints`; `Algebra.trdeg`;
and `Scheme.residueField`.  The proof-plan imports are retained for the stated
proof dependencies: `Sheaf.AlgebraicGeometry.ClosedPointField`,
`Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`,
`WeilConjectures.Topology.PresheafModuleStalkFunctor`, and
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`; Mathlib proof leaves are
public imports in the module.

Edge cases checked before writing: `r = 0` (for a zero-dimensional integral
scheme the two endpoint indices coincide); `Spec E` for a finite field
extension `E/K`; affine space over `K`, where the chain has the expected
length; arbitrary characteristic; and non-separated or non-quasi-compact
schemes, since only one affine chart is used in the source argument.  The
empty scheme is correctly excluded by `IsIntegral`.  No quasi-compactness,
separatedness, smoothness, or algebraic-closedness hypothesis was added.  The
orientation `⤳` was checked against
`specializes_iff_mem_closure`: the first index is generic and each next index
lies in the closure of the preceding one.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder "closed point of an integral locally finite type
  scheme over a field with a specialization chain from generic point of length
  transcendence degree"`: eight hits (generic-point, Jacobson, and closed-point
  ingredients), but no chain theorem.
- `msearch.py ... loogle "genericPoint, Specializes, Algebra.trdeg,
  closedPoints"`: zero hits.
- `msearch.py ... grep "genericPoint.*Specializes|Specializes.*genericPoint|
  closedPoints.*trdeg" AlgebraicGeometry`: four ingredient hits in Mathlib
  (`genericPoint`, `genericPoint_specializes`, and `FunctionField`), no exact
  statement.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for the theorem name and
  generic-fibre/closed-chain phrases, and `grep -rl` for the blueprint id:
  no duplicate declaration or module.
- The dependency declarations and their full signatures were read in their
  recorded Mathlib/source modules.  No new definition node or dependency-module
  repair was needed.

## Second reading by N8

I reopened the node and the completed module.  The field, integral/nonempty,
and locally-finite-type hypotheses occur exactly once and use the structure
morphism over `Spec K`.  The existential natural `r` is tied by an equality to
the cardinal transcendence degree, so the indexing cannot silently choose a
smaller length.  The `Fin (r+1)` family has exactly `r+1` points; `0` and
`Fin.last r` render the generic and closed endpoints, and every adjacent pair
has both the closure specialization and inequality required by the node.  The
final `Module.Finite` clause uses the canonical residue-field structural map
and no arbitrary algebra structure.  The helpers are real canonical composites
and do not alter the theorem's hypotheses.  The module compiled cleanly with
`scompile.py`; no statement mismatch, extra clause, or omitted edge case was
found.

## Maintainer review fix (NT-cc second reader, 2026-10-18)

One definition per notion (H4): the delivered helper `residueFieldBaseRingHom`
duplicated the project's canonical `K`-algebra structure on residue fields,
`AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap`
(`WeilConjectures/ZetaSeries.lean:224`), which the proof dependency
`lem-kun-closed-point-field` (`closedPoint_iff_residueField_trdeg_zero_and_finite`)
and the sibling modules `FiniteTypeResidueTrdeg` and `ClosedIrreducibleDimensionTrdeg`
use.  The helper was removed and the final clause now reads
`@Module.Finite K (X.residueField x) _ _
((X ↘ Spec (.of K)).residueFieldAlgebraMap x).toAlgebra.toModule`, with
`public import WeilConjectures.ZetaSeries` (already a public import of
`Sheaf.AlgebraicGeometry.ClosedPointField`).  Step 2 of the proof can now apply
lem-kun-closed-point-field(a) on the chart without a bridge between two algebra
structures.  Nothing else changed; the fixed module compiles cleanly with
`nt_compile.py`.
