## What changed

Split the existing normalized path prefix, unchanged, into EtaleAdicPathData and
reexport it publicly from the item, so the two compatibility lemmas can have
independent modules without import cycles. Added the proved composition wrapper.
Prove etaleFundamentalRep_exists using the existing DegreeDatum.lift and eq_lift,
after deriving the Frobenius conjugation relation from path naturality and pullback.
Prove lift change by the same path square and uniqueness. Prove basepoint change
on the geometric kernel and degree-one element, then use the subgroup of elements
intertwined by the given linear map and the degree decomposition.
The original etaleFundamentalRep_isLAdic hole stays in place. No statement is changed.
Change record: coord/changes/T2-etale-adic-path-interface.md.
Validation: lcompile.py --all compiled all four sandbox modules without errors
or warnings (result 2830dd5af03f4b5dff07fb81).

## Proved and sorry left

Original holes: 4. Three original holes are closed in the item:
AlgebraicGeometry.Scheme.etaleFundamentalRep_exists,
AlgebraicGeometry.Scheme.etaleFundamentalRep_liftChange, and
AlgebraicGeometry.Scheme.etaleFundamentalRep_changeBasePoint.
AlgebraicGeometry.Scheme.etaleFundamentalRep_isLAdic remains unchanged
(node def-wf-fundamental-representation).
The closure is a decomposition through smaller path-compatibility statements,
not a claim that all underlying sheaf theory is proved.

New holes:
AlgebraicGeometry.Scheme.etaleAlgebraicPath_naturality
(node new-t2-etale-adic-path-naturality), and
AlgebraicGeometry.Scheme.etaleAlgebraicPath_pullback
(node new-t2-etale-adic-path-pullback).
Each statement is strictly a part of the argument: neither mentions a Weil
representation, a degree datum, or an extension theorem. Their docstrings give the finite-germ, inverse-limit and coefficient-extension
arguments needed to identify the normalized paths.

## No longer needed

No mathematical module is withdrawn. The original direct imports of
LisseAdicAutomorphismPullback, LisseAdicFiberFunctors, LAdic,
WeilFundamentalRepresentation, IntegralFibrePathConstruction,
FibreFunctorLinearTransport, and StalkTransport are relocated to EtaleAdicPathData;
they remain needed by the verbatim path construction, and the old public imports
remain publicly reexported. No dependency in the original two-step DAG proof is
pruned: both existing E5 interfaces remain used by the relocated prefix.
No pro-etale representation or monodromy comparison is used to prove the etale
extension. The upstream abstract DegreeDatum construction is sufficient.

## Where the brief, the DAG or earlier work was wrong

The previous DAG proof described only the already closed path-construction prefix,
not the four remaining extension obligations. The updated proof records the two
actual sheaf compatibility squares and the full algebraic combination for existence,
lift change and basepoint change. The abstract extension node in the imported DAG
cites def-wf-fundamental-representation, so using that node from the item would
create a metadata cycle. The new generic group-only attachment records the already
proved upstream group theorem independently; it introduces no new group proof hole.
The newest blueprint uses pro-etale locally free objects, while the assigned module
and its reviewed consumers use the etale adic interface. This delivery preserves the
reviewed etale statements and makes no new comparison claim or target change.

## New nodes

new-t2-etale-adic-path-data records the relocated, proved finite and adic paths,
the geometric representation and fibre maps, plus the composition wrapper.

new-t2-etale-adic-path-naturality records naturality of the actual normalized paths
for every algebraic coefficient morphism, independently of Weil descent or groups.

new-t2-etale-adic-path-pullback records the specified automorphism pullback square
for arbitrary finite-fibre paths and the same recorded coefficient-stage comparisons.

new-t2-degree-kernel-extension records the existing proved group-only lift, kernel
formula, degree-one formula and uniqueness, without the parent-node dependency of
the blueprint's specialized Weil statement.

Small-case checks: all equations remain valid for rank zero, identity paths,
identity automorphisms and identity morphisms. The lift-change convention gives
T' = rho_geom(a) T; the basepoint convention gives transport followed by the action
at the new point. No Frobenius-stable integral lattice is assumed.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
