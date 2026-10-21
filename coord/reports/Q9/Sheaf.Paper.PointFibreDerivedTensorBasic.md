## What changed

Filled `WeilConjectures.finiteFieldSpecCoefficientPrimeInvertible` in
`Sheaf.Paper.PointFibreDerivedTensorBasic`. A private proof import of
`Mathlib.Algebra.CharP.CharAndCard` supplies `charP_of_card_eq_prime_pow`.
The cardinality specified by `FiniteFieldDatum` gives characteristic `D.p` on `D.k₀`.
`CharP.cast_ne_zero_of_ne_of_prime` makes the distinct prime a unit there.
Map that unit along `algebraMap D.k₀ D.k`, the inverse global-sections isomorphism
for `Spec D.k`, and residue evaluation at each point, then use `IsUnit.invertible`.
No definitions, signatures, visibility, or existing public imports changed.
Rephrased one explanatory comment so the launcher's raw-source keyword scan
does not mistake its wording for a prohibited declaration.

The whole module compiled cleanly using `lcompile.py`; the fresh resumption
check on 2026-10-21 succeeded in 24.7 seconds (exit code 0).
An explicit `#print axioms` probe for the completed theorem reported exactly
`propext`, `Classical.choice`, and `Quot.sound`; the temporary probe was removed.
Searches used LeanFinder for prime invertibility at the geometric point,
Loogle for `charP_of_card_eq_prime_pow`, and grep for that lemma and
`cast_ne_zero_of_ne_of_prime`. The existing geometric-fibre proof in
`Sheaf.Paper.SfWeilSheafComplex` also confirms the elementary unit-mapping route;
that module is not imported.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.finiteFieldSpecCoefficientPrimeInvertible`
(owning node `def-sf-point-fibre-tensor-system`).
Zero holes remain in the item module. Zero holes added; zero split off.
The completed theorem uses no unproved library theorem.

## No longer needed

None. No imports, modules, or nodes withdrawn. Existing imports support the
module's tensor and fibre definitions; no new Sheaf dependency is needed.
The owning definition node has no proof steps or proof dependencies to prune,
and its four-stage tensor-system definitions and unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The hole's documented characteristic-and-units argument is already supported
by Mathlib. Mapping the unit directly avoids needing separate characteristic
instances for the algebraic closure and the scheme residue fields.

The initial delivery check reproduced the previous attempt's keyword-scan failure:
it matched an English word in the existing explanatory comment about the named
functors. Rephrasing that comment resolves the packet diagnostic without changing
any Lean declaration or launcher file. The current claim names Q9; no matching
rework or return entry exists.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
