## Worker report

The module states `integralExtension_noetherianSpectrum` in
`Sheaf.TraceFormula.IntegralExtensionNoetherianSpectrum`.  It uses Mathlib's
`FractionRing A` for the fraction field `K`, `integralClosure A L` for the
integral closure `B`, `FiniteDimensional (FractionRing A) L` for finite degree,
and `NoetherianSpace (PrimeSpectrum (integralClosure A L))` for the Noetherian
Zariski space.  The scalar-tower instance
`IsScalarTower A (FractionRing A) L` renders the required composite map
`A -> K -> L`.

The hypotheses and conclusion render the node as follows.  `A : Type u` and
`L : Type v` are the commutative rings/fields in the statement.  `[CommRing A]`
and `[IsNoetherianRing A]` give a commutative Noetherian base.  `[IsDomain A]`
gives `1 != 0` and the no-zero-divisor condition.  `[Field L]` gives the field
extension target.  `[Algebra A L]`, `[Algebra (FractionRing A) L]`, and
`[IsScalarTower A (FractionRing A) L]` give the specified composite through the
fraction field.  `[FiniteDimensional (FractionRing A) L]` gives finite degree.
The object called `B` is exactly `integralClosure A L`.  The conclusion is
`NoetherianSpace (PrimeSpectrum (integralClosure A L))`, i.e. the underlying
Zariski space of `Spec B` is Noetherian.  No `Module.Finite A B` or
`IsNoetherianRing B` hypothesis is present.  The identity extension
`L = FractionRing A` is allowed by the same signature.

The declaration docstring records the postponed proof: induction on primes of
`A`; reduction to `R = A/p`; the least-degree monic relation showing the
contraction of each nonzero prime of the closure is a strictly larger prime;
finite residue-field degree and induction for each quotient spectrum; passage
from principal ideals to all proper closed subsets; and descent along the
continuous surjection on spectra of an integral inclusion.  It then applies the
argument at `p = 0` and includes the degree-one extension.

Dependency declarations used:

* `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`.
* `def-pc-field-extension`: the Mathlib field/algebra convention, using
  `Algebra` from `Mathlib.Algebra.Algebra.Defs`; the concrete field extension
  in this statement is represented by `[Field L]` and the algebra instances.
* `def-weil-pbc-integral-closure`: `integralClosure` from
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
* `def-weil-affine-spectrum`: `PrimeSpectrum` and its Zariski topology from
  Mathlib's spectrum definitions (the recorded `AlgebraicGeometry.Spec`
  declaration identifies the corresponding affine scheme).

Edge cases checked: `IsDomain A` excludes the zero ring and supplies the
fraction field; the identity extension is permitted; a degree-one extension
is covered by `FiniteDimensional`; no finiteness or Noetherian condition on
`integralClosure A L` is silently added; and the empty-spectrum cases that can
occur in closed-subspace steps are included by `NoetherianSpace`.

Searches for an existing declaration were made before writing the module.
`msearch.py leanfinder` with “integral closure of a Noetherian domain in a
finite extension of its fraction field has Noetherian spectrum” returned
`integralClosure.isNoetherianRing`, `IsIntegralClosure.isNoetherian`, and
related declarations, but each requires stronger assumptions and none states
this topological conclusion.  `msearch.py loogle` with
`integralClosure, Noetherian` returned only those stronger integral-closure
results.  `msearch.py grep` for
`integralClosure.*[Nn]oetherian|[Nn]oetherian.*integralClosure` found no matching
theorem with these hypotheses.  `rg` over `WeilConjectures` and `lean/Sheaf`
found no declaration of this node.  The existing Mathlib notions used above
were recorded as dependencies rather than redefined.

No statement dispute or node fault was found.

## Second reading by Q25

I reread the node and the module signature clause by clause.  The commutative
Noetherian domain assumptions are exactly `[CommRing A]`,
`[IsNoetherianRing A]`, and `[IsDomain A]`; the latter supplies both
nontriviality and the domain condition.  `FractionRing A` is the canonical
fraction field, and the two algebra instances plus `IsScalarTower` express
precisely the stipulated composite map into `L`.  `FiniteDimensional` is the
finite-degree condition.  `integralClosure A L` is the specified `B`, and the
conclusion is exactly Noetherianity of its prime spectrum.  The module adds no
module-finiteness or Noetherian-ring assumption on `B`, and the identity
extension remains admissible.  No mismatch was found.
