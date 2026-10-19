## What changed

Proved AlgebraicGeometry.Scheme.finiteCoefficient_tensor_ctf in
Sheaf.Paper.FiniteCoefficientTensorCtf, preserving its entire signature and public imports.
Retained and checked the earlier sandbox proof against current sources, removed its linter
warning and an unused import, and expressed both tensor bounds through existing DAG-attached
source lemmas. The proof locally compares the recorded K-flat tensor and Tor-amplitude
predicates with categorical derived tensor and torAmplitudeIn. It proves residue-field
invertibility of l from the finite-field datum, boundedness from the generic tensor bounds,
constructibility from finiteTensor_constructible_cohomology, and the summed Tor interval
by applying the bounds to M tensor F[0] and using associativity.

Proof-only imports added: Sheaf.Algebra.Homology.KFlatResolutionGeneral (import all, to use
its proved private categorical structures),
WeilConjectures.CategoryTheory.DerivedCategory.FlatModel, and
Mathlib.Algebra.CharP.CharAndCard. The private structures are used only in a theorem proof;
no definition or public signature exposes them. All instantiated site universes remain
independent as in the original statement. The existing node proof and proof_deps now
record this route. No definition, statement, or consumer changes; no change record needed.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.Scheme.finiteCoefficient_tensor_ctf (lem-sf-tensor-ctf).
Zero holes left in the item; zero holes added; zero split off. The proof uses existing
library declarations, including the separately proved constructible-cohomology theorem.
The file compiles through lcompile.py without diagnostics. Empty cohomological support
and zero inputs need no exceptional assumptions: finite sets supply bounds even when empty,
and the proof transports vanishing through actual isomorphisms. Ordered Tor endpoints
are retained and added via add_le_add.

## No longer needed

Removed the following proof-plan imports:

- Sheaf.Paper.FiniteCoefficientFlatModel (lem-sf-flat-model): its finite-coefficient
  wrapper and etale constructible variants are unnecessary; the generic source tensor
  bounds already use bounded flat models in the actual ringed-site module category.
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
  (lem-pc-bounded-above-flat-kflat-site): generic categorical bounds supply their own
  K-flatness, while the supplied P is already acyclic-tensor K-flat.
- Mathlib.Algebra.Homology.BifunctorShift (def-pc-tensor-complex-sheaves): no direct
  unfolding of tensor totalization is needed; it remains available through derivedTensor.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite (def-pc-flat-sheaf-modules): no
  site-flatness conversion or termwise finite-sum flatness calculation is needed here.
- Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
  (def-weil-finite-torsion-constructibility): still used, already publicly imported by
  FiniteTorAmplitude; only its redundant direct import was removed.
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
  (def-weil-derived-tensor): its fixed-ring ModuleCat-sheaf presentation is unnecessary;
  the statement uses the intrinsic Scheme.derivedTensor, whose public import stays.
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution
  (lem-weil-derived-tensor-functorial): replaced by the generic source K-flat comparison
  directly on the intrinsic constant-ring module category.

Also removed the retained attempt's unused Mathlib.Algebra.CharP.Invertible import.
Obsolete top-level tool_uses entries lem-pc-bounded-above-flat-kflat-site and
lem-sf-flat-model were removed; the constructible-cohomology approval is retained.
The unit's realized statement/steps are empty and its route is unchanged. These are
removals from this item's direct proof route, not claims that the corresponding modules
are globally unreachable: generic source bounds still use bounded flat models internally.

## Where the brief, the DAG or earlier work was wrong

The old plan expands flat-model and tensor-totalization calculations already proved
in the source library. Its fixed-ring tensor proof dependencies do not use this item's
intrinsic SheafOfModules encoding. The local K-flat comparison gives the required exact
identification without changing either encoding or any definition. The current blueprint
statement agrees with the original signature, and no mathematical correction is needed.
The retained sandbox had a complete proof but lacked its report and updated DAG record;
this delivery supplies them. There is no second worker or delegated review in this session.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
