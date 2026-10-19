## Worker report

Retained the interrupted packet: `Sheaf.Paper.GlobalGeometricFrobenius` defines
`WeilConjectures.globalGeometricFrobenius` and
`WeilConjectures.globalGeometricFrobeniusOnCohomology`. Both definitions have real data;
there is no theorem, axiom, or sorry in this module. The node changes only in `lean`.

Source checked: the node's recorded master definition, order 2061, and the current
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-weil-global-geometric-frobenius.md`,
order 2405. The current source gives the same two composites. The DAG additionally
names their already recorded transport and isomorphism dependencies.

Hypothesis and clause correspondence:

- The tuple p,a,q,k₀,k is `(D : FiniteFieldDatum.{u})`. Its fields include primality,
  positive exponent, q=p^a, cardinality of k₀, and the specified algebraic closure k.
- A prime l different from p, Q_l and its chosen closure are `(c : D.CoefficientDatum)`:
  `c.l`, its `Fact c.l.Prime`, `c.different`, and `c.Qbar` with its algebraic-closure
  structure. `(E : Padic.FiniteCoefficientFields c.l c.Qbar)` is exactly a finite
  intermediate extension contained in this closure; `E.val` is its coefficient field.
- The separated finite-type k₀-scheme is `Y₀ : Over (Spec (.of D.k₀))`, with
  `[LocallyOfFiniteType Y₀.hom]`, `[QuasiCompact Y₀.hom]`, and `[IsSeparated Y₀.hom]`.
  Locally finite type plus quasi-compact is the recorded finite-type convention.
- Y is the dependency's `D.geometricFiber Y₀`. The pullback in the fixed-pair type is
  along `(D.geometricFrobenius Y₀).hom`, which is id × Spec(geometric Frobenius),
  rather than the absolute power map or a k-linear substitute.
- `(K : sfWeilComplex D c.l c.different Y₀ E.val)` is precisely the fixed-pair category
  of bounded constructible E-complexes under derived Frobenius pullback. `K.carrier`
  is For(K), and `K.str.hom` is theta_K : Lg_Y^*For(K) → For(K), the hom of its iso.
- The first component of `globalGeometricFrobenius` is
  `(frobeniusCohomologyTransportRational ... K.carrier).1 ≫
  (frobeniusCohomologyRationalFunctor ... false).map K.str.hom`.
  These are exactly tau_For(K) and RΓ(theta_K), in the displayed source order.
  Its declared type is `End` of that ordinary coefficient complex.
- The second component uses `.2` and `true`, so it is tau_c,For(K) followed by
  RΓ_c(theta_K), with `End` of the compact coefficient complex as declared type.
  The functor's definition composes the compact-support direct image model with
  `pointRationalFibre`, which is the specified Fib_s at s=Spec k.
- `(c₀ : Compactification Y₀.hom)` retains the compactification presentation already
  required by the transport interface. It selects the recorded R a_! construction;
  it does not impose properness on Y₀ or supply an arbitrary functor/comparison.
  All compactification choices are accepted, including a nonproper Y₀.
- The first arrows are the existing canonical point/exchange transports, not supplied
  parameters. Their isomorphism assertion is the rational clause (last conjunct) of
  `frobeniusCohomologyTransport_isIso`; that dependency is publicly imported.
- The maps denoted F in every degree are
  `globalGeometricFrobeniusOnCohomology ... (i : ℤ)`, which applies
  `(DerivedCategory.coefficientFdCohomology E.val i).map` to both endomorphisms.
  Thus this includes negative and zero degrees and uses precisely H^i(F).

Dependency declarations read and reused (available through the two public imports):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, its `CoefficientDatum` and
  `geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius` (its field automorphism is the inverse of
  arithmetic Frobenius). The morphism-properties node is a convention collector;
  its finite-type and separated instances are the existing Mathlib properties.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilFrobeniusPullback`,
  `sfWeilForget`; the latter forgets exactly to `K.carrier`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`, used inside
  the recorded Frobenius pullback; no second pullback is defined.
- `Sheaf.Paper.CommonStageCompactWeilCohomology` publicly retains the ordinary,
  compact, and rational coefficient-complex interfaces used by the transport.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`, and the existing
  `DerivedCategory.coefficientFdCohomology` used in the transport's degree maps.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `Scheme.sfIntrinsicCompactSupport`,
  the fixed-compactification finite-level compact-support construction underlying
  its integral/rational model.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`:
  `frobeniusTransportRational`, `frobeniusCohomologyTransportRational`,
  `frobeniusCohomologyDirectModel`, `frobeniusCohomologyCompactModel`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`:
  `frobeniusCohomologyRationalFunctor`, and the rational clause of
  `frobeniusCohomologyTransport_isIso`. The functor's full definition was also
  checked using `scompile.py --source`; it is the actual model RΓ/RΓ_c followed
  by the point fibre, with no new comparison choice.

Edge cases checked by reading the constructions: the empty scheme and zero complex
are allowed; no nonempty, smooth, proper, connected, or positive-dimensional
hypothesis is added. There is no constraint on i beyond i : ℤ, and no assumption
that the finite extension is nontrivial. The datum permits every prime p, exponent
a≥1, and coefficient prime l≠p. The universe u is explicit and all variable names
are bound; both autoImplicit options are false.

Existing-definition searches retained in `searches.jsonl`:

- LeanFinder, “geometric Frobenius endomorphism on cohomology of a Weil complex
  transport composed with the Weil structure”: eight isocrystal/Witt-vector hits,
  no sheaf-cohomology operator.
- Loogle, “WeilComplex, Frobenius, cohomology”: no hits (unknown WeilComplex).
- Mathlib grep, “globalGeometricFrobenius|frobenius.*[Cc]ohomology|WeilComplex”:
  no hits.
- LeanSearch, “geometric Frobenius action on ordinary and compactly supported
  cohomology of a Weil complex”: eight ring/Witt-vector/Frobenius hits, no match.
- Direct rg of “globalGeometricFrobenius|def-weil-global-geometric-frobenius” in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared `lean/Sheaf`:
  no existing declaration. The saved searches concern components; those components
  are reused, while this module only composes them with the fixed Weil structure.

No statement dispute or source correction was needed. No new node or dependency
module was introduced.


## Second reading by NZ

Self-check on repair (the dispatcher explicitly forbids starting another agent;
the maintainer supplies the independent review). Reopened the node and the retained
module. The fixed-pair carrier and theta have the source orientation; ordinary
`false` and compact `true` select the two source functors. In each component the
canonical transport precedes the functorial image of theta. The degree clause
applies the same cohomology functor in every integer degree to these components.
All binders, constructions, signatures, and docstrings are retained from the
independently reviewed delivery.

## Returned-delivery repair

Addressed the H13/H4 return on immutable head `73c626f9071a`:
removed `lean/Sheaf/A/FrobeniusCohomologyTransportIso.lean` and the dependency node
copy `dag/nodes/sec-six-functors/lem-weil-frobenius-cohomology-transport-iso.json`.
The item's first import is now exactly
`public import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`; no other line of
the item module changed. NW's landed dependency record and its 32 declarations
remain owned by the canonical module. The report no longer has a dependency-module
section. A missing published compilation artifact does not justify rebinding an
already usable declaration.

Compared the retained item node with the current shared node: only `lean` differs.
The initial saved-packet dry run passed at `4bb5cc0523`; that packet still contained
the returned duplicate, so it was repaired before delivery.

Validation of the repaired packet is recorded below.

## Repair validation

The repaired item was compiled with the canonical NW source supplied as a local
side-project overlay, followed by the item: `scompile.py NZ
def-weil-global-geometric-frobenius /home/ubuntu/weil-newtargets-shared/lean/Sheaf/SixFunctors/FrobeniusCohomologyTransportIso.lean
lean/Sheaf/Paper/GlobalGeometricFrobenius.lean` exited 0. The dependency compiled in
28.7 seconds and the item in 4.7 seconds, with no errors or warnings. This validates
the import and declaration interface without adding a duplicate delivery module.


The subsequent required `deliver2.py NZ def-weil-global-geometric-frobenius
--no-push` completed with exit 1 before item elaboration. Its sole failure remains
`INFRASTRUCTURE RETRY (stale live olean)`: the published live build lacks
`Sheaf/SixFunctors/FrobeniusCohomologyTransportIso.olean`. Thus the prescribed
overlay compile passes, but the delivery gate does not reuse that private overlay.
The canonical dependency is not rebound or included in this delivery. Both returned
files are absent; only the item module and item node remain in the packet alongside
the report. No push was attempted. All tool calls completed before the provider
interruptions; there is no unconfirmed delivery mutation.


## Saved-packet retry validation

The next dispatcher retry began by reading this report and running the unchanged
saved packet through `deliver2.py NZ def-weil-global-geometric-frobenius --no-push`.
The gate again exited 1 with `INFRASTRUCTURE RETRY (stale live olean)`, naming the
missing published `Sheaf/SixFunctors/FrobeniusCohomologyTransportIso.olean`.

Reopened the item module, item node, canonical NW record, and current blueprint
(order 2405). The ordinary and compact composites and every-degree maps retain
the reviewed source orientation. Only the item's `lean` field differs from the
current shared node, its recorded signature is verbatim, and its first import is
exactly the canonical public import requested in the return. The packet contains
one Lean module and one node; the duplicate module, dependency node copy and
Dependency modules report section remain absent. NW still owns the canonical
32-declaration dependency record.

Re-ran the required `scompile.py NZ def-weil-global-geometric-frobenius` with the
read-only canonical `Sheaf/SixFunctors/FrobeniusCohomologyTransportIso.lean` source
and the sandbox item file as separate inputs. Exit 0, no errors or warnings:
canonical module 28.7 seconds, item 4.7 seconds (sandbox item 4.5 seconds).
This confirms the repaired packet without delivering or rebinding the dependency.
The final dry-run diagnostic is saved in `dry-run.log`; no wrapper or live file
was modified.


## Current retry validation

Resumed after the provider interruption and confirmed that both completed dry runs
returned exit 1 before item elaboration; neither attempted a push. Rechecked the
canonical source using `scompile.py --source
Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`, and compiled that read-only
source plus the sandbox item through `scompile.py NZ
def-weil-global-geometric-frobenius`: all separate compilation stages passed
without errors or warnings (canonical library check 28.7 s; item library check
4.7 s). The current shared item differs from the packet only in `lean`; the
recorded signature is verbatim, and no Lean line exceeds 100 characters. NW's
canonical 32-declaration record is unchanged. The packet still contains exactly
one item module and one item node, with the requested canonical first import.

The required delivery gate still reports `INFRASTRUCTURE RETRY (stale live
olean)`: the published live build lacks
`Sheaf/SixFunctors/FrobeniusCohomologyTransportIso.olean`. The source interface
is usable and is not rebound. A final gate retry is saved in `dry-run.log`.
No launcher tool or live source/artifact has been modified.


## Successful retry (2026-10-18)

The saved-packet dry run initially reproduced the missing canonical dependency
olean. The required `scompile.py` check with the read-only canonical dependency
source and the sandbox item then passed, with no errors or warnings (canonical
library 28.7 s; item library 4.7 s). The subsequent unchanged-source delivery
dry run passed preflight and compilation at `d772f0210f`. This supersedes the
earlier infrastructure-failure diagnostics above.

The final self-check reopened the item module, node, current blueprint order 2405,
and canonical rational-functor definition. The two components still compose the
canonical transport with the image of `K.str.hom`, and the degree maps apply
cohomology in every integer degree. Only `lean` differs from the current shared
item node; its signature is verbatim. The canonical first import is retained,
the duplicate module and dependency node are absent, and NW's record is unchanged.
No mathematical statement or construction was changed during this retry.
