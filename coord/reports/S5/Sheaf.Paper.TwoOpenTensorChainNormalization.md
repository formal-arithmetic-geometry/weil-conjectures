## What changed

Proved the two assigned theorem bodies in `Sheaf.Paper.TwoOpenTensorChainNormalization`
from two new finite-presentation interface lemmas. All existing definitions and theorem
signatures are unchanged. Added proof-only imports of `FiniteTensorPullCoherence` and
`FiniteOpenGammaRestriction`.

The main proof explicitly derives the compositor/unit equation from
`Adjunction.unit_leftAdjointUniq_hom_app`. It proves a generic calculation for nesting two
unit-normalized maps, and a tensor calculation combining naturality with pullback
composition. The rho calculation expands both signed symmetries, moves one past the unit
and the inverse-unit tensor map, and cancels the adjacent symmetries. The left and right
chain calculations then apply the generic helpers with the two different tensor orders.
Invertibility is proved separately from the actual projection isomorphism, involutive
symmetry, functorial images of delta, and the compositor.

`FiniteOpenGammaRestriction` also proves `finiteOpenUnit_isIso` by exact localization of
the existing fully faithful open adjunction. This is the same unit used by the existing
`twoOpenUnitIso`; it supplies no alternative adjunction or data construction.

## Proved and sorry left

Closed the two original holes:

- `WeilConjectures.FiniteOpenProduct.twoOpenRhoNormalization`.
- `WeilConjectures.FiniteOpenProduct.twoOpenTensorChainNormalization`.

Added two holes, each in its own module with its proof in words:

- `WeilConjectures.FiniteOpenProduct.finiteOpenGammaRestriction`
  (`lem-pur-finite-open-gamma-restriction`): transport the actual extension-first
  projection map to its unit-normalized restriction equation.
- `WeilConjectures.FiniteOpenProduct.finiteTensorPullCoherence`
  (`lem-pur-finite-tensor-pull-coherence`): the five elementary coherence equations on
  the published finite tensor, signed symmetry, and exact pullback comparisons.

This is a decomposition: two original holes closed, two lower holes added, zero net
holes closed. The assigned module compiles cleanly after import cleanup (9.1 seconds) and has zero remaining `sorry`.
Both new modules also compile within 60 seconds. All private helpers
and the new unit instance are proved.

## No longer needed

Removed the redundant proof-only `Mathlib.CategoryTheory.Adjunction.Basic` import;
its API is already available through the retained imports.
Removed redundant direct public imports of `PurityFiniteSetting` and
`OpenTensorNormalization` (both are publicly exported by `FiniteOpenProductSwap`),
and the unused direct `DerivedPullbackTensorIso` import. No existing modules were
withdrawn and no source-library declaration changed.

The assigned proof no longer directly applies `lem-sf-open-tensor-normalization` or
`lem-pur-derived-pullback-tensor-iso`; the two new interface lemmas expose their needed
finite-presentation consequences. Those dependencies remain needed below the new lemmas
and are NOT claimed as global pruning. The parent's proof dependencies and obsolete
parent-level tool-use entries were updated accordingly. The composite-adjunction
Mathlib leaf and finite-open-operations definition remain directly used.

## Where the brief, the DAG or earlier work was wrong

The plan describes the finite gamma restriction and tensor coherence as immediate
specializations, but the published Lean APIs state them on different presentations:
OpenTensorNormalization uses intrinsic realization equivalences, while the pullback
coherence statements use canonical finite intrinsic operations. The actual
FiniteOpenProduct maps are fixed-scalar and exact-derived. Their transport is a real
interface step; the new statements isolate precisely that step, without restating either
assigned theorem.

A direct proof of gamma restriction from the published adjunction projection transpose
was developed. The calculation reaches the desired component equality, but the expanded
comparison terms made kernel checking exceed the file limit. The new lemma's proof in
words records the shorter direct inverse-transpose argument, which avoids the intrinsic
realization detour. The incomplete experiment is outside the delivered Lean modules.
The two-open chain calculation is complete independently of this lower interface proof.

A read-only traversal of statement/proof dependencies encountered a pre-existing
cycle `lem-pc-ring-hom-extension-differential` ->
`lem-pc-ring-hom-extension-differential-adjacent` ->
`lem-pc-ring-hom-extension-differential`. This packet does not change those nodes;
its new nodes depend only on existing dependencies of the assigned item.

The unit record `sk-prop-an` has no realized step attached to this auxiliary node; its
statement and route are unchanged. Source reading: the current blueprint
`literature/blueprint/latest/.../lem-sf-kunneth-coherence.proof.md`, Stacks
`sites-cohomology.tex` labels `lemma-pullback-tensor-product` and
`lemma-j-shriek-and-tensor`, and `sites-modules.tex` label `lemma-j-shriek-and-tensor`.

## New nodes

`lem-pur-finite-open-gamma-restriction` owns `FiniteOpenGammaRestriction`. It is only the
extension-first, one-open formula, for arbitrary finite commutative coefficients and
unbounded inputs. It neither mentions rho nor a second open immersion. At an identity
open its equation reduces to the usual unit normalization; a zero input gives the zero
map. No boundedness or finite Tor hypothesis was introduced.

`lem-pur-finite-tensor-pull-coherence` owns `FiniteTensorPullCoherence`. It is independent
of extension by zero, units, delta, and either nested chain. Its naturality and composition
equations have the correct domains, and its involution uses both signed swaps, including
odd/odd inputs. Identity pullbacks reduce to tensor naturality with the canonical
compositor. These are the finite-presentation consequences of the existing cochain
coherence/descent route, not copies of either assigned statement.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
