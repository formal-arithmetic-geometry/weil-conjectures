## What changed

Replaced the body of `AlgebraicGeometry.Scheme.finiteQuotient_finiteModule_models_succ`
with a reduction through bounded finite etale-local cohomology and etale derived origin.
Its statement and public imports are unchanged. The original module now privately imports
`FiniteQuotientFiniteModuleCohomology` and `FiniteCoefficientEtaleBoundedModels`.

The new `FiniteCoefficientEtaleBoundedModels` theorem is proved from the existing
`AlgebraicGeometry.Etale.etale_site_bounded_constant_models` and the separate origin step.
Its private small-carrier helper constructs the algebraic complex explicitly: restrict the
ULift coefficient action, shrink each finitely generated module, conjugate every differential,
and prove the chain isomorphism, the original degree bounds and finite generation.
The proof constructs the covering sieve, proves joint surjectivity, and extends the models
to every arrow of the sieve by actual derived pullback and constant-sheaf comparisons.
The carrier construction adapts the proved construction in `SmallPerfectCoefficientLift`
without its projectivity requirement; it does not import that theorem.

Two proved private helpers in the assigned module show that all module sheaves and all
derived objects on an empty chart's proetale slice are zero. The main theorem uses the zero
algebraic complex on such charts and obtains its restriction isomorphism from zero objects.

The two remaining statements are separate mathematical steps. The coefficient-filtration
statement constructs only models of individual cohomology sheaves, with vanishing bounds;
it asserts no complex model or differential. The origin statement supplies an etale derived
object with finite cohomology local models and transports any supplied constant complex
model. It does not assert existence of a bounded algebraic complex. The proved bounded-model
theorem performs that construction using 094G. Neither new hole repeats the assigned
successor-complex theorem.

Validation: all four delivered modules compiled through `lcompile.py`. The two new
statements took 8.2 s and 6.8 s; the final bounded-model proof and assigned theorem
compiled cleanly in 14.6 s and 7.9 s, respectively. No compiler warnings remain.
The assigned theorem signature is byte-identical to the shared source.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.Scheme.finiteQuotient_finiteModule_models_succ` (1 of 1 original holes).
There are zero `sorry` bodies in the assigned module.

Also proved `AlgebraicGeometry.Scheme.finiteCoefficient_etale_bounded_models`, including its
private small-carrier construction, covering-sieve argument and further-restriction proof.

Added exactly two holes:

- `AlgebraicGeometry.Scheme.finiteQuotient_finiteModule_cohomology_succ`, node
  `lem-weil-pbc-finite-quotient-finite-module-cohomology`.
- `AlgebraicGeometry.Scheme.finiteCoefficient_etale_slice_origin`, node
  `lem-weil-pbc-finite-coefficient-etale-slice-origin`.

This is a decomposition, not an axiom-free proof of the original mathematical obligation:
one original hole is closed and two strictly separate steps remain. Both are public named
theorems with source citations and complete proofs in words, each in its own new module.

## No longer needed

No original Lean import was removed: the assigned module initially imported only its
statement data. No module is withdrawn, and no global pruning is claimed.

The original direct planned dependencies are now assigned to the precise lower steps in
the new nodes. The construction uses `EtaleSiteBoundedConstantModels` directly; it does not
need to invoke `FiniteRingDerivedLocalConstancy` or `NilpotentReductionLissity` as additional
steps. The latter nilpotent lissity step is unnecessary here because both outer cohomology
terms in the coefficient-filtration triangle already have finite etale-local constant
models, and the finite local-system Serre argument gives the middle term directly.
Thus `lem-weil-pbc-finite-ring-derived-local-constancy` and
`lem-weil-pbc-nilpotent-reduction-lissity` are removed from this route's proof dependencies.
They may still be used elsewhere; no existing declaration is removed or changed.

`pqf-lem-locnoeth-lft` is retained in the origin node: local Noetherianity is inherited by
etale chart schemes when that step identifies their sites. No separate direct proof
import of it is needed by the assigned module.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The blueprint ancestry tool returns no
blueprint ancestor for the assigned generated node (its `created.item` is a module name).
The new nodes therefore record a null blueprint ancestor, with this item in `via`;
searches for 094G, 09AL and finite locally constant cohomology found no duplicate
blueprint statement for these specialized steps. The declared dependencies contain the
abstract finite-type Serre argument, bounded constant-model descent and finite-ring derived
origin, but not the specialization linking the actual completed coefficient reductions to
those encodings. These missing pieces have been stated separately, without asserting
projectivity, completed realization, compatible trivializations or a new Tor hypothesis.
The intermediate origin object is used only by existential elimination in a proof; no
public definition is defined by choosing it from an unproved mere existence statement.

The original source's `NilpotentReductionLissity` step is redundant for this particular
successor argument: the coefficient triangle and etale finite local-system Serre closure
suffice. The unit's proper-base-change route is unchanged.

## New nodes

`lem-weil-pbc-finite-quotient-finite-module-cohomology` records the coefficient-filtration
cohomology calculation, with the two prescribed local perfect models and actual scalar
compatibility. Its new module is `Sheaf.Paper.FiniteQuotientFiniteModuleCohomology`.

`lem-weil-pbc-finite-coefficient-etale-slice-origin` records bounded derived origin and
transport of supplied models on a finite-coefficient slice, independently of an adic
filtration. Its new module is `Sheaf.Paper.FiniteCoefficientEtaleSliceOrigin`.

`lem-weil-pbc-finite-coefficient-etale-bounded-models` records the proved assembly of the
existing etale bounded constant-model theorem, universe transport and sieve restriction.
Its new module is `Sheaf.Paper.FiniteCoefficientEtaleBoundedModels`.

The assigned node's proof, proof dependencies and proof origin follow this assembly.
No existing module or node other than the assigned node is changed; no change record is
required.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
