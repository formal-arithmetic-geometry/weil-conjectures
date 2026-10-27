## What changed

Replaced the proof of `AlgebraicGeometry.etaleTowerBrownAdjunction` by a Lean
construction from three separate geometric interface lemmas. The existing public
statements, definitions, public imports and universe binders are unchanged.

The proved private helpers establish the Grothendieck/coproduct/conservativity
properties at each site, compare the recorded derived models with the smaller
localizations required by Brown representability, transfer exactness through the
inverse-image adjunctions, paste the coefficient transition squares, reflect
coproduct cocones through all evaluations, and calculate scalar transposition
through the Brown adjunction. The coefficient helper proves regularity of the
chosen generator, adic completeness and finiteness of all its quotient rings.
The Noetherian helper supplies the hypotheses for proper finite-level coproducts.

Added three statement modules, each with its own source, proof plan and DAG node:
`EtaleCompactSupportConstruction`, `EtaleCompactSupportScalarAction`, and
`EtaleCoefficientProperCoproducts`. Updated the item's node to the implemented
route. No source-library file, target signature or existing definition was changed.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.etaleTowerBrownAdjunction`,
by a complete proof from the three statements below and existing library lemmas.
The item module has zero remaining `sorry`. This delivery is a decomposition,
not a net elimination of holes: one original hole closed, three holes added.

The new holes are exactly:

- `AlgebraicGeometry.etaleCompactSupport_construction`, node
  `lem-pur-etale-compact-support-construction`: coherent ordinary and derived open
  extension on the already specified strict-system interface, including its mate
  and transition equations. It asserts no Brown adjoint, scalar compatibility,
  triangulatedness, or coproduct preservation.
- `AlgebraicGeometry.etaleCompactSupport_scalarAction`, node
  `lem-pur-etale-compact-support-scalar-action`: normalized canonical coefficient
  multiplication and its preservation by the given compact-support functor.
  The Brown adjoint and all Hom/scalar transpose assertions are proved above it.
- `AlgebraicGeometry.etaleCoefficientProper_coproducts`, node
  `lem-pur-etale-coefficient-proper-coproducts`: transport of the existing proper
  finite-coefficient coproduct theorem from module-valued sheaves to the specified
  ringed-site coefficient presentation and universal derived model.

Each retained hole is a public theorem with exactly a `by sorry` proof. No hole
occurs in a definition, private helper or the combining proof. Edge cases checked
in the statements: positive quotient exponent at n=0, zero coefficient quotients,
arbitrary ramification and arbitrary chosen generator of the maximal ideal,
empty schemes, and empty coproducts. The construction lemma does not impose the
finite-field base hypothesis of the earlier system-adjoint existence theorem.

## No longer needed

Removed these private proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts`: used below the new
  coefficient-presentation transport lemma, rather than directly at this level.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`:
  exactness now follows from the exact inverse-image adjoints.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  the combining proof uses the existing derived-coproduct API.
- `Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear`: scalar compatibility is the
  separate geometric scalar lemma; scalar transposition is proved directly.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: the open
  construction is isolated in the construction lemma.
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`:
  the system and coefficient-universe Grothendieck lemmas give the needed instances.
- `Mathlib.CategoryTheory.Localization.Linear` and
  `Mathlib.Algebra.Homology.DerivedCategory.Linear`: the public interface specifies
  normalized central scalar endomorphisms, and the combining proof calculates with
  them directly instead of choosing additional global `Linear` instances.

The direct right-derived-triangulated dependency
`lem-pc-right-derived-functor-triangulated` is unnecessary for this argument.
The source module is preserved. The other removed direct dependencies concerning
open extension, constant-module presentation, scalar localization and K-injectives
remain needed by the proof plans of the separate geometric lemmas or by the
existing derived-coproduct API; no claim is made that they are globally pruned.
No existing module is withdrawn, and no blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned geometric statements use a different coefficient presentation from
the current strict-system interface. Existing extension-by-zero and proper-image
coproduct declarations act on sheaves valued in `ModuleCat A`; the level categories
here are modules over the sheafified constant quotient ring. Transport must also
respect the explicitly normalized inverse-image lift and derived-factorization
maps. Applying the former declarations directly does not typecheck.

The existing `etaleCoefficientSystemAdjoint` existence theorem specializes to an
algebraic closure of a finite field and a prescribed uniformizer. It cannot supply
the compact-support construction for the arbitrary characteristic-p field and
arbitrary maximal-ideal generator of this item. The new construction lemma states
only the missing geometric part at the required generality.

The Brown theorem uses a smaller derived localization than the standard recorded
`strictEtaleSystemDerived` instance. The proved `brownSized` helper handles this
by exact identity-induced equivalences and cancellation of adjoint equivalences;
no universe or public signature is changed. Explicit local instance priority
also keeps the recorded level/system localizations consistent when importing the
private comparison helpers.

## New nodes

`lem-pur-etale-compact-support-construction` in
`dag/nodes/sec-smooth-purity/lem-pur-etale-compact-support-construction.json`
is the geometric construction and open-restriction coherence part of the original
Step 3/4. Its Lean attachment is `Sheaf.Paper.EtaleCompactSupportConstruction`.

`lem-pur-etale-compact-support-scalar-action` in
`dag/nodes/sec-smooth-purity/lem-pur-etale-compact-support-scalar-action.json`
is the normalized scalar multiplication part of the original Steps 3/5. Its Lean
attachment is `Sheaf.Paper.EtaleCompactSupportScalarAction`.

`lem-pur-etale-coefficient-proper-coproducts` in
`dag/nodes/sec-smooth-purity/lem-pur-etale-coefficient-proper-coproducts.json`
is the coefficient-presentation transport within original Step 6. Its Lean
attachment is `Sheaf.Paper.EtaleCoefficientProperCoproducts`.

All three are strictly separate parts of the argument, preserve the current
blueprint unit route, and include the three search records. The proof-context change record is
`coord/changes/E3-etale-tower-brown-proof-context.md`; it documents the new local
instance attributes and helper universe commands requested by the delivery checker.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
