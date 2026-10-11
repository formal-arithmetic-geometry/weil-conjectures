## Worker report

The delivery adds `AlgebraicGeometry.Scheme.HasFiniteTorDimensionOver`, an explicit
finite Tor dimension predicate for an object over the inverse-image structure sheaf,
and states `hasFiniteTorDimension_schemeDerivedDirectImage_of_bounded_coherent_support`.
The theorem binds a Noetherian target `S`, a locally finite type morphism `f : X ⟶ S`,
derived-category instances, and `E`. `hbounded` renders bounded cohomology by vanishing
of every homology sheaf outside one interval; `hcoherent` renders coherent cohomology;
`hsupport` applies `Scheme.Modules.HasSupportProperOver` degreewise; `hTor` is the new
inverse-image finite-Tor predicate. The conclusion is `Scheme.HasFiniteTorDimension` of
the derived direct image (the ringed-space direct-image functor is definitionally the
recorded scheme direct image).

The dependency declarations used are `Sheaf.AlgebraicGeometry.DerivedCategory`,
`AlgebraicGeometry.schemeDerivedCategory`; `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`,
`AlgebraicGeometry.Scheme.Modules.HasSupportProperOver`; and
`Sheaf.AlgebraicGeometry.FiniteTorDimension`, `AlgebraicGeometry.Scheme.HasFiniteTorDimension`.
The direct image uses `AlgebraicGeometry.RingedSpace.derivedModuleDirectImage` from
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`, which is the body of the
recorded `schemeDerivedDirectImage` declaration.

Edge cases checked: the interval permits `a=b`; zero complexes satisfy the bounded and
support clauses; empty support is represented by the existential closed subset; arbitrary
module test sheaves and all integer degrees are quantified; no nonemptiness or positive
characteristic assumption is introduced.

Searches: `msearch.py ... leanfinder` for finite Tor over an inverse-image ring found no
result (service unavailable); `msearch.py ... loogle` for restriction of scalars and
`DerivedCategory.torAmplitudeIn` found zero hits (the latter identifier is unknown in the
pinned Mathlib); grep of Mathlib and `WeilConjectures` for finiteTorDim/HasFiniteTorDim found
no matching declaration, and grep of `lean/Sheaf` found only the existing global finite-Tor
predicate. `blueprint_refs.py search 'finite Tor dimension'` found only unrelated imported
blueprint nodes. The Stacks pages 08EV and 08CG were opened and checked against every clause.

## New nodes

`def-pc-finite-tor-dimension-over` is needed because no existing DAG, Mathlib, or project
declaration states finite Tor dimension over `f^{-1} O_S`; it records the inverse-image
ring and restriction-of-scalars model and the K-flat representative used by the statement.
Its source is Stacks 08EV hypothesis (3), via Definition 08CG.

## Earlier second reading (a previous round; superseded)

The node and both modules were reread. The Noetherian, locally finite type, bounded,
coherent, proper-support, and finite-Tor hypotheses each occur once in the theorem;
the conclusion is finite Tor dimension of the derived direct image. The new definition
quantifies a single interval independently of every inverse-image module and every degree.
No mismatch was found.

## Second reading by E1

I reread the unit statement, its Stacks source (Tag 08EV, proof of Lemma 36.27.1),
and both delivered modules against every dependency declaration.

- **Objects.** `S : Scheme.{u₁}` with `[IsNoetherian S]` is the Noetherian target;
  `X : Scheme.{u₁}`, `f : X ⟶ S` with `[LocallyOfFiniteType f]` is the locally
  finite type morphism; `E : schemeDerivedCategory X` is the object of
  `D(O_X)`. The two `HasDerivedCategory` binders provide the derived categories
  on X and S. The conclusion uses the recorded
  `RingedSpace.derivedModuleDirectImage f.toLRSHom.toShHom`.
- **Hypotheses.** `hbounded` now renders one common finite interval, explicitly
  with `a ≤ b`, and vanishing of every homology object outside it. `hcoherent`
  states coherence of every homology sheaf. `hsupport` states
  `Scheme.Modules.HasSupportProperOver f` degreewise. `hTor` is exactly the
  delivered `HasFiniteTorDimensionOver f E`, whose definition restricts scalars
  along `f⁻¹ O_S` and uses one interval for every inverse-image module and all
  degrees. No extra Noetherian, separated, characteristic, or nonemptiness
  assumption occurs.
- **Conclusion.** `HasFiniteTorDimension S` of the derived direct image is the
  existing global finite-Tor predicate, with its own common interval and all
  `O_S`-module tests, matching the node clause.

The only mismatch found was the missing inequality `a ≤ b` in the worker's
`hbounded` binder. I added it to the Lean signature and copied the exact updated
signature into the node's `lean.statement`; this is required by the finite
interval in the source and by the global finite-Tor convention. The definition
module and all other hypotheses and conclusion already matched. The zero object
satisfies the clauses, `a = b` is allowed, empty supports are allowed by
`HasSupportProperOver`, all integer degrees are quantified, and the universe
choices do not exclude empty schemes or index types. Searches recorded in the
worker report found no existing finite-Tor-over-inverse-image declaration in
Mathlib, `WeilConjectures`, or `lean/Sheaf`; the global
`Scheme.HasFiniteTorDimension` is a distinct notion and is reused only for the
conclusion.
