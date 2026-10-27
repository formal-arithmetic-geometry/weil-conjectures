## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedPullbackMPseudoCoherent` states
`AlgebraicGeometry.derivedPullback_preserves_mPseudoCoherent`. It contains one
named theorem with proof `sorry`, no definitions and no auxiliary theorems.
Only the item's `lean` field changes. No statement correction or dependency
repair is needed.

Source read: `literature/stacks-project/cohomology.tex`,
`lemma-pseudo-coherent-pullback` (Tag 09U7), including its proof, and the preceding
`definition-pseudo-coherent` and
`lemma-pseudo-coherent-independent-representative` (Tags 08CB and 08CC).
The stated scheme specialization agrees with that unrestricted ringed-space lemma.
The suggested CompactObject example has been withdrawn in the current read clone
and contains no declarations; this module follows the current module/public-import
conventions of the recorded MPseudoCoherentComplex dependency instead.

Hypothesis and clause correspondence:

- Schemes `T` and `Y`: `{T Y : Scheme.{u}}`, using the recorded Mathlib scheme
  category and its morphisms. Arbitrary `h : T ⟶ Y` has no property assumptions.
- Integer degree: `(m : ℤ)`, without a sign restriction.
- Arbitrary object of `D(𝒪_Y)`: `(K : schemeDerivedCategory Y)`, not the
  quasi-coherent subcategory and with no boundedness requirement.
- The local strictly perfect approximation hypothesis is exactly
  `(hK : Scheme.IsMPseudoCoherent Y m K)`. The recorded definition quantifies
  over every point and a neighbourhood containing it, a strictly perfect
  complex transported across `Scheme.Modules.overEquiv`, and an arrow to the
  derived open pullback, with `IsIso` on cohomology above `m` and `Epi` at `m`.
  Neighbourhoods and approximations can depend on `m`; no global cover or bound
  is imposed by the theorem.
- Derived pullback is exactly the recorded functor `(derivedPullback h).obj K`.
- Conclusion: `Scheme.IsMPseudoCoherent T m ((derivedPullback h).obj K)` uses
  exactly the same degree and the same recorded approximation predicate on `T`.
- The two `HasDerivedCategory.{w}` binders and the two families of such binders
  for open subschemes provide the localizations required by the recorded
  definitions. They specify categorical models, not flatness, quasi-coherence,
  Noetherianity or any geometric restriction. Universes `u w` are explicit and
  `autoImplicit` is disabled. No extra localization on over-sites is assumed.
- The explicit negative clause is respected: there are no flatness,
  quasi-coherent cohomology, Noetherian, quasi-compactness or separatedness
  assumptions.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; full signatures/docstrings read in Scheme.lean.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, the shared derived category of
  `SheafOfModules.{u} (moduleRings Y.toRingedSpace)`; its complete definition
  and docstring were read.
- `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent`; complete definition/docstring read.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`:
  `AlgebraicGeometry.derivedPullback`; the section binders, complete definition,
  docstring, comparison and `derivedPullback_spec` were read. It is the canonical
  transported left derived pullback, not an arbitrarily chosen functor.

The proof-only imports mirror all stated proof dependencies, including Mathlib
matches (which need no additional Lean record):

- `WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`:
  `AlgebraicGeometry.derivedPullback_openRestriction_iso_universes`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
  `CategoryTheory.Pretriangulated` (TR1).
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.HomologySequence.exact₁`, `exact₂`, `exact₃`.
- `WeilConjectures.AlgebraicGeometry.InverseImageModuleFunctor`:
  `TopCat.Sheaf.inverseImageModuleFunctor_exact`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the recorded
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings` interface publicly retains
  the generic ringed-site construction needed by the proof.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:
  `CategoryTheory.Functor.homologyFunctorIso`.
- `Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds`:
  `SheafOfModules.ringedTensorCohomologicalBounds`, clause (a).
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`:
  `AlgebraicGeometry.Scheme.IsStrictlyPerfect`, `IsPerfect`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect`:
  `AlgebraicGeometry.derivedPullback_preserve_perfect`.

The theorem docstring retains the node's complete six-step proof plan, including
cone vanishing in degrees at least `m`, the upper bound `m - 1` after nonflat
scalar extension, refining perfect objects to strictly perfect models, and the
final long exact cohomology sequence.

Edge cases checked before writing: all integers including negative degrees and
`m = 0`; zero objects (zero strictly perfect approximations); empty target scheme
(the pointwise conclusion is vacuous); identity morphisms; nonflat morphisms;
non-Noetherian schemes; and non-quasi-compact schemes, whose local approximations
need not admit a uniform upper bound. No finite or nonempty cover condition,
cohomological global bound, or extra universe equality occurs in the signature.
The cone bound follows from surjectivity at `m` and isomorphisms above `m`; the
conclusion asks only surjectivity at `m`, not an isomorphism there. No statement
is disputed.

Searches performed with the prescribed wrapper:

- LeanFinder: `Derived pullback preserves m pseudo coherent complexes on schemes`:
  eight hits, ordinary scheme pullbacks, cover pullbacks and the ordinary module
  pullback pseudofunctor. None concerns the required degreewise approximation.
- Loogle: `"IsMPseudoCoherent"`: zero hits.
- Mathlib grep: `pseudo.?coher|IsMPseudoCoherent`: zero hits.
- Project `rg` on both `lean/WeilConjectures` and `lean/Sheaf`:
  `IsMPseudoCoherent|derivedPullback.*[Pp]seudo|[Pp]seudo.*derivedPullback`.
  Found the shared scheme definition and its uses, separate ring-level
  approximation results and algebraic-space predicates. None states this
  scheme derived-pullback preservation theorem. In particular ring localization
  results concern a different carrier and only a specialization.
- Search of `lean/WeilConjectures` for
  `lem-sfb-derived-pullback-m-pseudocoherent`: no hits.

Validation: `scompile.py` compiled the sandbox and library module cleanly on the
server (2.4 seconds each). `deliver2.py --no-push` passed the server preflight
and per-file compilation, printing OK for commit ea24627d49f. No Lean errors or
unexpected warnings were reported. The delivery wrapper supplies the required
second-reading heading and records that independent review belongs to the maintainer.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
