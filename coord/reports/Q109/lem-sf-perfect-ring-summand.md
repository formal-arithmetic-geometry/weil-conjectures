## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.PerfectRingSummand` states
`DerivedCategory.isPerfectRingComplex_summand`, with `sorry` as its only proof.
The node is unchanged outside `lean`. No new notions, dependency repairs, or
statement corrections are needed. No repair note exists for this item.

Clause-by-clause correspondence:

- “A a commutative ring” is `{A : Type u} [CommRing A]`. No nonzero,
  Noetherian, coherence, or field hypothesis is imposed.
- “K,L objects of D(A)” is `(K L : DerivedCategory (ModuleCat.{u} A))`.
  `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` selects the localization and
  its morphism universe, as the recorded derived-category dependency requires.
  The independent `w` is not identified with `u`. The module universe follows
  the recorded perfect-ring-complex predicate, which uses `ModuleCat.{u} A`.
- “K ⊕ L” is the categorical binary biproduct `K ⊞ L`, in that derived
  category; it is not a direct sum of arbitrarily chosen representatives.
- “If K ⊕ L is perfect” is `(h : IsPerfectRingComplex (K ⊞ L))`.
- “both K and L are perfect” is the full conjunction
  `IsPerfectRingComplex K ∧ IsPerfectRingComplex L`.

Recorded statement dependencies read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`. I read their definitions
  and docstrings in the pinned Mathlib checkout. The chosen localization has
  arbitrary morphism universe `w` and is additive.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`. I read its entire definition:
  a complex P, integers a,b, `P.IsStrictlyGE a`, `P.IsStrictlyLE b`, finite
  projective terms, and an isomorphism `C ≅ Q.obj P`. Thus the conclusion
  means exactly the bounded finite projective models in the node.

The module also imports every already stated proof dependency. I read the
signatures/docstrings of `DerivedCategory.IsPseudoCoherent` in
`Sheaf.RingTheory.RingPseudoCoherent`,
`CochainComplex.exists_finiteFree_model_of_finite_projective` in
`Sheaf.RingTheory.FiniteProjectiveComplexFreeModel`,
`CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat` in
`Sheaf.Algebra.Homology.BoundedFlatKFlat`,
`DerivedCategory.exists_derivedTensor_second_factor_functor` in
`Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`,
`DerivedCategory.mPseudoCoherent_summand` and `pseudoCoherent_summand` in
`Sheaf.Algebra.Homology.RingPseudoCoherentSummand`, and
`DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude` in
`Sheaf.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect`.
The Mathlib leaf `Module.Flat.of_projective` (and its free specialization
`Module.Flat.of_free`) is in `Mathlib.RingTheory.Flat.Basic` and is imported.
These are proof-only imports, not extra hypotheses or duplicated definitions.
The declaration docstring spells out all six DAG proof steps and their inputs.

Source check: the local Stacks `more-algebra.tex`,
`lemma-summands-perfect` (Tag 066S), says that if K ⊕ L is perfect then
both summands are perfect. Its proof invokes the perfectness criterion,
pseudo-coherent summands, and Tor-amplitude summands, precisely the DAG route.

Edge cases checked before writing: the zero ring is admitted by `CommRing`;
either or both summands may be the zero object; arbitrary non-Noetherian
commutative rings and finite projective modules that are not free are admitted.
Neither termwise splitting of an arbitrarily chosen model nor boundedness of
K or L is assumed. No characteristic or amplitude restriction is imposed.
There is no suspected false statement and no statement dispute.

Searches for an existing statement (2026-10-17):

- `msearch.py ... leanfinder "A direct summand of a perfect complex over a
  commutative ring is perfect"`: eight hits, including K-projectivity and
  `CategoryTheory.Retract.hasProjectiveDimensionLT`, none expressing perfect
  ring-complex summands.
- `msearch.py ... loogle "DerivedCategory, CategoryTheory.Retract"`: zero hits.
- `msearch.py ... leansearch "direct summand of a perfect complex of modules
  is perfect"`: eight hits about perfect pairings and flat direct sums;
  no matching theorem.
- `msearch.py ... grep "perfect.*summand|Perfect.*biprod|IsPerfectRingComplex"`:
  zero Mathlib hits.
- `rg` over `WeilConjectures` and `lean/Sheaf` for
  `IsPerfectRingComplex|perfect.*summand|[Pp]erfect.*[Bb]iprod|[Pp]erfect.*[Rr]etract`
  and for the item id: no existing ring summand theorem. The scheme theorem
  `Sheaf.AlgebraicGeometry.PerfectSummand` concerns scheme-module complexes,
  and hence has different objects. The upstream `DerivedCategory.IsPerfect`
  has an unnecessarily specialized localization universe and supplies no
  summand theorem. Existing ring triangle closure and perfect cohomology
  assembly results also have different hypotheses/conclusions.

## Second reading by Q109

I reopened the node, the Stacks lemma, the recorded perfectness definition,
and the finished module for a separate checking pass. This is a same-worker
second pass; the dispatcher forbids starting another agent, and the maintainer
will perform the independent review. The ring binder supplies exactly the
commutative-ring hypothesis; K and L inhabit the recorded D(A), with no
boundedness hypothesis; `⊞` is their derived categorical direct sum; `h`
asserts exactly its perfectness; the conclusion asserts perfectness of each
summand using the same predicate. The source adds no suppressed Noetherian
hypothesis. Both universes are explicitly bound and `w` remains independent.
The one postponed theorem matches the item and has its six-step proof in the
docstring. No mismatch or required statement change was found.
