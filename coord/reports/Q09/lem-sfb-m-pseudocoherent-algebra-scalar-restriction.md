## Worker report

The module `Sheaf.RingTheory.MPseudoCoherentScalarRestriction` states
`DerivedCategory.isMPseudoCoherent_restrictScalars_iff`, with proof `sorry`.
It states precisely the fixed-integer equivalence in Stacks 064Z, More on Algebra,
`lemma-finite-push-pseudo-coherent` (local source lines 16282–16342).
No definition, dependency repair, new node, or statement correction is needed.

Hypothesis and clause correspondence:

- Commutative rings S and T: `{S : Type uS} {T : Type uT} [CommRing S] [CommRing T]`.
- The ring homomorphism: `(f : S →+* T)`. No `Algebra`, flatness, surjectivity,
  Noetherian, finite-type, or nontriviality hypothesis is added.
- T[0] pseudo-coherent over S through f: `hT : IsPseudoCoherent
  ((singleFunctor (ModuleCat.{max uS uT v} S) 0).obj
  ((ModuleCat.restrictScalars f).obj (ModuleCat.of T (ULift.{max uS v} T))))`.
  The `ULift` is the canonical lifted regular T-module; it supplies enough universe
  room without changing the additive group or scalar action up to canonical equivalence.
  `singleFunctor ... 0` puts precisely this restricted regular module in degree zero.
- Every integer m: `(m : ℤ)`, without any sign restriction.
- Every unbounded derived T-module K: `(K : DerivedCategory
  (ModuleCat.{max uS uT v} T))`, with no cohomological bound.
- Left side: `IsMPseudoCoherent m K` uses the dependency's bounded finite-free
  approximation, isomorphisms above m, and epimorphism in degree m.
- Right side: `IsMPseudoCoherent m
  ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K)` uses the same cutoff m.
- The two directions are `↔`, with the T predicate on the left and S on the right.
- The specified f_* is Mathlib's exact `ModuleCat.restrictScalars f` followed by
  `Functor.mapDerivedCategory`. Reading `RestrictScalars.obj'` and `map'` confirms
  unchanged carriers, additive structure and differentials, with action f(s)•k.
  `restrictScalars_map_exact` and its finite-limit/finite-colimit instances supply
  exactness. `mapDerivedCategoryFactors` identifies its value on any representing
  complex with termwise restriction followed by Q. Quasi-isomorphism preservation
  is part of this existing localization construction, not an extra assumption or
  an arbitrary choice of functor.
- `[HasDerivedCategory.{wS} ...]` and `[HasDerivedCategory.{wT} ...]` are the recorded
  size-convention interfaces, independently chosen. Ring universes are independent,
  and the module universe `max uS uT v` accommodates both rings and arbitrary modules.

Dependencies read and used:

- `WeilConjectures.RingTheory.RingPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`:
  its full definition is bounded-above finite-free representative up to derived iso.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`: the recorded unbounded localization.
  This is publicly reexported by the exact-functor module.
- `WeilConjectures.RingTheory.MPseudoCoherent`, `DerivedCategory.IsMPseudoCoherent`:
  its full definition gives bounded finite-free approximation with the required
  degreewise isomorphisms and epimorphism.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` and
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` give exact restriction and
  the canonical induced functor described above; their full interfaces were read.

Plain proof imports follow the recorded proof-dependency modules:
`WeilConjectures.RingTheory.PseudoCoherentIffAllM`,
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
`WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle`, and
`WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent`.
The proof dependency `lem-sfb-pseudocoherent-terms-bounded-above` currently has no
Lean record or Mathlib match, so has no import yet. It is used only in the future
proof, not in typing the statement. Its role is explicit in the seven-step docstring.

Edge cases checked: S or T the zero ring; zero/acyclic K; negative, zero and positive
m; zero-rank finite-free terms; bounded-above and arbitrarily unbounded-below K;
nonflat nonsurjective maps; separate ring and localization universes. The statement
excludes none of these. In the induction proof, an upper bound (rather than a
largest nonzero cohomology degree) handles the acyclic case. No disputed statement
or node fault was found.

Searches for an existing declaration:

- `msearch.py ... leanfinder "pseudocoherent algebra scalar restriction"`: eight
  hits, including `RestrictScalars.algebra`, ordinary finite presentation and ring
  restriction pseudofunctors; no fixed-degree derived equivalence.
- `msearch.py ... loogle '"IsMPseudoCoherent", "restrictScalars"'`: zero hits.
- `msearch.py ... grep 'pseudo.?coher|mPseudoCoherent'`: zero Mathlib hits.
- `msearch.py ... leansearch "Restriction of scalars along a pseudo coherent algebra
  preserves and reflects m pseudo coherent derived objects"`: eight hits, mainly
  `ModuleCat.restrictScalars`, its object construction, and sheaf restriction;
  no pseudo-coherence theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node id and `isMPseudoCoherent.*restrictScalars` / reverse order found
  no existing fixed-degree equivalence. Wider pseudo-coherence and scalar searches
  found the recorded definitions and polynomial-presentation invariance, which
  concerns full pseudo-coherence and does not state this lemma.

Validation: scompile.py compiled this file both as sandbox and library module
against the live server build, with no warnings or errors (1.6 s / 1.8 s).
All universes and variables are explicitly bound, `autoImplicit` is false, and
all Lean lines are at most 100 characters.

## Second reading by Q09

I reopened the node, the completed file, and the Stacks lemma for a separate pass.
This is a self-review: the dispatcher explicitly forbids starting other agents;
the maintainer supplies independent review after delivery.

The binder `hT` applies pseudo-coherence to the actual restricted lifted regular
module in degree zero, rather than to an unrelated module or an assumed abstract
scalar functor. S, T, and f match the node. The degree binder is ℤ and the conclusion
uses exactly the same m on both sides. K ranges over the entire derived category.
The exact functor's documented termwise construction matches the requested scalar
action and preservation of quasi-isomorphisms. No extra boundedness or algebraic
hypothesis occurs. `ULift` is canonical size transport, not an added mathematical
restriction. The seven proof steps preserve the accepted split, including the
zero-witness base case and finite top-cohomology induction. No mismatch was found
and no revision was needed in this reading.
