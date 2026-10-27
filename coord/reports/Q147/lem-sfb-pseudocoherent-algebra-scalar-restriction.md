## Worker report

The module `Sheaf.RingTheory.PseudoCoherentAlgebraScalarRestriction` states
`DerivedCategory.isPseudoCoherent_restrictScalars_iff_of_algebra`, with proof `sorry`.
It is exactly the final assertion of Stacks 064Z, read in
`literature/stacks-project/more-algebra.tex`, lemma-finite-push-pseudo-coherent.
No definitions, new nodes, dependency repairs, or statement corrections are needed.

Clause-by-clause correspondence:

- Commutative rings S and T are `{S : Type uS} {T : Type uT} [CommRing S]
  [CommRing T]`. The arbitrary homomorphism is `(f : S →+* T)`.
- The hypothesis on T[0] is `hT : IsPseudoCoherent ((singleFunctor
  (ModuleCat.{max uS uT v} S) 0).obj ((ModuleCat.restrictScalars f).obj
  (ModuleCat.of T (ULift.{max uS v} T))))`. The single functor concentrates the
  restricted regular T-module in degree zero. ULift is the canonical size copy of
  T, with its usual T-module action, not a new algebra or arbitrary choice.
  `ULift.moduleEquiv` identifies it with T; source scalars act through f.
- Every derived object is `(K : DerivedCategory (ModuleCat.{max uS uT v} T))`.
  The common module universe contains both rings, and v permits arbitrary larger
  modules. Ring universes uS and uT remain independent. The two
  `HasDerivedCategory` instances allow independent morphism universes wS and wT;
  they encode the chosen localizations, not additional algebraic hypotheses.
- The left assertion is `IsPseudoCoherent K`; the right assertion is
  `IsPseudoCoherent ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K)`.
  `↔` includes both implications in the node's order.
- The specified f_* is literally the induced functor of Mathlib's ordinary
  `ModuleCat.restrictScalars`. Its source definition uses `Module.compHom`, keeps
  the underlying additive group, and maps linear maps without changing their
  functions. `mapDerivedCategoryFactors` identifies its action with termwise
  restriction of complexes followed by localization. Thus differentials stay the
  same. No arbitrary comparison map or derived tensor is substituted.
- There is no flatness, surjectivity, boundedness of K, nonzero-ring, or
  Noetherian assumption. The only finiteness hypothesis is hT, as in 064Z.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.RingPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`: a bounded-above complex E with every term
  finite free and `Nonempty (Q.obj E ≅ C)`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor`: localization of cochain
  complexes at quasi-isomorphisms, and the degree-zero embedding.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` supplies exactness of
  `ModuleCat.restrictScalars` in arbitrary universes;
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` supplies
  `CategoryTheory.Functor.mapDerivedCategory` and its termwise factorization.
- `Mathlib.Algebra.Module.ULift` supplies the canonical lifted module and
  `ULift.moduleEquiv` (the latter explains the size copy in hT).

The recorded, stated proof dependencies are imported privately:
`WeilConjectures.RingTheory.PseudoCoherentIffAllM`
(`DerivedCategory.isPseudoCoherent_iff_forall_isMPseudoCoherent`),
`WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle`
(`CategoryTheory.isMPseudoCoherent_of_distinguished_triangle`),
`WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent`
(`DerivedCategory.finite_homology_of_isMPseudoCoherent`), and
`WeilConjectures.RingTheory.FiniteConeFreeModel`
(`DerivedCategory.exists_finiteFree_model_of_finite_cones`).
Their source declarations and docstrings were read. The proof-only dependency
`lem-sfb-pseudocoherent-terms-bounded-above` has neither a Lean record nor a
Mathlib match in the base, so its import is omitted under the rule to import
proof dependencies that are stated. It supplies no object needed to type this
statement. The theorem docstring includes all six accepted proof steps, including
this Tag 064Y input, without inventing an unrecorded postponed theorem.

Edge cases checked before writing: identity ring maps, zero target ring and zero
complex, rank-zero free modules, arbitrary nonflat/nonsurjective maps, complexes
not initially bounded above, and independently sized rings/modules/localizations.
The zero ring is admitted by CommRing; rank zero enters the proof via empty
finite generators; the general K binder does not exclude acyclic or unbounded
representatives. ULift allows the regular target module in exactly the universe
of the tested derived objects. The source requires no omitted standing hypothesis.
No STATEMENT-DISPUTED flag or node fault was found.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: "Restriction of scalars through a pseudo coherent
  algebra preserves and reflects pseudo coherent derived complexes". Eight hits
  include scalar-restriction pseudofunctors and exact derived functors; none
  assert the pseudo-coherence equivalence.
- `msearch.py ... leansearch`: "Pseudo coherent complexes and restriction of
  scalars along a pseudo coherent algebra". Eight hits concern ordinary scalar
  restriction, with no pseudo-coherence equivalence.
- `msearch.py ... loogle`: `"PseudoCoherent", "restrictScalars"`: zero hits.
- `msearch.py ... grep`: `pseudo.?coher|pseudoCoherent`: zero Mathlib hits.
- `rg` for PseudoCoherent, pseudoCoherent and scalar-restriction names in
  `lean/WeilConjectures` and `lean/Sheaf`: existing pseudo-coherence definition
  found and reused. `PolynomialPresentationPseudoCoherence` is a comparison of
  two finite polynomial presentations, not this theorem.
  `FiniteFreeAlgebraPseudoCoherentResolution` assumes a finite-free algebra and
  states only a resolution implication for right modules, not this theorem.
  Neither is a match. The chosen declaration name has no prior occurrence.
- Search for this item's id in `lean/WeilConjectures`: no hit. Search in
  `dag/lean_names_upstream.json` for pseudo-coherence/scalar names: no match.

## Second reading by Q147

A second pass reopened the node, the completed module, the two statement-dependency
source declarations, and Stacks 064Z. This is a self-review: the dispatcher prohibits
starting other agents, and the maintainer's independent review reads the delivery.
The ring-map binders correspond exactly to the first sentence. hT is the restricted
regular module in degree zero; ULift only changes size. K is an arbitrary derived
T-module, and the displayed equivalence retains its two assertions and direction.
The functor is the exact ordinary forgetful functor induced on the localization,
so it has precisely the specified action on groups, differentials, and scalars.
No extra flatness, surjectivity, Noetherian, nontriviality, or boundedness condition
was found. Independent ring and derived morphism universes were retained.
No mismatch or subsequent statement change was needed.
