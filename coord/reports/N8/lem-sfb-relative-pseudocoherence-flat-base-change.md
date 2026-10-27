## Worker report

The module `Sheaf.AlgebraicGeometry.RelativePseudoCoherenceFlatBaseChange` states
`AlgebraicGeometry.Scheme.isMPseudoCoherentRelativeTo_of_flatBaseChange` and
`AlgebraicGeometry.Scheme.isPseudoCoherentRelativeTo_of_flatBaseChange`.
Both proofs are `sorry`, as required at stage 2; no definitions or additional axioms
are introduced. The original statement and all dependency lists are unchanged.

The source was read in `literature/stacks-project/more-morphisms.tex`,
`lemma-base-change-relative-pseudo-coherent` (Tag 09UR), and
`definition-relative-pseudo-coherence` (Tag 09UI). The source lemma assumes Tor
independence; the node is its flat-base-change specialization. Flatness implies
that condition, and the node's own five-step proof is included in the docstring.

Clause-by-clause correspondence:

- Schemes X, S and S' are `{X S S' : Scheme.{u}}`. The arrows are
  `(f : X ⟶ S) (g : S' ⟶ S)`.
- Local finite type of f is `[LocallyOfFiniteType f]`; flatness of g is `[Flat g]`.
  No finite-type assumption on g or flatness assumption on f is imposed.
- X' is Mathlib's chosen scheme `pullback f g`; q is `pullback.fst f g`, and
  f' is `pullback.snd f g`. These are actual canonical projections, not free maps.
  The finite-type instance on f' is inferred from the finite-type instance on f
  by Mathlib's base-change instance, rather than added as a hypothesis.
- Every integer degree is `(m : ℤ)`, and every unbounded derived object is
  `(E : schemeDerivedCategory X)`.
- Relative m-pseudo-coherence is precisely
  `(hE : IsMPseudoCoherentRelativeTo f m E)`.
- The conclusion is `IsMPseudoCoherentRelativeTo (pullback.snd f g) m
  ((derivedPullback (pullback.fst f g)).obj E)`; thus it concerns the original
  degree m, the new base S', its structure morphism f', and exactly Lq*E.
- The second declaration states the node's “in particular” clause explicitly,
  replacing the fixed-degree hypothesis and conclusion by
  `IsPseudoCoherentRelativeTo f E` and
  `IsPseudoCoherentRelativeTo (pullback.snd f g)
  ((derivedPullback (pullback.fst f g)).obj E)`.
- There is no quasi-coherence, boundedness, Noetherian, separatedness, nonempty,
  quasi-compactness, finite-cover, or uniform-in-m cover condition.

The binder `[∀ Y : Scheme.{u}, HasDerivedCategory.{w}
(SheafOfModules.{u} (moduleRings Y.toRingedSpace))]` is the shared localization
infrastructure required by the recorded relative predicate, including all affine
ambient schemes and open restrictions it uses. It does not change the coefficient
category or assume a mathematical finiteness property. Both universe parameters
are explicit; `set_option autoImplicit false` prevents accidental extra binders.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, with morphisms
  `Scheme.Hom` written using the category notation.
- `def-pc-morphism-conventions` is a convention node; its local-finite-type
  constituent is `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, whose
  docstring and `Flat.iff_flat_stalkMap` identify it with stalkwise flatness.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies
  scheme pullbacks.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, the derived category of the shared
  `SheafOfModules` carrier, rather than its quasi-coherent full subcategory.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherentRelativeTo` and
  `AlgebraicGeometry.Scheme.IsPseudoCoherentRelativeTo`; their complete definitions
  were read, including the quantifiers over affine neighbourhoods, polynomial
  embeddings, and the all-integer-degree condition.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`:
  `AlgebraicGeometry.derivedPullback`, the actual transported canonical functor;
  its full interface and K-flat characterization were read.

The modules of available proof dependencies are imported privately, including the
Mathlib affine-basis, open/closed base-change, localization and ideal-sheaf files,
`MPseudoCoherentComplex`, `DerivedPullbackComposition`,
`FlatPullbackTorIndependent`, and `TorSymmetry`. Two proof nodes have no recorded
Lean module at the time of writing:
`lem-sfb-tor-independent-closed-pushforward-comparison` and
`lem-sfb-derived-pullback-m-pseudocoherent`. These are proof prerequisites only;
no import can yet name them. They are retained in the DAG and docstring, and the
maintainer can add their imports after they land. No missing statement notion
or unusable statement-dependency interface was found.

Edge cases checked before drafting: empty X, empty S' (and thus empty pullback),
zero E, m = 0, negative and positive m, identity g, non-Noetherian bases, infinite
affine covers, and degree-dependent witnesses. The predicates impose only local
conditions; none of these cases is excluded. In particular m-pseudo-coherence
alone does not require quasi-coherent cohomology in all degrees, so E is correctly
in the full derived category.

Searches for an existing statement:

- `msearch.py ... leanfinder "Flat base change preserves m pseudo coherent
  complexes relative to a scheme"`: eight results, led by
  `AlgebraicGeometry.Flat.isStableUnderBaseChange` and other ordinary flat/smooth
  morphism facts; none states relative pseudo-coherence of a derived complex.
- `msearch.py ... loogle '"PseudoCoherent"'`: zero results.
- `msearch.py ... grep 'pseudo.?coher|IsMPseudoCoherent'`: zero Mathlib results.
- `rg -n 'relative.*[Pp]seudo|[Pp]seudo.*[Rr]elative'` in `lean/WeilConjectures`
  and `lean/Sheaf`: the relative predicate, the closed-support theorem and affine
  embedding/gluing statements exist, but no flat-base-change theorem.
- `grep -rn 'lem-sfb-relative-pseudocoherence-flat-base-change'
  lean/WeilConjectures`: no hits.
- Exact proposed declaration names searched in Mathlib, upstream, Sheaf and
  `dag/lean_names_upstream.json`: no hits before this sandbox file was written.

There is no statement dispute, correction, new node, or dependency repair.

## Second reading by N8

A separate self-review pass reopened the node and the completed module. This is
not claimed as a second agent's independent review: the dispatch brief prohibits
starting other agents, and the maintainer supplies the independent review.

The projections were checked in order: the first projection is q to X, used only
inside `derivedPullback`; the second is f' to S', used as the relative structure
map. The degree m is unchanged. Only f is locally of finite type and only g is
assumed flat. The full derived category is used, with no quasi-coherent-property
binder. The second theorem has no fixed-degree hypothesis and states the full
all-m consequence. The definitions allow covers to vary with m and allow empty
schemes. The localization universe remains independent from the scheme universe.
No mathematical mismatch was found. The proof docstring was expanded to include
all five recorded steps, and all currently recorded proof modules were included.

Validation: the prescribed `scompile.py` compiled this module against the live
server library; final dry-run and delivery results are recorded by `deliver2.py`.
