## Worker report

The module `Sheaf.RingTheory.StablyFreeComplexLift` states
`DerivedCategory.exists_stablyFree_lift_mod_ideal`, with its only proof `sorry`.
It states Stacks Tag 0BCB, including the simultaneous free-term assertion.
Nothing is proved and no new definition is introduced.

Hypothesis and clause correspondence:

- The ring is `{R : Type u} [CommRing R]`, following the Stacks convention that
  rings are commutative with identity and the existing ring pseudo-coherence carrier.
- The ideal is `(I : Ideal R)`. The condition that every element of `1 + I` is
  invertible is `hunits : ∀ x : I, IsUnit (1 + (x : R))`.
- `K : DerivedCategory (ModuleCat.{max u v} R)` is an arbitrary object of `D(R)`.
  Both derived categories have explicitly bound `HasDerivedCategory` instances,
  with independent morphism universes `w` and `w'`; these choose the localizations.
- Pseudo-coherence is exactly `hK : IsPseudoCoherent K`. The existing definition
  gives a bounded-above complex of finite free modules and an isomorphism of its
  image under `Q` to `K`.
- `E` is a cochain complex over `R ⧸ I`. `hEbound : ∃ b : ℤ, E.IsStrictlyLE b`
  means its terms are zero above some bound, not merely its cohomology.
- `hEterms` requires, in every degree, both `Module.Finite` and
  `Module.IsStablyFree` over `R ⧸ I`. Mathlib's stabilization is by a finite free
  module, with the stabilized sum free. Since the module is also finite, that
  free sum is finite, giving exactly the finite ranks m,n of the node. Conversely
  the node's stabilization gives these two properties. The binary product is
  the binary direct sum of modules.
- `hE` says `Q.obj` of the termwise reduction of `Classical.choose hK` is
  isomorphic to `Q.obj E` in `D(R/I)`. The chosen representative is bounded above
  finite free, hence K-flat, so its reduction computes `K ⊗ᴸ R/I`. This imposes
  exactly the given derived-reduction condition; no representative or chain map
  is demanded as extra input. It is the same encoding used by the landed parent
  `Sheaf.RingTheory.MinimalFreeModel`, and is independent of the choice of model
  up to derived isomorphism.
- The conclusion existentially supplies one `P : CochainComplex ... ℤ`.
  `∃ b, P.IsStrictlyLE b` is boundedness above; the next conjunct requires finite
  stably free terms in every degree. `Nonempty (Q.obj P ≅ K)` means it represents
  `K`. The next conjunct is an isomorphism of complexes between its termwise
  reduction and `E`, so the differentials are respected, not just cohomology.
- The last conjunct, `∀ i : ℤ, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i)`,
  is the free-term assertion for every applicable degree of the SAME `P`.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: Mathlib leaf `DerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, and `DerivedCategory.Q`.
  These are localization at quasi-isomorphisms of integer-indexed cochain complexes.
- `def-pc-ring-pseudo-coherent-complex`:
  `Sheaf.RingTheory.RingPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`.
  Its full signature and existential finite-free-model definition were read.
- The original dependency `def-pc-derived-category` was read in full, including
  `AlgebraicGeometry.schemeDerivedCategory` in
  `Sheaf.AlgebraicGeometry.DerivedCategory`; it concerns sheaves on a scheme and
  cannot supply `D(R)`. The citation correction is recorded below.
- Standard notions: `Module.IsStablyFree` in
  `Mathlib.Algebra.Module.StablyFree.Basic` (constructor and docstring read),
  `ModuleCat.extendScalars` in `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
  (signature and docstring read), `Functor.mapHomologicalComplex`,
  `CochainComplex.IsStrictlyLE`, and `Ideal.Quotient.mk`. No private copies.

Edge cases checked: zero ring, zero complex, zero modules, rank zero, and `I = 0`
are admitted. `I = ⊤` satisfies the unit hypothesis only for the zero ring, which
is also admitted. No local, Noetherian, nontriviality, characteristic, or fixed
bound hypothesis is imposed. The degree index is all of `ℤ`; negative bounds and
unbounded negative tails are admitted. Module universes are `max u v`, so scalars
and their quotient fit the tensor construction; `v` is arbitrary. The free-term
clause is simultaneous and vacuous when no term is free. The only proof is sorry.

Searches (2026-10-11):

- `msearch.py ... leanfinder`: "Lift a bounded above complex of finite stably free
  modules from R/I representing derived base change of a pseudo coherent complex".
  Eight hits: local cohomology, flat factorization, adic completion, local-ring
  module freeness; none states this complex-lifting theorem.
- `msearch.py ... loogle`: `Module.IsStablyFree`. Twelve hits give the existing
  stably-free definition, equivalence/ULift/Shrink transport, projectivity, and
  stabilization constructors. These were used, not duplicated.
- `msearch.py ... grep`: `IsStablyFree|stably.free`. Ten hits in the basic
  stably-free module and invertible-module files, no complex-lifting theorem.
- `msearch.py ... leansearch`: "lifting bounded above complex finite stably free
  modules quotient ring pseudo coherent". Service unavailable: Internal Server
  Error. Other search kinds succeeded.
- `rg` on the source project for `IsPseudoCoherent`, `IsStablyFree`, and
  lifting/stably-free patterns: only module stabilization helpers and unrelated
  derived tensor constructions; no matching theorem. Searching the exact item
  id in `WeilConjectures` found no result.
- `rg` in `lean/Sheaf`: found and read `RingPseudoCoherent`, `MinimalFreeModel`,
  `ComplexLiftClassProjective`, and `AcyclicLift`. None is the item: the former
  two give its definition and a local-ring specialization, and the latter two
  are its general tool and an acyclic lifting tool.
- `rg` for `exists_stablyFree_lift_mod_ideal|StablyFreeComplexLift` in Mathlib,
  upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing name.

Source read at https://stacks.math.columbia.edu/tag/0BCB (the local Stacks tex
file is absent). The current online numbering is 15.77.5; the node records the
older number 15.75.6. The tag and lemma label agree. The declaration docstring
carries all the node's proof steps and the final Tag 0BC6 Nakayama argument.
The node's proof informally claims closure under all direct summands; finite
stably free modules need not have that closure. The required class condition is
instead the split two-out-of-three condition with first and middle terms in the
class, as in Tag 0BC3 and the signature of `complex_lift_class_projective`.
The docstring states that precise condition. This does not dispute the theorem;
the proof field is left unchanged because the citation correction does not force
an alteration of the mathematical proof route.

Validation: server `scompile.py` returned exit code 0, compiled in 2.3 seconds,
with no warnings. All binders and universes are explicit. Delivery dry run follows.

## Statement corrected

The old statement is the original node statement verbatim in
`statement_change.old_statement`. It cited `[def-pc-derived-category]` for `D(R)`;
that node defines the scheme-derived category of sheaves of modules, an ill-typed
citation for ordinary ring modules. The corrected statement replaces it with
`[def-weil-abstract-derived-category]` and cites
`[def-pc-ring-pseudo-coherent-complex]` at pseudo-coherence. No hypothesis or
conclusion is changed. This follows Stacks Tag 0BCB, which states the result over
a ring and its quotient. The correction retains the previous stage-1 correction
in `statement_change.previous`; only the citation text and `stmt_deps` change.

Every citer found by scanning `stmt_deps` and `proof_deps`:

- `lem-sc-perfect-local-pseudocoherent-free-model`: holds true. Its local-ring
  application with the maximal ideal and residue complex is unchanged, and its
  own statement already uses the corrected ring-derived category and ring
  pseudo-coherence dependencies. No citer is edited.


## Second reading by S1

I independently opened the node copy and StablyFreeComplexLift.lean, the two
statement dependencies and their declarations, the original scheme-derived
category declaration, and the sole actual citer. I read the corrected statement
first against Stacks Tag 0BCB and the upstream more-algebra.tex at
`lemma-lift-complex-stably-frees` (lines 18003–18029). The chapter is commutative
algebra; rings are commutative with identity. There is no standing Noetherian,
local, characteristic, or nonzero-ring assumption in this section.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

1. Ring R: `{R : Type u} [CommRing R]`; arbitrary commutative unital ring.
2. Ideal I: `(I : Ideal R)`; the quotient in every term is the same `R ⧸ I`.
3. Units in 1+I: `hunits : ∀ x : I, IsUnit (1 + (x : R))` enumerates exactly
   those elements. No stronger local-ring or henselian assumption is introduced.
4. K in D(R): `K : DerivedCategory (ModuleCat.{max u v} R)`. I read
   Mathlib DerivedCategory.Basic: `HasDerivedCategory` chooses a localization
   at quasi-isomorphisms, `Q` is its localization functor. The two instances
   permit arbitrary choices for R and R/I, with independent morphism universes.
5. K pseudo-coherent: `hK : IsPseudoCoherent K` uses the landed
   `Sheaf.RingTheory.RingPseudoCoherent` definition. Its body is an existential
   bounded-above finite-free cochain model with `Nonempty (Q.obj E ≅ K)`.
   It is precisely the dependency node, not a scheme notion or cohomological
   boundedness predicate.
6. E: `E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ` includes its
   differentials. `hEbound : ∃ b : ℤ, E.IsStrictlyLE b` is termwise vanishing
   above an arbitrary integer. I checked `isStrictlyLE_iff` in Mathlib's
   Embedding.CochainComplex, not just the similarly named derived `IsLE`.
7. Finite stably free E terms: `hEterms` requires `Module.Finite` and
   `Module.IsStablyFree` for every integer i. I opened StablyFree.Basic:
   the stabilizing module N is finite free and M × N is free. Finite M
   makes M × N finite as well, so both free modules have finite bases,
   giving exactly M ⊕ A^m ≅ A^n. Conversely that presentation satisfies
   the two predicates. Binary products are binary direct sums here.
8. E represents derived reduction: `hE` is a derived isomorphism between
   `Q.obj E` and Q of extension of scalars of `Classical.choose hK`.
   The chosen complex is bounded above finite free, hence K-flat. Ordinary
   termwise extension along `Ideal.Quotient.mk I` therefore computes the
   required derived tensor. I opened ModuleCat.ChangeOfRings: extendScalars
   is tensor with the quotient, and mapHomologicalComplex also tensors the
   differentials. This encoding agrees with the landed MinimalFreeModel;
   changing the finite-free representative does not change the condition.
9. One lifted P: the outer existential quantifies a cochain complex over R,
   followed by `∃ b, P.IsStrictlyLE b` and finite stably free terms at all i.
   Its bound is not required to equal the chosen bound of E.
10. P represents K: `Nonempty (Q.obj P ≅ K)` is an isomorphism in D(R).
11. Reduction is E as a complex: `Nonempty (...obj P ≅ E)` is an isomorphism
    in the cochain-complex category, not merely in D(R/I) or degreewise.
12. Simultaneous free-term assertion: the final
    `∀ i : ℤ, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i)`
    belongs to the same outer P existential. There is no per-degree choice
    of another P and no extra requirement on degrees where E is not free.

Edge cases: zero rings and zero modules/complexes are admitted; rank zero,
I = 0, and arbitrary characteristic are admitted. I = top is excluded by
hunits unless the ring is zero, exactly as in the source. Bounds can be zero
or negative and the negative tail can be infinite. The index is all integers,
so there is no nonempty-index or positive-degree restriction. There is no
scheme or empty-scheme parameter. The module universe `max u v` accommodates
both tensor factors and v is arbitrary; no mathematical module is lost by
lifting its carrier to that universe. Localization universes w and w' are
explicitly bound. No variable is implicitly introduced.

Independent searches (2026-10-11), with alternative wording:

- LeanFinder via msearch: "Jacobson radical quotient lifting projective cochain
  complex with prescribed reduction": eight results, including
  `CochainComplex.isKProjective_of_projective` and projective resolutions.
  They establish general projective-complex facts, not this lifting theorem.
- Loogle via msearch: `ModuleCat.extendScalars`: twelve results, the tensor
  functor and its adjunction/composition properties; used the existing functor.
- Grep via msearch: `lift.*complex|complex.*lift|Jacobson`: returned Jacobson
  algebra and complex-embedding results, no match for this theorem.
- Direct rg over Mathlib homological algebra, upstream WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json with
  `stablyFree|stably_free|stably free|lift_mod_ideal|lift.*[Cc]omplex|[Cc]omplex.*lift`:
  found existing module stabilization helpers, the general class lifting
  theorem, and MinimalFreeModel. I opened the latter two signatures: neither
  states this theorem. The general tool needs a class and closure/surjectivity
  hypotheses; MinimalFreeModel assumes a local ring and prescribed residue
  ranks. No duplicate of this item was found.
- LeanSearch: "prescribed quotient complex lift through ideal contained in
  Jacobson radical": Internal Server Error, recorded unavailable; the other
  search kinds and direct source inspection succeeded.

Correction/citers: the recorded citation correction changes no mathematical
clause of Tag 0BCB. I opened `schemeDerivedCategory`: it uses sheaves of
modules on a scheme and cannot supply this D(R). Its replacement and the
ring pseudo-coherence dependency are appropriate. A complete rg of the item
id in dag/nodes finds just one node citing it in stmt_deps/proof_deps:
`lem-sc-perfect-local-pseudocoherent-free-model`, holds true. Its step 2
applies the theorem with I the maximal ideal and finite free E terms; the
same P is finite free in every degree. No second actual citer exists.
Occurrences in the item's own metadata and the general tool's created and
statement_change records are not dependency citations. No citer is edited.
There are no new definition nodes or dependency modules in this delivery.

H5–H9: no definition or private copy is added; the only proof is the named
sorry theorem. Both docstrings cite Tag 0BCB and the exact blueprint id.
The declaration docstring supplies all proof steps, including stable lifting,
Nakayama surjectivity, pseudo-coherent model choice, and the simultaneous
free-term argument. Its precise split two-out-of-three property correctly
replaces the node proof's overbroad informal direct-summand claim; that claim
is not needed and is not asserted in Lean. All imports serve the signature,
all lines meet the width limit, and there is no file-local notation/instance.

Mismatches and changes: no mathematical mismatch found. The node's
lean.statement was whitespace-normalized rather than literally copied;
I replaced it with the verbatim multiline signature from the file, checking
that whitespace normalization gives exactly the prior string. Lean source,
mathematical statement, and dependencies needed no change.
