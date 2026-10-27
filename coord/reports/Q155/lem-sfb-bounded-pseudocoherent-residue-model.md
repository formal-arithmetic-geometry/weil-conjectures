## Worker report

The module `Sheaf.RingTheory.BoundedPseudoCoherentResidueModel` states
`DerivedCategory.exists_bounded_finiteFree_residue_model`. Its single proof is
`sorry`, with the complete eight-step DAG proof in the declaration docstring.
There are no definitions, auxiliary theorems, new nodes, dependency repairs, or
statement corrections. The node changes only in `lean`.

I read Stacks `more-algebra.tex`, Tag 0BYP
(`lemma-lift-bounded-pseudo-coherent-to-perfect`, lines 20000 ff.), Tag 0BCC
(`lemma-lift-pseudo-coherent-from-residue-field`, lines 19548 ff.), and Tag 0BCD
(`lemma-lift-perfect-from-residue-field`, lines 19594 ff.). These give precisely
the local model required by the node. The current latest blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` was read; this is a
supporting local-algebra node, not the unit's statement.

Hypotheses and clauses, matched individually:

- A commutative ring is `{R : Type u} [CommRing R]`; the prime ideal is
  `(p : Ideal R) [p.IsPrime]`.
- The object of D(R) is `(K : DerivedCategory (ModuleCat.{max u v} R))`.
  `hK : IsPseudoCoherent K` uses the dependency's exact upstream definition,
  whose witness is a bounded-above finite-free complex representing K.
- Boundedness below is `hbelow : ∃ c : ℤ, ∀ i : ℤ, i < c →
  IsZero ((homologyFunctor (ModuleCat.{max u v} R) i).obj K)`.
- The residue field is literally `FractionRing (R ⧸ p)` as requested, with the
  canonical ring map `(algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp
  (Ideal.Quotient.mk p)`.
- Derived tensor with the residue field is `Functor.mapHomologicalComplex
  (ModuleCat.extendScalars ...) (ComplexShape.up ℤ)` applied to
  `Classical.choose hK`. This is the actual representative supplied by the
  recorded definition, not a new definition or an arbitrary object. It is
  bounded above finite free, so it computes the prescribed derived tensor.
  This use of a representative of a given K is the established upstream
  interface also used in `exists_unique_minimalFreeModel`; its derived tensor
  is independent of that representative.
- The integer a is `(a : ℤ)`. The vanishing hypothesis `hresidue` says the
  residue cohomology objects are zero for every `i < a`. This renders
  dimension zero, rather than using natural-valued finrank alone, which could
  wrongly accept an infinite-dimensional vector space. Every residue
  cohomology is in fact finite dimensional for a pseudo-coherent object,
  independently of this hypothesis, as recorded in proof step 1.
- The first conjunct is `∀ i : ℤ, Module.Finite (FractionRing (R ⧸ p)) ...`,
  exactly finiteness of all the d_i. The numbers d_i themselves are written
  inline as `Module.finrank (FractionRing (R ⧸ p)) ...`; because the first
  conjunct establishes finite dimension this is the actual dimension.
- The principal neighbourhood is `∃ f : R, f ∉ p`; `Localization.Away f`
  is R[1/f] with its canonical `algebraMap`.
- The upper endpoint is `∃ b : ℤ, a ≤ b`.
- The model F is a cochain complex of `ModuleCat.{max u v}
  (Localization.Away f)`. The clause `∀ i, i < a ∨ b < i → IsZero (F.X i)`
  says exactly that its terms outside [a,b] vanish; thus it is bounded.
- For every `a ≤ i` and `i ≤ b`, the term is isomorphic to
  `ModuleCat.of (Localization.Away f) (ULift.{v} (Fin d_i → Localization.Away f))`.
  A finite function module is the finite direct sum of d_i copies. `ULift`
  only places these standard modules in the common module universe.
- The final `Nonempty (Q.obj F ≅ Q.obj (...))` is an isomorphism in D(R_f).
  The right side is the canonical termwise extension of the same bounded-above
  finite-free representative of K along `algebraMap R (Localization.Away f)`;
  it therefore is the derived tensor K ⊗ᴸ R_f specified in the node. The
  statement does not replace this comparison by cohomology isomorphisms.

`HasDerivedCategory.{w}` and `HasDerivedCategory.{w'}` are the selected
localizations of the module categories, as required by the derived-category
statement dependency. The target family is bound for every f so it is available
for the existential f; these are only choices of derived-category models,
not mathematical restrictions on R. Ring and module size universes are explicit
and independent (`u`, `v`), as are the source and target morphism sizes.
No file-local notations, instances, private definitions, lets, or auto-implicits
occur in the statement.

Statement dependencies used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; cohomology is
  `DerivedCategory.homologyFunctor` from the associated HomologySequence API.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`, read with its full witness signature.

The existing proof dependencies are imported without `public`, and were read:
`WeilConjectures.RingTheory.MinimalFreeModel` /
`DerivedCategory.exists_unique_minimalFreeModel`;
`Sheaf.Algebra.Homology.FreeComplexResidueDegreeCancellation` /
`CochainComplex.exists_localized_homotopyEquiv_zero_degree`;
`Mathlib.Algebra.Homology.DerivedCategory.KProjective` /
`CochainComplex.IsKProjective.Qh_map_bijective`;
`Mathlib.Algebra.Module.LocalizedModule.Exact` / `LocalizedModule.map_exact`;
and `Mathlib.RingTheory.Localization.AtPrime.Basic` / `Localization.AtPrime`.
The localization-away definition is publicly imported because the statement
uses it directly. All seven proof dependencies have their existing declaration
interfaces; none is copied into this module.

Edge cases checked before drafting: K = 0 permits b = a and all zero-rank
terms; the interval endpoint b = a remains allowed; no relation between the
cohomological lower bound c and a is imposed (the proof cuts at min(a,c)-1).
The proof retains the original a. Zero-dimensional cohomology is expressed as
zero objects, never inferred just from a possibly infinite finrank. Nonreduced
rings and arbitrary characteristics are allowed; no noetherian, flatness, or
regularity hypothesis is added. Empty products of denominators are 1. The zero
ring has no prime ideal, so introduces no inconsistent residue-field case.
No STATEMENT-DISPUTED issue was found.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A bounded below pseudo coherent complex has near a
  prime a bounded finite free model with ranks the dimensions of derived
  residue field cohomology"`: eight hits, including module free-locus results
  and `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, `isGE_Q_obj_iff`,
  `isLE_Q_obj_iff`, `isGE_iff`. None supplies finite free residue-rank models.
- `msearch.py ... leansearch "A bounded below pseudo coherent complex has a
  finite free model near a prime with residue field cohomology ranks"`:
  eight hits, including module rankAtStalk/freeLocus facts, quasi-finite fibre
  finiteness, a sheaf finite-presentation fact, and derived bounded models.
  None states this result.
- `msearch.py ... loogle '"PseudoCoherent"'`: zero hits.
- `msearch.py ... grep 'pseudo.?coherent|minimal.*free.*complex'`: zero hits.
- `rg` on `lean/WeilConjectures/RingTheory` for bounded pseudo-coherence,
  residue models, and residue ranks found `MinimalFreeModel` and unrelated
  polynomial residue models, not this near-prime theorem. `rg` for the item id
  in `lean/WeilConjectures` found no declaration. Searches in `lean/Sheaf`
  found scheme-level fibre models and distinct ring results, not this theorem.
- The proposed full declaration name was searched in Mathlib, WeilConjectures,
  Sheaf, and `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py Q155 lem-sfb-bounded-pseudocoherent-residue-model
<module>` compiled both the module-mode sandbox and its actual library module
cleanly (2.4 s and 2.3 s). The initial compile's application syntax and excess
closing parenthesis were fixed; no semantic adjustment was needed.

## Second reading by Q155

I reopened the node and the completed module for a separate clause-by-clause
pass. This is the same worker's second pass: the dispatcher explicitly forbids
starting other agents; the maintainer supplies the independent delivery review.
The ring, prime, derived object, pseudo-coherence and existential cohomological
lower bound all occur. Residue extension is along the canonical quotient and
fraction-field map. I checked that hresidue asserts vanishing of the object
and that finiteness is concluded for every degree, without assuming finiteness.
The existential witnesses f, b, F have f outside p, b at least the given a,
zero terms outside the closed interval, and the exact residue-cohomology rank
inside the interval. The final comparison is in D(R_f) and uses the chosen
finite-free representative on both sides of scalar extension. All variables
and universes are bound explicitly. There are no strengthened hypotheses such
as noetherianity or boundedness below of the representative's terms. No
mismatch was found and no statement change was required. The node's lean
signature is extracted verbatim from the final source.
