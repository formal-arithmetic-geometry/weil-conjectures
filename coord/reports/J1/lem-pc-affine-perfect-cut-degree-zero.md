## Worker report

The theorem `DerivedCategory.affine_perfect_cut_degree_zero` states the affine
bounded-above finite-free, degree-zero specialization of Stacks Tag 0A1U.
`ModuleCat.cohomologyBaseChange` defines its canonical comparison without any sorry.
The theorem is the only postponed proof; its docstring gives all three proof steps.

Hypotheses and clauses, matched individually:

- The commutative ring is `{R : Type v} [CommRing R]`. Stacks uses commutative rings.
- The prime is `(p : Ideal R) [p.IsPrime]`; its residue field is `p.ResidueField`,
  Mathlib's residue field of `Localization.AtPrime p` (ResidueField/Ideal.lean:33).
- The complex is `K : CochainComplex (ModuleCat.{v} R) ℤ`, with the standard upward shape.
- Bounded above is `hbounded : ∃ b : ℤ, K.IsStrictlyLE b`; the integer bound is unrestricted.
- Every term is finite free via `hfree : ∀ i, Module.Free R (K.X i) ∧ Module.Finite R (K.X i)`.
- The comparison surjectivity is `Epi (ModuleCat.cohomologyBaseChange ... K 0)`.
  Epi in ModuleCat is equivalent to surjectivity. The map is the adjoint of the
  cohomology map induced by the extension-restriction unit, followed by the exact
  restriction homology comparison. Its value on a tensor generator is the scalar
  multiple of the corresponding cycle class. The left-sided tensor convention is
  identified with the node's convention by tensor symmetry. Because K is bounded above
  and free, termwise extension computes its derived tensor with the residue field.
- Shrinking is `∃ f : R, f ∉ p`, with ring `Localization.Away f`.
- Extension of scalars is `RingTensorCohomology.extend R (Localization.Away f)`.
- The first conjunct is an isomorphism in D(R_f), using `Q.obj` and `Nonempty`.
  Its summands are the genuine complex truncations `.truncLE 0` and `.truncGE 1`,
  mapped by Q, and `⊞` is the binary biproduct. These represent the derived truncations.
- The second conjunct supplies a complex P and integer b, with `P.IsStrictlyGE 1`,
  `P.IsStrictlyLE b`, finite projective terms, and an isomorphism from the positive
  truncation to `Q.obj P`. This is the bounded finite-projective representative clause.
- The third conjunct states `.IsPerfect` for that same positive truncation, using
  the existing ring-module definition `DerivedCategory.IsPerfect`.
- The last conjunct quantifies over every R_f-module N and says the derived tensor
  with N in degree zero `.IsGE 1`. For the standard derived t-structure this means
  exactly vanishing cohomology in all degrees below 1, the half-infinite Tor-amplitude.
- The `HasDerivedCategory.{v}` family supplies chosen localizations for D(R_f).
  It is structure needed to name these categories, with the standard choice available
  for every ModuleCat; it places no mathematical restriction on R or f. All universes
  and variables are explicitly bound; `autoImplicit` is false. The arbitrary ring
  universe v covers modules in every chosen ambient universe.

Dependency declarations used:

- `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`; their complete signatures
  and docstrings were read. The standard t-structure and complex truncations come from
  Mathlib's DerivedCategory.TStructure and Embedding.CochainComplex (via Perfect).
- `def-pc-ring-tensor-cohomology`: Sheaf.Algebra.Homology.RingTensorCohomology,
  `RingTensorCohomology.extend`; its complete module was read. It uses the additive
  extension-of-scalars functor termwise and agrees with the node's tensor convention.
- `def-pc-perfect-ring-complex`: WeilConjectures.CategoryTheory.DerivedCategory.Perfect,
  `DerivedCategory.IsPerfect`; its docstring and signature were read, including the
  preceding CommRing and HasDerivedCategory binders. This is a full existing definition.
- `def-pc-module-cohomology-base-change`: delivered module
  Sheaf.Algebra.Homology.ModuleCohomologyBaseChange, `ModuleCat.cohomologyBaseChange`.
  It uses `ModuleCat.extendRestrictScalarsAdj`, `ShortComplex.mapNatTrans`,
  `ShortComplex.homologyMap`, and `ShortComplex.mapHomologyIso` for exact restriction.
  Their source signatures were inspected. No proof or data is postponed in this definition.

Edge cases checked: K=0 permits f=1 and P=0; a complex supported entirely at nonpositive
indices has zero positive truncation. A complex in degree 1 has zero source and target
H⁰ so the hypothesis is automatic and the conclusion holds. No lower bound on K is
assumed: an unbounded negative tail is permitted. The prime ideal excludes the zero
ring automatically; no extra Nontrivial hypothesis is introduced. Empty finite bases
and zero-rank finite free modules are allowed. No constraint b≥1 is imposed on a zero
representative. Arbitrary characteristic and non-Noetherian commutative rings are allowed.

Searches (actual service results are in searches.jsonl and the new nodes):

- msearch leansearch: cohomology base change map tensor homology complex localization
  split truncation; service unavailable (Internal Server Error).
- msearch leanfinder: bounded above finite free complex splits truncation locally when
  degree zero cohomology base change is surjective; eight hits concerning truncation,
  K-projectivity and split maps, none the stated theorem.
- msearch grep: `baseChangeHomology|homologyBaseChange|better.cut|affine_perfect_cut`;
  no Mathlib hits.
- msearch leansearch and leanfinder: perfect complex over a commutative ring bounded
  finite projective modules and cohomology base change map; LeanSearch unavailable,
  LeanFinder eight K-projective/Tor hits, no exact definition or theorem.
- msearch grep: `cohomologyBaseChange|IsPerfect|homologyBaseChange` in Algebra/Homology;
  no Mathlib hits.
- rg over WeilConjectures: no target id or affine cut theorem; the existing general
  `DerivedCategory.IsPerfect` was found in CategoryTheory/DerivedCategory/Perfect.lean:88.
  Broader comparison-map searches found sheaf/etale comparisons, not this module map.
- rg over lean/Sheaf: scheme-perfectness and RingTensorCohomology were found; no
  nonflat module cohomology-base-change map or affine cut theorem. The flat-only
  RingTensorCohomology.baseChangeMap requires a flat coefficient map and cannot define
  the residue-field comparison here.
- DAG searches and blueprint_refs.py search 'cohomology base change' (0 blueprint hits)
  and 'perfect' were checked. The Poincare-duality perfect-point node is restricted to
  its fixed coefficient setting and has no Lean record; the scheme-perfect node uses
  sheaves. No DAG node carries general arbitrary-ring perfectness. The upstream name
  list and repository source were checked for declaration-name collisions.

Source inspected: /home/ubuntu/c1-stacks-review/more-algebra.tex, lines 19743–19825,
Lemma better-cut-complex-in-two and its proof. The local repository's literature copy
is absent, so this available Stacks checkout was read. The lemma's general i was
specialized to zero, and its finite-free model proof gives precisely the stronger
representative clause already in this node. No statement is disputed.

Server validation: ModuleCohomologyBaseChange compiled alone in 2.3 s; both delivered
modules compiled together in 2.5 s with no error or warning. The prescribed combiner
concatenates global universe declarations, so the two files use different universe
names u and v to permit that combined check.

## New nodes

`def-pc-module-cohomology-base-change` defines the ordinary canonical cohomology
base-change map for any commutative coefficient algebra, exactly the map in Tag 0A1U
when the complex is bounded above and free. Search results above show that the landed
flat-only map cannot supply this comparison. The new definition uses the existing
adjunction and exact restriction, and its data has no sorry.

`def-pc-perfect-ring-complex` records the existing upstream `DerivedCategory.IsPerfect`
for arbitrary commutative rings. It adds no Lean module and does not duplicate a notion.
Its source is the ring-perfect conclusion and bounded finite-projective model of Tag
0A1U. The searched DAG notions are scheme-perfectness and fixed-coefficient point
perfectness; neither provides the arbitrary-ring statement needed here.

## Statement corrected

Original statement, verbatim:

> Let R be a ring, let p be a prime ideal of R, and let K be a bounded-above complex of finite free R-modules. Assume that the canonical map H^0(K) tensor_R kappa(p) to H^0(K tensor_R^L kappa(p)) is surjective. Then there is f not in p such that, in the derived category D(R_f), K tensor_R R_f is isomorphic to tau_{<=0}(K tensor_R R_f) direct-sum tau_{>=1}(K tensor_R R_f), and tau_{>=1}(K tensor_R R_f) is represented by a bounded complex of finite projective R_f-modules in degrees at least 1; in particular tau_{>=1}(K tensor_R R_f) is perfect [def-pc-perfect-complex] of Tor-amplitude in [1,infinity).


The original statement cited `[def-pc-perfect-complex]` for a perfect object of D(R_f),
but that definition takes an object of D(O_X) for a scheme X. It cannot be applied to
this ring-module object. The correction replaces this reference with
`[def-pc-perfect-ring-complex]`, names the canonical map's new definition node, and
spells out 'commutative ring', the convention of the Stacks source. Every hypothesis
and conclusion remains mathematically the same. The original statement is preserved
verbatim in statement_change.old_statement; proof and proof_deps are unchanged.

The only actual citer (checking stmt_deps/proof_deps, rather than blueprint via fields)
is `lem-sc-perfect-cut-complex-degree-zero`: holds true. Its step 2 applies the affine
cut to a commutative coordinate ring and then sheafifies the positive perfect complex;
the affine bounded-projective comparison to scheme-perfectness is the same as before.
No citer is edited and no blueprint unit statement is changed.

## Second reading by J1

I reread the corrected node statement, its source (Stacks Tag 0A1U, Lemma
better-cut-complex-in-two), and both delivered modules declaration by declaration.
The objects and clauses match as follows:

- `R` is `{R : Type v} [CommRing R]`; this is exactly the commutative-ring
  convention of the source, with no Noetherian, domain, or characteristic assumption.
- `p : Ideal R` with `[p.IsPrime]` is the prime and `p.ResidueField` is its
  residue field.  The prime is introduced before the complex and no nontriviality
  hypothesis is added.
- `K : CochainComplex (ModuleCat.{v} R) ℤ` is the cochain complex; the hypotheses
  `∃ b, K.IsStrictlyLE b` and `∀ i, Module.Free R (K.X i) ∧ Module.Finite R (K.X i)`
  render bounded-above and finite-free termwise exactly.
- The fibre hypothesis is `Epi (ModuleCat.cohomologyBaseChange
  (B := p.ResidueField) K 0)`, using the new canonical base-change definition.
  Its source is the extension-of-scalars map on homology followed by the exact
  restriction homology comparison, so it is the stated map from H⁰(K) tensor the
  residue field to H⁰ after tensoring.
- The existential `∃ f : R, f ∉ p` is the required shrinking.  Every subsequent
  object uses `Localization.Away f`, exactly R_f, and
  `RingTensorCohomology.extend R (Localization.Away f)` is the scalar extension.
- The first conjunct is `Nonempty` of the derived-category isomorphism from the
  extended complex to `Q.obj truncLE 0 ⊞ Q.obj truncGE 1`, preserving both
  truncation bounds and the direct-sum conclusion.
- The second conjunct quantifies one complex `P` and integer bound `b`, requires
  `IsStrictlyGE 1`, `IsStrictlyLE b`, finite projective terms, and an isomorphism
  from the positive truncation to `Q.obj P`; this is the bounded finite-projective
  representative in degrees at least one.
- The third conjunct applies the ring-module `DerivedCategory.IsPerfect` to that
  same positive truncation, and the final universal conjunct states derived tensor
  with every `R_f`-module is `IsGE 1`, exactly the Tor-amplitude clause.

The `HasDerivedCategory` binder is only the chosen derived-category infrastructure
needed by `Q`; it introduces no mathematical restriction. Universes are shared
(`v`) throughout the ring, modules, localization, and test modules. Empty or zero
complexes, empty finite bases, degree zero, arbitrary characteristic, and
non-Noetherian rings remain admitted; the prime hypothesis excludes the degenerate
zero-ring case in the usual way. No index-set or lower-bound hypothesis was added.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` for the theorem and for a
cohomology-base-change declaration. No exact match exists. The only perfectness
notion suitable for this ring-derived category is the existing
`DerivedCategory.IsPerfect` recorded by `def-pc-perfect-ring-complex`; the existing
flat-only comparison map cannot serve the residue-field map, so
`def-pc-module-cohomology-base-change` is necessary. The source and dependency node
records were also reread; no further mismatch was found. The worker's correction
from the scheme perfectness definition to ring perfectness is retained, and the
citer `lem-sc-perfect-cut-complex-degree-zero` still holds because it uses precisely
this affine conclusion.
