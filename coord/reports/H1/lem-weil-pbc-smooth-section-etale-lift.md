## Worker report

The module `lean/Sheaf/Paper/SmoothSectionEtaleLift.lean` states
`AlgebraicGeometry.exists_etale_lift_of_smooth` for commutative rings `A` and `B`, an
`A`-ideal `J`, an `A`-algebra map `σ : B →ₐ[A] A ⧸ J`, and smoothness of the
contravariant affine scheme morphism induced by `algebraMap A B`.  Its conclusion
quantifies a target ring `A'`, its commutative-ring and `A`-algebra structures,
an étale affine scheme morphism, an `A`-algebra isomorphism witness represented by
`Function.Bijective α` from `A ⧸ J` to `A' ⧸ J.map (algebraMap A A')`, and an
`A`-algebra lift `tildeσ` satisfying the quotient equality.  The proof is `sorry`
as required for stage 2.

The Lean renders each clause as follows.  The base rings and structures are
`(A B : Type u) [CommRing A] [CommRing B] [Algebra A B]`; the ideal and section are
`(J : Ideal A) (σ : B →ₐ[A] A ⧸ J)`; smoothness is
`hB : Smooth (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)`.  The
existential target is `∃ (A' : Type u) (hA' : CommRing A') (hAlg : Algebra A A'),`
with these witnesses installed by the two `letI` binders.  Étaleness is
`Etale (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A A')).op)`.  The quotient
comparison is `α : A ⧸ J →ₐ[A] A' ⧸ (J.map (algebraMap A A'))`, with
`Function.Bijective α`; the lift is `tildeσ : B →ₐ[A] A'`, and its compatibility is
`Ideal.Quotient.mk (J.map (algebraMap A A')) ∘ tildeσ = α.toRingHom ∘ σ.toRingHom`.

Dependencies used are the existing Mathlib declarations recorded by the DAG:
`AlgebraicGeometry.Smooth` from `Mathlib.AlgebraicGeometry.Morphisms.Smooth` and
`AlgebraicGeometry.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
`Ideal.Quotient.mk` and the quotient notation are Mathlib primitives from
`Mathlib.RingTheory.Ideal.Quotient.Defs`; no project dependency declaration was
needed.

Edge cases checked before writing include `J = ⊥`, `J = ⊤`, the zero ring, the
zero-rank/free rank-zero situation implicit in the source proof, and the empty
spectrum.  The universe uses one `u` for both rings and the target ring, so no
smaller independent universe makes the assertion vacuous.

Searches made: `msearch.py ... leanfinder "smooth algebra section modulo ideal lifts
to etale neighbourhood"` returned only standard étale lifting primitives and no
matching theorem; `msearch.py ... loogle "AlgebraicGeometry.Smooth,
AlgebraicGeometry.Etale"` found `AlgebraicGeometry.Etale.instSmooth`; the grep
search for `lift.*section|exists.*Etale` in Mathlib algebraic geometry returned no
hits; `rg` over the project and upstream source found no existing declaration of
this lemma.  The dependency-node records were read and their full Mathlib
signatures checked.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the stage-2 dry run is the verification performed here.

## Second reading by H1

Read the sandbox node, its ten proof steps, both statement-dependency nodes, and
Mathlib's recorded declarations directly. Read Stacks More on Algebra,
`lemma-lift-section-smooth-morphism` (07M7), including its full proof, at
`/home/ubuntu/c1-stacks-review/more-algebra.tex:2139` (the local literature copy).
The chapter introduction imposes no additional ring hypotheses; the lemma concerns
arbitrary commutative rings and arbitrary ideals, not just henselian pairs.

Object-by-object, hypothesis-by-hypothesis, conclusion-by-conclusion checklist:

- Commutative base ring A: `(A : Type u) [CommRing A]`. Exact.
- Ideal J of A and quotient map π: `(J : Ideal A)`, `A ⧸ J`, and the
  canonical quotient algebra structure; π is implicit because it has no independent
  choice and is not separately used in the conclusion. Exact.
- Commutative A-algebra B: `(B : Type u) [CommRing B] [Algebra A B]`. Exact.
- Smooth Spec B → Spec A: `hB : Smooth (Scheme.Spec.map
  (CommRingCat.ofHom (algebraMap A B)).op)`. The dependency
  def-sbc-smooth-morphisms records Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  `AlgebraicGeometry.Smooth`; its `smooth_appLE` field asserts smooth ring maps
  on every pair of affine opens. Stacks 02H6 identifies this with the node's
  infinitesimal lifting form; the item already uses the affine smooth form. Exact.
- A-algebra homomorphism σ to A/J: `(σ : B →ₐ[A] A ⧸ J)`. Its `commutes`
  field is precisely the source diagram's commutativity. No extra surjectivity
  hypothesis: surjectivity follows from A-linearity and A → A/J. Exact.
- Existential ring map A → A': `∃ (A' : CommAlgCat.{u} A)`, with canonical
  `algebraMap A A'`. Opened CommAlgCat.Basic: the bundle contains only a carrier,
  commutative-ring structure, and A-algebra structure, and `CommAlgCat.of` bundles
  any such algebra. It adds no condition. Replaces separate structure witnesses
  and their prohibited `letI` binders without changing the mathematical assertion.
- Étale Spec A' → Spec A: `Etale (Scheme.Spec.map
  (CommRingCat.ofHom (algebraMap A A')).op)`. The dependency def-weil-etale-morphism
  records Mathlib.AlgebraicGeometry.Morphisms.Etale, `AlgebraicGeometry.Etale`;
  opened its `etale_appLE` field and the flat/formally-unramified/lfp equivalence.
  These are the node's notion, not a finite étale specialization. Exact.
- Extended ideal JA' and quotient map q: `J.map (algebraMap A A')` and
  `Ideal.Quotient.mk (J.map (algebraMap A A'))`. `Ideal.map` is the ideal generated
  by the images, hence exactly JA'. Exact.
- Induced quotient isomorphism α: `∃ (α : A ⧸ J →ₐ[A]
  A' ⧸ (J.map (algebraMap A A'))), Function.Bijective α`. A bijective algebra
  homomorphism is an algebra isomorphism, with no chosen inverse needed here.
  This does not allow an unrelated isomorphism: for every a ∈ A,
  `α.commutes a` forces α(π(a)) = q(algebraMap A A' a), and π is surjective.
  Thus α is necessarily the induced map required by the node. Exact.
- A-algebra lift and compatibility: `∃ (tildeσ : B →ₐ[A] A'),
  Ideal.Quotient.mk (J.map (algebraMap A A')) ∘ tildeσ =
  α.toRingHom ∘ σ.toRingHom`. Equality of the underlying functions is precisely
  q ∘ tildeσ = α ∘ σ, since the maps already carry their algebra structures. Exact.
- Quantifier order: A, B, J, σ, smoothness hypothesis; then A' and its étaleness,
  quotient isomorphism, and compatible lift. No further assumptions or conclusion
  clauses. Exact.

Edge cases: J = 0 is covered (σ itself gives a lift with A' = A);
J = A is covered (the zero A-algebra is an étale neighbourhood with zero quotient).
The zero ring and empty spectra are allowed by CommRing and the affine-local
Smooth/Etale predicates; no Nontrivial assumption appears. No index set, rank,
or characteristic is constrained in the statement; the proof docstring allows
rank n = 0. The arbitrary universe u contains both input carriers and the output
carrier. Using one ambient universe matches Scheme.{u} and excludes no pair of
rings: choose a common larger ambient universe. A' can be constructed in that
same universe by the finite presentations and localizations in the source proof.
No unbound variable or independent smaller test-object universe occurs.

Independent searches (different phrasing from the worker):

- LeanSearch through msearch.py: “smooth algebra homomorphism to quotient lifts
  after etale base change inducing quotient isomorphism”. Service returned
  unavailable (Internal Server Error); no absence verdict based on this service.
- LeanFinder through msearch.py: “a morphism from a smooth algebra to a quotient
  ring extends to an etale algebra with unchanged quotient”. Eight candidates,
  including StandardEtalePair.lift, square-zero root lifting, and
  RingHom.IsStandardSmooth.exists_etale_mvPolynomial. Read returned signatures:
  these respectively assume a standard pair/root, a square-zero ideal, or give
  polynomial étale charts; none asserts 07M7 for an arbitrary ideal and section.
- Loogle: `Algebra.Smooth, Ideal.Quotient` rejected the latter identifier;
  follow-up `Algebra.Smooth, Algebra.Etale` returned only
  Algebra.Etale.instSmooth and Algebra.Etale.iff_formallyUnramified_and_smooth,
  neither an existence/lifting statement.
- rg of Mathlib RingTheory/Smooth, Etale and RingHom for
  `etale.*lift|lift.*etale|smooth.*section|section.*smooth` and
  `section|neighbourhood|neighborhood`: formal lifting results and finite-algebra
  fibre-splitting étale neighbourhoods, no matching general statement.
- rg with the first expression over WeilConjectures and repository lean/Sheaf:
  geometric purity/étale-site lifting and smooth charts only. Also searched the
  proposed declaration and blueprint id in dag/lean_names_upstream.json and both
  libraries: no existing statement or name collision. No second notion defined.

Mismatches and repairs: the worker's docstring compressed the ten-step proof into
one sentence (H8); replaced it by all ten steps, including their dependency-node
names and the conormal, free-case, symmetric-algebra, and base-change arguments.
The worker used `letI` binders prohibited by the statement conventions; replaced
its existential carrier/structure witnesses by Mathlib's CommAlgCat bundle and
added the used import. Added the conventional copyright header and moved the
module docstring immediately after imports. Kept all hypotheses, maps and
conclusion clauses that were already right. Updated lean.statement verbatim to
the resulting signature. No node statement correction, new definition node,
or dependency module was necessary. The only theorem proof remains `sorry`;
there are no definitions, private copies, local notation, local instances, or
hidden proof obligations in this delivery.

Validation: scompile.py compiled the revised sole module cleanly in 1.8 seconds
(exit 0, no warnings). Checked the full signature, explicit universe binder,
and all module lines (at most 100 characters) by eye and mechanically.
