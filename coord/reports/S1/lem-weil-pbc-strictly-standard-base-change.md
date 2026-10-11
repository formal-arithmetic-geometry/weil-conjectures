## Worker report

The module `lean/Sheaf/RingTheory/StrictlyStandardBaseChange.lean` states
`Algebra.standardElements_baseChange`, with a `sorry` proof, covering both cases of
lem-weil-pbc-strictly-standard-base-change. The original node is copied with only `lean`
changed. No new definitions, dependency modules, or statement corrections are needed.

Source checked: [Stacks Lemma 07CC](https://stacks.math.columbia.edu/tag/07CC).
The local `literature/stacks-project/smoothing.tex` is absent on this machine; the official
online tag supplies the statement and proof. Both cases agree with the node.

Hypothesis and clause correspondence:

- The rings R, A, R' are `{R : Type u} {A : Type v} {R' : Type w}` with the three
  `CommRing` instances. All universes are explicitly declared and independent.
- The ring maps R → A and R → R' are `[Algebra R A]` and `[Algebra R R']`. The second
  map is arbitrary: no finiteness, flatness, injectivity, or characteristic condition.
- Finite presentation of R → A is `[FinitePresentation R A]`.
- The base-changed algebra is `R' ⊗[R] A`, with its canonical left R'-algebra structure.
  This is precisely the source's A' = A ⊗_R R', written in the customary Mathlib order:
  `Algebra.TensorProduct.commRight R R' A` is an R'-algebra isomorphism onto
  `A ⊗[R] R'` with `Algebra.TensorProduct.rightAlgebra`. Its `commRight_tmul` sends
  `1 ⊗ a` to `a ⊗ 1`. Signatures and docstrings read in
  `Mathlib/RingTheory/TensorProduct/Maps.lean:418-426` and `Basic.lean:490-495`.
  The definition predicates are invariant under algebra isomorphism by composing their
  witnessing presentation (also explained in the dependency node's proof, step 3).
- Finite presentation of A' over R' is supplied by Mathlib's global instance
  `Algebra.FinitePresentation.baseChange` from `Mathlib.RingTheory.FiniteStability`.
  Its full signature was read at line 55; no extra hypothesis on A' is introduced.
- The element a ∈ A is `(a : A)`; its canonical base-changed image is
  `(1 ⊗ₜ[R] a : R' ⊗[R] A)`.
- The elementary case is the first implication, from
  `IsElementaryStandardElement (R := R) a` to
  `IsElementaryStandardElement (R := R') (1 ⊗ₜ[R] a : R' ⊗[R] A)`.
- The strictly standard case is the second implication, using the respective
  `IsStrictlyStandardElement` predicates. The conjunction packages the two independent
  assertions denoted by “resp.” in the source, without assuming both predicates at once.

Dependency declarations used: `Algebra.IsElementaryStandardElement` and
`Algebra.IsStrictlyStandardElement` in `Sheaf.RingTheory.StrictlyStandardElement`, recorded
on def-weil-pbc-strictly-standard-element. Their full definitions and docstrings were read.
The predicates quantify over finite presentations, the same c bound, the requisite initial
minor or sum over all size-c minors, and the remaining-relation ideal-square condition.
Neither predicate is copied. Both imports are used: one supplies those predicates, the other
supplies finite presentation of the base change. The theorem docstring gives all five proof
steps of the node, including their cited dependencies, for stage 3.

Edge cases checked before writing: zero rings are allowed by CommRing and no Nontrivial
binder; arbitrary characteristics and nonflat base change are included. Zero elements are
included. Empty variable/relation sets and c=0 are governed by the existing predicates:
empty determinants are 1, the unique size-zero subset contributes a, and c=m makes the
remaining relations condition empty. No condition excludes any of these cases. Separate
universes cover differently sized rings; there are no unbound implicits or test-object
quantifications. No node fault or STATEMENT-DISPUTED issue was found.

Searches (using `/home/ubuntu/weil-launcher/msearch.py` with this group and item):

- leanfinder: “Elementary standard and strictly standard elements of finitely presented
  algebras are preserved by base change”. Eight hits: finite-presentation base change,
  submersive-presentation base change, and smoothness base change; none state preservation
  of either standard-element predicate.
- loogle: “Algebra.FinitePresentation, Algebra.TensorProduct”. Zero hits; tool reports
  unknown identifier Algebra.TensorProduct. This unsuccessful query is recorded honestly.
- grep: “strictlyStandard|StrictlyStandard|elementaryStandard|ElementaryStandard”.
  Zero Mathlib hits.
- leansearch: “Elementary standard and strictly standard elements are stable under tensor
  product base change”. Unavailable, Internal Server Error; no conclusion drawn from it.
- rg on `WeilConjectures/`: the same four-name pattern, “strictly standard|elementary
  standard”, and the exact item id. No match in the source repository.
- rg on `lean/Sheaf`: the four-name pattern finds the dependency predicates and existing
  Popescu/desingularization users, but no base-change statement. The chosen full theorem
  name has no match there, in the source, or in `dag/lean_names_upstream.json`.
- Read Mathlib FiniteStability.lean, TensorProduct/Basic.lean and TensorProduct/Maps.lean
  to verify the finite-presentation instance and the canonical tensor identification.

Server compile via `scompile.py S1 lem-weil-pbc-strictly-standard-base-change <module>`
passed in 1.4 seconds with no errors or warnings. Delivery dry run is the final mechanical
check; the independent second reader will add their own reading and deliver.

## Second reading by S1

I independently compared the node with the Lean declaration and the source Lemma 07CC.
The node introduces a finite-presentation ring map `R → A`, an arbitrary ring map
`R → R'`, the base change `A' = A ⊗[R] R'`, and an element `a : A`. Its conclusion
has two separate implications: elementary standardness of `a` implies elementary
standardness of `a ⊗ 1` over `R'`, and strictly standardness of `a` implies strictly
standardness of `a ⊗ 1` over `R'`.

The Lean binders `{R : Type u} {A : Type v} {R' : Type w}` with `CommRing` instances,
`[Algebra R A]`, `[Algebra R R']`, and `[FinitePresentation R A]` render exactly those
maps and hypotheses. `a : A` renders the element. The target is represented as
`R' ⊗[R] A`, whose canonical `R'`-algebra structure is the tensor-commuted form of the
source's `A ⊗[R] R'`; `(1 ⊗ₜ[R] a)` is the corresponding image of `a ⊗ 1`. The imported
finite-presentation base-change instance supplies the source parenthetical assertion
that this algebra is finitely presented over `R'`. The conjunction and implication
structure renders both independent “resp.” clauses without adding a joint hypothesis.

Edge cases are covered: zero rings and zero elements are permitted, no characteristic,
flatness, injectivity, or nontriviality is assumed, arbitrary (including empty) finite
presentation data and `c = 0` remain governed by the dependency predicates, and the
three universe parameters allow independently sized rings. No variables are unbound.

I searched the project, source repository, and Mathlib for the notion and theorem using
`rg` plus LeanFinder/Loogle/LeanSearch queries recorded in the worker report. Only the
project's dependency predicates and unrelated presentation base-change results were
found; no existing base-change statement exists. I found no mismatch and made no code
or node-statement change. The module compiles cleanly with `scompile.py`.
