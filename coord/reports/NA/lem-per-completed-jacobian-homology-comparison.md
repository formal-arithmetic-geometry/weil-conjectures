## Worker report

This is a stage-2 statement delivery, not a repeated stage-1 split. The Q119 ledger entry
at coord/ledger.md:41997 records a stage-1 merge; the current node is split and has no lean
record. Its statement and proof are preserved. The earlier stale-dispatch diagnosis did
not distinguish the stages. There was no interrupted delivery or existing Lean work in
this sandbox, only dispatcher brief markers.

The new module lean/Sheaf/RingTheory/CompletedJacobianHomologyComparison.lean states
AlgebraicGeometry.completedJacobianHomologyComparison, with sorry as the entire proof.
There are no new definitions or extra theorem obligations. It adds the already landed
node def-per-completed-polynomial-conormal to stmt_deps to use its continuous derivative.

Hypotheses and clauses, in the order of the natural statement:

* A is an arbitrary commutative Noetherian ring: `{A : Type u} [CommRing A]
  [IsNoetherianRing A]`. The ideal is `(I : Ideal A)`; no properness or nonzero condition.
* C is a commutative finite type A-algebra: `{C : Type v} [CommRing C] [Algebra A C]
  [Algebra.FiniteType A C]`. The ring universes u and v are independent.
* Its completion is `AdicCompletion (I.map (algebraMap A C)) C`, using the extended
  ideal IC. Mathlib's compatible tower includes n=0 (the forced zero coordinate),
  equivalent to the node's tower indexed by n>=1.
* The finite ranks s,r are arbitrary naturals. `MvPolynomial (Fin s) A` is Q.
  `(α : ... →ₐ[A] C)` and `(hα : Function.Surjective α)` express its presentation.
* K is `RingHom.ker α.toRingHom`. The conormal domain is
  `(Algebra.Extension.ofSurjective α hα).Cotangent`, Mathlib's type synonym of
  K.Cotangent = K/K², equipped with its canonical descended C-module structure.
  The section chosen by ofSurjective chooses only lifts: the resulting scalar action
  is independent of lifts since K kills K/K². It does not choose an unknown object.
* The ordinary C-linear arrow dα is specified by the first conjunct, on every kernel
  element f and coordinate j: `dα (Algebra.Extension.Cotangent.mk f) j =
  α (MvPolynomial.pderiv j f.val)`. All conormal classes have such representatives.
* M1 is `dα.ker`; M0 is `(Fin s → C) ⧸ dα.range`, the ordinary module cokernel.
  A finite direct sum of C is rendered by functions Fin s → C.
* Both module completions are `AdicCompletion (I.map (algebraMap A C)) ...`.
  They carry the canonical completed-C action from AdicCompletion.module, defined by
  multiplying each quotient coordinate (AdicCompletion.smul_eval).
* P is the existing `rigPolynomialCompletion I r`, definitionally the completion of
  MvPolynomial (Fin r) A at IQ. `(β : P →ₐ[A] C-hat)` and `hβ` express ANY surjective
  A-algebra map, with no added continuity hypothesis.
* J is `RingHom.ker β.toRingHom`; its conormal module is the same Mathlib Extension
  construction for β. The dβ binder is linear over completed C. The second conjunct
  gives its values on all conormal classes as
  `β (rigPartialDerivative I r j f.val)`, reusing the existing unique continuous
  extension of polynomial differentiation.
* The last two conjuncts are `Nonempty (... ≃ₗ[C-hat] dβ.ker)` and
  `Nonempty (... ≃ₗ[C-hat] ((Fin r → C-hat) ⧸ dβ.range))`, respectively the two
  isomorphisms of the node, from completed M1 and completed M0.

The arrows are existentially introduced together with their defining formulas, rather
than assumed as input or chosen by a data definition. This also states the well-defined
linear arrows asserted by 'Define' in the node. Each formula determines its arrow
uniquely: Extension.Cotangent.mk_surjective says every class is represented by a kernel
element, and equality of functions follows coordinate by coordinate. Thus the theorem
cannot select alternative homology by selecting arbitrary maps. No stronger presentation,
extra topology, arbitrary module action, or tensor-for-completion replacement is assumed.

Dependency declarations read and used:

* Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing; its abbreviation and docstring
  identify this with finite generation of all ideals.
* Mathlib.RingTheory.FiniteType: RingHom.FiniteType (the recorded bare-ring-map notion)
  and Algebra.FiniteType (its algebra-instance form used here), with
  RingHom.finiteType_algebraMap giving the equivalent formulations.
* Mathlib.RingTheory.AdicCompletion.Basic and .Algebra: AdicCompletion, its ring and
  module structures, including module and smul_eval. The coordinate and scalar formulas
  were read in these sources.
* Mathlib.Algebra.MvPolynomial.Basic and .Eval: MvPolynomial, aeval, algHom_ext;
  Mathlib.Algebra.MvPolynomial.PDeriv: pderiv.
* Sheaf.RingTheory.CompletedPolynomialConormal: rigPolynomialCompletion and
  rigPartialDerivative. The whole module and the definition node were read; the latter
  derivative is chosen from a uniqueness theorem and has no hollow data.
* Mathlib.RingTheory.Extension.Basic: Extension.ofSurjective, Extension.Cotangent,
  Extension.Cotangent.module, Extension.Cotangent.mk, and mk_surjective. Their full
  definitions and scalar action were read.

The other proof dependencies currently have no lean record or mathlib_match, so there
are no recorded proof modules to import. Their steps are retained by name in the full
proof docstring: finite conormal homology; completion modulo I; polynomial-conormal
completion and finite-module tensor comparison; exact completion of two short exact
sequences; presentation independence; explicit homotopy action on kernel and cokernel.
The source read is literature/stacks-project/restricted.tex, the definition (NL) and
proofs of lemma-NL-up-to-homotopy (0GAE) and lemma-NL-is-completion (0GAF).

Edge cases checked mathematically and against the binders:

* s=0 or r=0: Fin 0 gives the zero coordinate module; kernels/cokernels and the two
  completion expressions remain defined. No Positive or Nonempty rank is required.
* I=0: the completions reduce to the original modules; presentation independence
  gives the ordinary comparison.
* I=A: all completions are zero; beta onto the zero algebra and its conormal complex
  are covered. No Nontrivial instance is required.
* Zero C and zero A are allowed. The surjectivity hypotheses, not an implicit
  nonzero-ring convention, determine which presentations exist.
* Arbitrary beta is permitted. As an A-algebra map it carries I^nP into I^n C-hat,
  so the source's continuity condition imposes no additional hypothesis.
* Universes u and v are independent; no equality or size hypothesis is introduced.

Searches made for this item (msearch.py with group NA and this item):

* leanfinder: "Completion of the kernel and cokernel of a polynomial conormal
  differential agrees with the continuous completed polynomial Jacobian homology".
  Eight hits, including Algebra.PreSubmersivePresentation.cotangentComplexAux,
  Algebra.Generators.cotangentRestrict_mk and ordinary cotangent comparison lemmas;
  none is the completed arbitrary-presentation homology comparison.
* loogle: "Algebra.H1Cotangent, AdicCompletion". Zero hits.
* grep: "completed.*cotangent|cotangent.*completion|AdicCompletion.*H1Cotangent",
  Mathlib/RingTheory. One hit, AdicCompletion/LocalRing.lean:161, an Ideal.mapCotangent
  use for a maximal-ideal dimension calculation, not the item.
* leansearch: "Adic completion of ordinary conormal kernel and cokernel agrees with
  any continuous completed polynomial Jacobian presentation". Eight hits, including
  AdicCompletion.module, AdicCompletion.map_exact, and
  AdicCompletion.ofTensorProductEquivOfFiniteNoetherian; no full comparison theorem.
* rg over the upstream WeilConjectures source for this item id: no matches. rg over
  upstream and lean/Sheaf for completedJacobianHomologyComparison and completion/H1
  patterns: no existing theorem. A concept search in lean/Sheaf found
  CompletedPolynomialConormal.lean, which is reused, not duplicated.

Validation: scompile.py NA lem-per-completed-jacobian-homology-comparison compiled the
new module in both sandbox and library positions, cleanly (2.4 s and 2.7 s). No warning
or error. The only postponed proof is the item's named theorem.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED fault.

## Second reading by NA

The worker reread the finished node and module, checking each clause as recorded above.
This is a self-check; the independent maintainer review required by this dispatched
brief remains the delivery review. No second agent was started, as instructed. The key
checks were that beta targets the actual completion of C, that its arbitrary-map case
was kept, that the formulas force both differentials on every conormal class, and that
both isomorphisms are linear over completed C with its coordinatewise action. No
mismatch was found and no natural-language statement was changed.
