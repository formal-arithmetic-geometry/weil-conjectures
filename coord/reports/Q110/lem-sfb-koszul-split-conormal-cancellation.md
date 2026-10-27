# Q110: lem-sfb-koszul-split-conormal-cancellation

## Worker report

The delivery states `Ideal.koszulRegular_quotient_of_split_conormal` in
`Sheaf.RingTheory.KoszulSplitConormalCancellation`, with one `sorry` proof.
No definitions or additional nodes are introduced. The accepted Q107 stage-1
split, statement, dependencies and proof are unchanged; only `lean` is added.
The inherited unchanged-stage-1-item refusal is superseded by the current stage-2
assignment, as coord/brief-stage2.md section 0 explicitly explains.

I read Stacks divisors.tex, Tag 068Z, statement and proof (3), and Tag 063G,
statement and proof. The former gives cancellation with the split conormal
sequence; the latter identifies Koszul regularity with finite regular generators
on affine neighbourhoods. The node is the principal-affine ideal form of these.

Clause-by-clause rendering:

- A commutative ring is `{R : Type u} [CommRing R]`, with explicit universe `u`.
- The two ideals are `(K J : Ideal R)` and their inclusion is `hKJ : K ≤ J`.
- Finite generation of K is exactly `hK : K.FG`.
- Every prime containing J is quantified in `hlocal` as
  `∀ (p : Ideal R), p.IsPrime → J ≤ p → ...`.
- A common principal neighbourhood is `∃ h : R, h ∉ p ∧ ...`.
  Both existential tuples use the SAME `Localization.Away h`.
- Generators of KR_h are `n : ℕ`, `f : Fin n → Localization.Away h`, with
  `Ideal.span (Set.range f) = K.map (algebraMap R (Localization.Away h))`.
  The second tuple uses `m`, `g`, and J in the identical expression.
- Koszul regularity of these two tuples is the recorded
  `RingTheory.Sequence.IsKoszulRegular f` and `IsKoszulRegular g`.
- The module K/KJ is `K ⧸ (J • ⊤ : Submodule R K)`. Under inclusion into R,
  the submodule J times K maps precisely onto JK=KJ, by ideal multiplication.
  J/J² is the existing Mathlib `J.Cotangent`, whose quotient map is
  `J.toCotangent`.
- The split exact canonical conormal sequence is expressed by `hsplit`:
  `∃ r : J.Cotangent →ₗ[R] (K ⧸ (J • ⊤ : Submodule R K)), ∀ k : K, ...`.
  Its equality reads r([k] in J/J²) = [k] in K/KJ, using
  `J.toCotangent ⟨k.1, hKJ k.2⟩` and `(J • ⊤).mkQ k`.
  This is precisely the retraction identity for the CANONICAL inclusion map.
  That map is well defined since KJ is contained in J². Quotient classes of
  elements k exhaust K/KJ, so this equality is equivalent to r alpha=id.
  The identity makes alpha injective. The canonical next quotient map to
  J/(K+J²) is surjective, and its kernel is (K+J²)/J², the image of alpha.
  Thus no exactness condition is lost by the generator-wise formulation.
  Conversely, the node's split exact sequence gives exactly this equality.
  Both modules are killed by J: an R-linear map between them is automatically
  linear for the induced R/J-actions, since each quotient scalar lifts to R.
  Therefore using R-linearity adds or drops no hypothesis; no arbitrary alpha
  or arbitrary comparison map has been substituted.
- The ring Rbar is the literal `R ⧸ K`. The ideal Jbar is
  `J.map (Ideal.Quotient.mk K)`, the image ideal J/K since K≤J.
- The conclusion quantifies every `q : Ideal (R ⧸ K)` with `q.IsPrime` and
  `J.map (Ideal.Quotient.mk K) ≤ q`.
- Its witness is `∃ u : R ⧸ K, u ∉ q ∧ ...`, followed by a finite tuple
  `g : Fin n → Localization.Away u`. The span equality uses the image of Jbar
  under `algebraMap (R ⧸ K) (Localization.Away u)`; regularity uses the same
  recorded Koszul-regularity definition. This is the stated conclusion exactly.
- Lengths n and m range over all naturals including zero; no nonempty or
  Noetherian instance occurs. `set_option autoImplicit false` forbids unbound
  variables, and all universes are explicitly declared.

Dependency interfaces read and used:

- def-weil-ring-localization-away: `Localization.Away`, recorded module
  Mathlib.GroupTheory.MonoidLocalization.Away, publicly provided through
  Mathlib.RingTheory.Localization.Away.Basic (which supplies ring/algebra data).
- def-weil-pbc-koszul-regular-sequence: module
  WeilConjectures.RingTheory.KoszulRegularSequence, declaration
  `RingTheory.Sequence.IsKoszulRegular`, read in full including its docstring.
  It means vanishing of every nonzero natural-degree Koszul homology module;
  the underlying complex has zero negative degrees.
- Mathlib.RingTheory.Ideal.Cotangent: `Ideal.Cotangent`, `Ideal.toCotangent`;
  Mathlib.LinearAlgebra.Quotient.Defs: `Submodule.mkQ`;
  Mathlib.RingTheory.Ideal.Maps: `Ideal.map`;
  Mathlib.RingTheory.Ideal.Quotient.Defs: `Ideal.Quotient.mk`.
  These existing notions suffice; none is duplicated.

Already stated proof dependencies are imported with plain import:
Mathlib.RingTheory.Localization.AtPrime.Basic (Localization.AtPrime),
Mathlib.LinearAlgebra.TensorProduct.Map (TensorProduct, LinearMap.rTensor),
Mathlib.LinearAlgebra.Basis.VectorSpace (Module.Basis.extend),
Mathlib.RingTheory.Flat.Localization (IsLocalization.flat),
Mathlib.RingTheory.Localization.Ideal (localization/quotient compatibility),
WeilConjectures.RingTheory.KoszulRegularFlatBaseChange
(RingTheory.Sequence.isKoszulRegular_of_flat), and
WeilConjectures.AlgebraicGeometry.KoszulComplex (ExteriorAlgebra.koszulComplex).
The proof dependencies lem-sfb-koszul-generators-from-fibre-basis and
lem-sfb-koszul-prefix-quotient-criterion have no Lean record or Mathlib match
at inspection time; their proof steps are included in the theorem docstring,
but there is no module to import yet. They are not statement prerequisites.

Edge cases checked mathematically before writing:

- K=0: the retraction has zero target, and the conclusion is the assumed local
  Koszul regularity of J transported along R/0.
- K=J: the canonical conormal map is the identity; J/K=0 is generated by an
  empty Koszul-regular tuple on the whole quotient spectrum.
- J=R: neither the premise nor the conclusion has a prime containing the unit
  ideal. The conormal modules are zero, so splitting still makes sense.
- R/K=0 (including the zero ring R): the conclusion is vacuous because there
  are no prime ideals. No Nontrivial instance excludes this case.
- Empty tuples: Fin 0 is admitted by both local hypotheses and the conclusion.
- The split condition is substantive: for R=k[x], K=(x²), J=(x), the canonical
  map K/KJ→J/J² is zero with nonzero domain, so no such retraction exists.
  This example would invalidate cancellation if splitting were dropped.

Searches for an existing statement (all via the prescribed msearch.py):

- leanfinder: "Nested ideals K contained in J locally generated by Koszul regular
  sequences with a split conormal sequence imply J modulo K is locally generated
  by a Koszul regular sequence". Eight hits, including
  RingTheory.Sequence.IsWeaklyRegular.regular_mod_prev and ordinary regular-sequence
  localization/concatenation lemmas; none states non-Noetherian Koszul cancellation.
- loogle: `"IsKoszulRegular"`. Zero hits.
- grep: `Koszul|conormal.*split|exact_mulQuot`, Mathlib/RingTheory.
  Three hits: ordinary regular sequence TODO and
  Ideal.exact_mulQuot_quotOfMul (an unrelated multiplication exact sequence).
- leansearch: "Split conormal sequence cancellation for nested Koszul regular
  ideals without Noetherian hypotheses". Eight ordinary regular-sequence and
  Krull-dimension hits, no exact statement.
- rg across lean/WeilConjectures and lean/Sheaf for split/conormal/cancellation
  patterns, and for this item id and the proposed theorem name; no exact match.
  Nearby conormal splitting results concern smooth presentations or dimension
  comparisons, not cancellation for arbitrary nested Koszul-regular ideals.
  No match in dag/lean_names_upstream.json for the proposed declaration.

Server validation: scompile.py compiled both the sandbox probe and the actual
library module cleanly (2.7 s and 3.1 s). No warnings or errors were printed.
There is no statement dispute or statement correction.

## Second reading by Q110

This is the worker's own second pass, not a claim of an independent reader;
the dispatcher brief forbids starting other agents and assigns independent
review of this delivery to the maintainer. With the complete node and module
open, I rechecked the single h, the two independent finite lengths, the prime
quantifiers on R and R/K, the quotient ideal, and the element-wise retraction
identity. The nonliteral but equivalent presentation is the conormal hypothesis:
its equivalence to the full canonical split exact sequence is detailed above.
No mismatch was found and no statement change was made.
