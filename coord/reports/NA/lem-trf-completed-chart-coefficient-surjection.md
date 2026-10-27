## Worker report

The module `Sheaf.RingTheory.CompletedChartCoefficientSurjection` states
`AddMonoidAlgebra.exists_completedChart_coefficient_surjection`, with `sorry` as
its entire proof. Its docstring carries the nine steps of the accepted DAG proof.
`AddMonoidAlgebra.CompletedChartSurjection` is a fully written proposition packaging
the completion, local-surjection and evaluation clauses belonging to this same node.
It chooses no data and introduces no additional theorem. Both declarations are
listed in `lean.declarations`.

Hypothesis-by-hypothesis correspondence:

- The nonzero Noetherian local commutative ring is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`. Mathlib's `IsLocalRing A` already implies
  `Nontrivial A`; a separate instance binder was removed after the overlapping-instance
  linter identified that redundancy. The residue field k is `IsLocalRing.ResidueField A`,
  definitionally the quotient by its maximal ideal.
- The additive commutative monoid is `(P : Type v) [AddCommMonoid P]`, with the
  recorded `AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P)` and sharpness
  `∀ q : P, IsAddUnit q → q = 0`. The type tag converts the existing multiplicative
  fs predicate without changing the monoid or its group completion.
- The structural map is `a : Multiplicative P →* A`. Thus its zero exponent has
  value one and addition of exponents becomes multiplication. `_ha` is exactly
  the condition that all nonzero exponents map into the maximal ideal.
- The ideal is pinned by `_hI : I = Ideal.span {x | ∃ q : P,
  q ≠ 0 ∧ x = a (.ofAdd q)}`; this is not an arbitrary ideal.
- `[IsRegularLocalRing (A ⧸ I)]` states regularity of R using the ring clause of
  `def-weil-regular-scheme`'s Mathlib match. It also supplies the quotient's local
  and Noetherian instances.
- The chosen lifts are `u : Fin n → A`. `_hu` applies the recorded
  `IsLocalRing.IsRegularSystemOfParameters` to their quotient images as `List.ofFn`.
  That definition includes both generation of the quotient maximal ideal and
  equality of the list length with Krull dimension, hence also n = dim R.

Conclusion-by-conclusion correspondence:

- `maximalIdeal A = I ⊔ Ideal.span (Set.range u)` is m = I + (u_i).
- S is literally `AdicCompletion (maximalIdeal A) A`, the recorded inverse-limit
  construction; its canonical images use `algebraMap A S`.
- The first completion conclusions are `IsNoetherianRing S`, `IsLocalRing S`,
  `maximalIdeal S = (maximalIdeal A).map (algebraMap A S)`, and
  `IsAdicComplete` for that extended ideal. Thus completeness is for mS itself.
- `Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A S))` gives the
  canonical residue field identification, and `ringKrullDim S = ringKrullDim A`
  states the dimension equality.
- Containing a field is the existence of a field K and a unital ring map K -> A;
  such a map is injective since A is nonzero. The quantified field can be taken
  in `Type u`, by replacing any given field with its image subfield in A, so this
  imposes no restriction. Its negation selects precisely the other case.
- In the field case the coefficient ring is literally `ResidueField A`, not just
  an isomorphic field. `coeffMap : k →+* S` satisfies
  `(AdicCompletion.evalOneₐ m).toRingHom.comp coeffMap = RingHom.id k`, the section
  condition for the canonical S -> k projection.
- In the no-field case p is prime and `CharP k p`; C is a local commutative ring
  with `IsCohenRing p C`. The explicit residue equivalence is
  `e : (C ⧸ Ideal.span {(p : C)}) ≃+* k`. The displayed equality for the composite
  of `coeffMap` with `evalOneₐ m` says exactly that the coefficient map reduces to e.
  The Cohen-ring predicate includes m_C = pC and completeness; the field instance
  gives m_k = 0. Injectivity of C -> S is not assumed or asserted.
- Both branches conclude `CompletedChartSurjection A P a n u L coeffMap`.
  Its ring B is the existing `CompletedLocalModel L P n`; the polynomial ring E
  is `MvPolynomial (Fin n) (AddMonoidAlgebra L P)`. These are finite sums with
  the stipulated multiplication, completed at `localModelCompletionIdeal`.
- The predicate existentially supplies a local-ring structure on B, states that
  its maximal ideal is the extension of the completion ideal, and states
  `IsAdicComplete` for that extended ideal. These are conclusions, not assumptions.
- It supplies `φ : B →+* S`, `IsLocalHom φ` and `Function.Surjective φ`.
  `@Continuous` explicitly uses the extended-ideal adic topology on B and the
  mS-adic topology on S, avoiding an unrelated ambient topology.
- The equality for every polynomial f says that φ extends the actual finite-sum
  evaluation, using Mathlib's `AddMonoidAlgebra.liftNCRingHom` with the prescribed
  coefficient and chart maps, followed by `MvPolynomial.eval₂Hom` at the prescribed
  parameter images. The commutation witness is the existing `Commute.all` theorem
  in the commutative target, not an additional assumption.
- Two further equalities give φ(z^q) = the canonical image of a(q), for every q,
  and φ(T_i) = the canonical image of u_i. They spell out the clauses the node
  states explicitly, in addition to the full evaluation equality.
- `φ '' (aB : Set B) = (mS : Set S)` and
  `φ '' (completedLocalModelBoundaryIdeal L P n : Set B) = (mS : Set S)` are
  the requested actual set-image equalities. The latter existing ideal is
  exactly J = (z^q for q nonzero, T_i)B, not its closure.

Dependency interfaces read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (via the parameter module).
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` publicly exposes
  `AlgebraicGeometry.IsFineSaturatedMonoid` from `LogRegularPair`; its definition
  uses finite generation, injectivity into the actual Grothendieck group, and saturation.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the exact ring
  part of `def-weil-regular-scheme`'s retained `mathlib_match`. The separately recorded
  scheme predicate is not the notion needed for this ring statement.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, including both its span and length clauses.
- `Mathlib.RingTheory.AdicCompletion.Basic`, `.Algebra` and `.LocalRing`:
  `AdicCompletion`, `IsAdicComplete`, `evalOneₐ`, the completion's canonical algebra,
  local-ring instance, and residue-field map.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`.
- `Sheaf.RingTheory.CompleteToricModel`, owned by the landed definition node
  `def-trf-complete-toric-model`: `ToricMonoid.Complete`, `completionIdeal`,
  `completedChartIdeal` and `chartIdeal` are abbreviations of the existing
  `AddMonoidAlgebra.CompletedLocalModel`, `localModelCompletionIdeal`,
  `completedLocalModelBoundaryIdeal` and `localModelBoundaryIdeal` terms used in
  the signature. The module is now publicly imported and its definition node is
  the added `stmt_deps` entry. The statement uses these constructions only and
  does not use the normality theorem; the theorem node is therefore not a
  statement dependency. No mathematical statement or proof is changed.
- Plain proof imports match the recorded proof dependencies:
  `WeilConjectures.RingTheory.AdicCompletionNoetherian` (`AdicCompletion.isNoetherianRing`),
  `WeilConjectures.RingTheory.CompletionDimension` (`RingTheory.completion_dimension`),
  `WeilConjectures.RingTheory.ExistsCoefficientSubring`
  (`IsLocalRing.exists_coefficient_subring`),
  `WeilConjectures.RingTheory.CohenRingsExist` (`exists_cohenRing`),
  `WeilConjectures.RingTheory.CohenRingLiftToCompleteLocal`
  (`IsLocalRing.exists_cohenRing_lift`),
  `Mathlib.RingTheory.AdicCompletion.Completeness` (`isAdicComplete`,
  `ker_evalOneₐ_eq_map`), and `.Functoriality`
  (`surjective_of_mk_map_comp_surjective`). The local-completion proof dependency
  is supplied by the public `.LocalRing` import already needed in the signature.

Sources and edge cases:

Read ILO Exposé VI 1.6(i)--(ii), printed p.70 (PDF page 76), and the local
Stacks algebra.tex coefficient-ring definition and Cohen-structure theorem 032A,
including the paragraph constructing the compatible Cohen lifts and the final
surjectivity paragraph. The node explicitly refines the coefficient-and-surjection
part and does not require a log-rank dimension hypothesis or a domain assumption.

P may be the trivial monoid, since all nonzero-exponent generators are given by
sets without a nonemptiness hypothesis. Fin 0 and the empty `List.ofFn` are allowed.
With P trivial and n = 0, the parameter condition forces m = 0, hence A = k and
both completions give k; the field branch allows the identity, and the no-field
branch has false antecedent. For A = Z_p, P trivial, u_1 = p, the assertion gives
Z_p[[T]] -> Z_p with T mapping to p and J mapping onto (p). For A = Z/p² and
P = N with a(1) = p, n = 0, the Cohen coefficient map is permitted to have kernel,
while J still maps onto (p). Equal characteristic p allows a noninjective monoid
chart (for example a nonzero generator mapping to zero) and does not force a Cohen
coefficient ring. The coefficient and monoid universes are independent (u and v);
no scheme/site universe equation or nonempty-index assumption is introduced.

Searches for an existing statement, all run with msearch.py for this item:

- LeanFinder: "surjective continuous local homomorphism from completed monoid
  polynomial algebra over coefficient field or Cohen ring to complete local ring".
  Eight hits, including completion evaluation surjectivity, none the chart statement.
- Loogle: "AdicCompletion, MvPolynomial.eval₂Hom, AddMonoidAlgebra.lift". Zero hits.
- Mathlib grep: "coefficient.*surject|completedLocalModel|CompletedLocalModel|ToricMonoid"
  in RingTheory. Zero hits.
- LeanSearch: "surjective completed monoid polynomial chart coefficient ring Cohen
  ring local ring". Eight hits on coefficient reduction, polynomial maps and local
  ring maps; none the completed chart with both coefficient cases.
- rg over both `lean/WeilConjectures` and `lean/Sheaf` for completed charts,
  formal monoid models, coefficient surjections, `CompletedLocalModel` and
  `ToricMonoid` found the existing local-model definitions and downstream stronger
  log-regular chart theorem. Neither states this weaker-hypothesis coefficient
  construction with all its parameter and ideal-image conclusions.
- rg for the item's exact id in `lean/WeilConjectures` found no declaration.
  rg for both proposed full names in Mathlib, the upstream names index and both
  project roots found no collision.

No new definition node, dependency-module repair, statement correction, or
STATEMENT-DISPUTED finding is needed. The independent maintainer review reads
this delivery; no second-reader agent was started.

## Repair of return 0ab413c9cdf

H2 repaired: replaced the added theorem dependency
`lem-trf-log-regular-saturation-normality` with the already landed definition owner
`def-trf-complete-toric-model`, and replaced the public import with
`Sheaf.RingTheory.CompleteToricModel`. Read that node's Lean record and the full
model, ideal and monomial declarations in its module: the ToricMonoid abbreviations
are the same terms already used in this statement. Kept the accepted signatures
verbatim; only the public import changes in the Lean file. Updated the dependency
explanation above. Compared the retained sandbox node with current main and
refreshed all untouched fields from main; the wrapper builds the repaired delivery
on the current main branch. The maintainer found all other clauses correct.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
