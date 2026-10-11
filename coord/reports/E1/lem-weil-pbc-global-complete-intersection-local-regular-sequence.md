## Worker report

Item: lem-weil-pbc-global-complete-intersection-local-regular-sequence.
Module: `Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence`.
Declaration: `MvPolynomial.isRegular_localizationAtPrime_of_quotient_dimension`.
The delivery states the theorem with one `sorry`; it defines no new notion and proves nothing.
The item copy changes only `lean`. No new nodes, dependency modules, or statement corrections.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `(k : Type u) [Field k]`, with the universe explicitly declared.
- The nonnegative integers m and t are `(m t : ℕ)`; no inequality is added.
- Q = k[y₁,...,yₘ] is `MvPolynomial (Fin m) k`, Mathlib's polynomial algebra.
  Indexing by 0,...,m-1 rather than 1,...,m merely renames the variables.
- The ordered t equations are `f : Fin t → MvPolynomial (Fin m) k`.
  `List.ofFn f` retains that exact order and has length t.
- J = (f₁,...,fₜ) is `Ideal.span (Set.range f)`; T is the quotient
  `MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)`.
  These are expressions in the signature, not arbitrary replacement rings or ideals.
- T ≠ 0 is the `Nontrivial` instance binder on precisely this quotient.
- The Krull dimension of Spec T is `topologicalKrullDim (AlgebraicGeometry.Spec
  (CommRingCat.of (...)))`. The hypothesis is `dim(Spec T) + t = m` in `WithBot ℕ∞`.
  For a nonzero T its dimension is nonnegative or infinite, never bottom. The displayed
  equality forces finite dimension and t ≤ m, and is equivalent to the node's *integer*
  equality dim(Spec T) = m-t. This avoids erroneously admitting t>m through ℕ subtraction.
- The specified prime q'' is `(q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]`.
- The containment J ⊆ q'' is `hq : Ideal.span (Set.range f) ≤ q`.
- Q_q'' is `Localization.AtPrime q`, Mathlib's localization at the prime complement.
- The elements fᵢ/1 are obtained from the original ordered list by `.map (algebraMap
  (MvPolynomial (Fin m) k) (Localization.AtPrime q))`, the canonical localization map.
- Regularity on the local ring itself is `RingTheory.Sequence.IsRegular
  (Localization.AtPrime q)` applied to that mapped list. Its inherited
  `regular_mod_prev` asserts injectivity of multiplication on each successive quotient;
  its `top_ne_smul` asserts that the final quotient is nonzero. Both clauses are present.
  No conclusion about just weak regularity is substituted.

Dependencies and declarations used (the complete recorded signatures and docstrings
were opened in the read-only source):

- def-weil-pbc-mv-polynomial-ring: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`; its recorded universal-property declarations
  `MvPolynomial.aeval` (`Mathlib.Algebra.MvPolynomial.Eval`) and `MvPolynomial.algHom_ext`
  were also read. Only the algebra itself is needed in this signature.
- def-kun-topological-krull-dimension: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension` (Krull dimension of irreducible closed subsets).
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` in
  `Mathlib.AlgebraicGeometry.Scheme`, the actual affine scheme, not a different spectrum.
- def-weil-pbc-localization-at-prime: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; the other clauses of this dependency
  (residue fields and fibre rings) do not occur in the item.
- def-weil-pbc-regular-sequence: `RingTheory.Sequence.IsRegular` in
  `Mathlib.RingTheory.Regular.RegularSequence`, with the base ring as its module.

Edge cases checked before writing:

- t=0: the list and generated ideal are empty/zero. The conclusion is regularity of
  the empty sequence on a nonzero prime localization, exactly as the definition requires.
- m=0: Q=k. If t=0 the quotient and the dimension hypothesis are those of a field.
  If t>0 the integer dimension condition cannot hold for nonzero T; the Lean additive
  condition likewise cannot hold. In particular a zero equation in a field is excluded.
- t>m: no nonzero quotient can have negative dimension; this is excluded by hdim,
  rather than by an extra hypothesis or truncated subtraction.
- A unit among the equations makes T zero and also prevents a prime containing J;
  the hypotheses correctly exclude it.
- A zero or redundant equation cannot satisfy the expected dimension count unless the
  empty-sequence case applies; no arbitrary distinctness/nonvanishing assumption is added.
- All field characteristics and all universes of fields are admitted. No algebraic closure,
  finite field, maximal-prime, closed-point, or positive-dimension hypothesis is imposed.

Searches made:

1. `msearch.py ... leanfinder` query: "Equations in a polynomial ring over a field whose
   quotient has dimension number of variables minus number of equations form a regular
   sequence after localization at every prime containing them". Eight hits: localization
   of an already weakly regular sequence, the regular-sequence definition and variants,
   and the local-ring equivalence. None obtains regularity from the dimension hypothesis.
2. `msearch.py ... loogle` query: `RingTheory.Sequence.IsRegular, MvPolynomial`.
   Result: zero hits.
3. `msearch.py ... grep` query:
   `IsRegular.*MvPolynomial|MvPolynomial.*IsRegular|complete.intersection` in `RingTheory`.
   Ten hits, concerning regular leading coefficients, regular polynomial rings, and an
   unrelated presentation comment. No matching theorem.
4. `rg -n 'complete.intersection|global_complete|IsRegular.*MvPolynomial|MvPolynomial.*IsRegular'`
   over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's `lean/Sheaf`.
   The source repository gives no hits; project hits include CompleteIntersectionOverField,
   finitely generated field models, and relative complete intersection modules. They define
   the notion or give other existence/flatness statements, not this theorem. Opened
   CompleteIntersectionOverField to compare the existing dimension convention.
5. `grep -rn 'lem-weil-pbc-global-complete-intersection-local-regular-sequence'` over
   `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no hits.
6. `msearch.py ... leansearch` query: "Equations of a global complete intersection over
   a field form a regular sequence at each prime containing the equations".
   Service unavailable: Internal Server Error. The other searches above succeeded.

Source check: `literature/stacks-project/algebra.tex` is absent on this machine, so opened
[Stacks Tag 00SB](https://stacks.math.columbia.edu/tag/00SB) and
[Stacks Tag 00SC](https://stacks.math.columbia.edu/tag/00SC) online. The dimension argument
at a maximal ideal and its application at the arbitrary prime match the node. The docstring
includes all six node proof steps with their dependency ids, explicitly distinguishing the
node's final localization elaboration from the source's shorter assertion.
No statement fault or STATEMENT-DISPUTED issue found.

Validation: server `scompile.py E1 lem-weil-pbc-global-complete-intersection-local-regular-sequence
<module>` succeeded, exit 0, compiled in 1.6 seconds, with no warnings. All variables and
universes are explicitly bound. Every Lean line is at most 100 characters. The `lean.statement`
record is copied verbatim from `theorem` through the signature, excluding `:=`.

## Second reading by E1

I independently opened the item JSON, delivered Lean module, all five statement dependency
nodes, and their recorded Mathlib declarations. No statement mismatch was found; the Lean
and node record remain unchanged. No new definition nodes, dependency modules, or statement
corrections occur in this delivery, so H12/H13 and correction-citer checks are inapplicable.

Source: the local Stacks algebra.tex is absent. I read the actual TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex, from
`lemma-lci-CM` through the proof of `lemma-lci`, and checked the rendered
[00SB](https://stacks.math.columbia.edu/tag/00SB) and
[00SC](https://stacks.math.columbia.edu/tag/00SC). The first proof assumes a field and a
finite polynomial presentation of dimension n-c; the last paragraph of the second proof
applies this to the equations at an arbitrary containing prime. Finite type and Noetherian
properties follow from this concrete polynomial presentation; they need no extra binders.

My object/hypothesis/conclusion checklist (each verdict: exact):

1. Field k: `(k : Type u) [Field k]`; arbitrary characteristic and universe u.
2. Nonnegative integers m,t: `(m t : ℕ)`, including zero; no extra inequality.
3. Polynomial ring Q: `MvPolynomial (Fin m) k`. The variable-index bijection just
   shifts 1,...,m to 0,...,m-1. Mathlib Basic defines the finite monomial algebra;
   I also read the dependency's `aeval` and `algHom_ext` signatures and docstrings.
4. Ordered equations f₁,...,fₜ: `f : Fin t → MvPolynomial (Fin m) k`;
   `List.ofFn f` preserves their order, including repeated or zero elements.
5. Generated ideal J: `Ideal.span (Set.range f)`; quotient T:
   `MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)`. Neither is a separately
   chosen ideal or ring with an omitted identification.
6. Nonzero T: precisely `[Nontrivial (... ⧸ Ideal.span (Set.range f))]`.
7. Dimension of Spec T equals the integer m-t: `hdim` uses
   `topologicalKrullDim (AlgebraicGeometry.Spec (CommRingCat.of T)) +
   (t : WithBot ℕ∞) = (m : WithBot ℕ∞)`. Nonzero T has nonempty spectrum,
   so its dimension is nonnegative or infinite. This equation forces finiteness
   and t≤m and is equivalent to the integer difference condition. In particular
   it does not silently interpret a negative integer as truncated subtraction.
   I read `topologicalKrullDim`, defined using `IrreducibleCloseds`, and `Spec`,
   defined from the affine locally ringed space, as the dependency nodes require.
8. Arbitrary prime q'' of Q: `(q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]`;
   no maximality, closed-point, or residue-field assumption appears.
9. J contained in q'': `hq : Ideal.span (Set.range f) ≤ q`.
10. Local ring Q_q'': `Localization.AtPrime q`, exactly the localization at
    `q.primeCompl`; the dependency's residue-field and fibre clauses are not needed.
11. Images in their original order: `(List.ofFn f).map (algebraMap Q
    (Localization.AtPrime q))`, the canonical map a↦a/1.
12. Regular sequence in that ring: `RingTheory.Sequence.IsRegular
    (Localization.AtPrime q)` of this list, with that ring as its own module.
    I read `IsWeaklyRegular.regular_mod_prev`, `IsRegular.top_ne_smul`, and
    `IsSMulRegular`: multiplication is injective on each quotient by the preceding
    terms and the final quotient is nonzero. Both conclusion clauses are present.

The binder order is the node's order: field, presentation, nonzero quotient and dimension,
then the arbitrary containing prime, then regularity. The canonical quotient and
localization introduce no hidden choices or extra assumptions. All variables and the
universe are explicitly bound.

Edge cases: t=0 yields the empty regular sequence on a nonzero prime localization.
m=0 gives a field polynomial ring; only t=0 can meet the dimension equation for a
nonzero quotient. t>m is excluded by exactly the node's integer dimension condition.
The zero quotient and empty affine scheme are excluded by the explicit nonzero
hypothesis, as in the node. A unit equation also precludes a containing prime. Zero
or redundant equations are allowed syntactically but cannot meet the expected dimension
count. No characteristic or universe is excluded. No finiteness instance is imposed
on the field itself.

Independent searches, using different wording from the worker:

- LeanFinder: "codimension equal to length of equations implies nonzerodivisors in
  successive polynomial quotients localized at primes". Eight hits; the closest is
  `IsWeaklyRegular.isRegular_of_isLocalization_of_mem`, whose signature I opened.
  It assumes weak regularity and does not infer it from dimension; no exact match.
- Loogle: `MvPolynomial, topologicalKrullDim`: zero hits.
- LeanSearch: "polynomial algebra over a field equations expected codimension yield
  regular sequence in local rings": service unavailable (Internal Server Error);
  this is not a negative-search verdict.
- msearch grep, RingTheory/Regular: `quotient.*dimension|dimension.*regular|regular.*dimension`:
  five projective-dimension hits, no matching Krull-dimension converse.
- Independent rg over Mathlib RingTheory, upstream WeilConjectures, and project lean/Sheaf:
  `quotient_dimension|dimension.*[Ii]sRegular|[Ii]sRegular.*dimension|regular.*codimension|codimension.*regular`.
  Opened project `RingTheory.Sequence.isRegular_of_dimension_drop`: a general CM local
  ring criterion requiring local dimension and depth, not this polynomial-global theorem.
  Opened `Algebra.IsGlobalCompleteIntersection`: a presentation predicate, not the result.
  Upstream hits concern regular immersions, not this theorem. The exact proposed name
  also has no hits in upstream, Mathlib, or dag/lean_names_upstream.json.

H5/H6: no definitions and exactly one named theorem with proof `by sorry`.
H8: module and theorem docstrings carry the source and blueprint id; the six-step
proof follows the node's maximal-localization argument, dimension bounds, CM criterion,
and subsequent localization/isomorphism. H9: namespace MvPolynomial and topic RingTheory
are appropriate; each import supplies a notion used in the signature, all lines meet
100 characters, and the recorded signature is verbatim the theorem signature.

Repairs: none needed. I added only this independent second-reading report.
Validation: scompile.py compiled the delivered module on the server in 1.7 seconds,
exit 0, with no errors or warnings. The dry-run and actual delivery follow below.
