## Worker report

Repair of returned immutable head 858e99bf2f5c, based on the live reviewed Q17 node.
The sandbox initially contained only dispatcher marker files, with no retained node,
module or report. I read the live node, its nine statement dependencies and recorded
interfaces, their source declarations and docstrings, its seven proof steps and proof
dependencies, and the return in coord/returns/O2.md. The old stage-1 delivery is
superseded; this delivery changes the live node only in `lean`.

The module `Sheaf.AlgebraicGeometry.Curve.AlgClosedCurveModel` states
`AlgebraicGeometry.exists_smooth_proper_integral_curve_model`, with one `sorry` proof
and no definitions. Its docstring contains the source places and all seven steps of
Q17's compactify-then-normalize proof, with the dependency ids used in each step.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base field is `(k : Type u) [Field k] [IsAlgClosed k]`. Mathlib's
  `IsAlgClosed` means every polynomial splits and is equivalent to the node's
  every-nonconstant-polynomial-has-a-root formulation by `IsAlgClosed.exists_root`
  and `IsAlgClosed.of_exists_root`.
- The field extension is `(E : Type u) [Field E] [Algebra k E]`. A field algebra
  map is injective, so it supplies the stated copy of k in E.
- Finite generation as a FIELD extension is
  `hfg : (⊤ : IntermediateField k E).FG`, not finite generation as an algebra.
- Transcendence degree one is `htrdeg : Algebra.trdeg k E = 1`.
- A single model is quantified as `∃ (C : Scheme.{u}) (s : C ⟶ Spec (.of k))`.
  The arbitrary common universe follows the scheme convention of the recorded
  dependencies and imposes no finiteness or countability bound.
- Integrality is the existential instance `(_ : IsIntegral C)`, in scope when
  the actual function field is formed. It includes nonemptiness.
- Smoothness and properness over k are `Smooth s` and `IsProper s`.
- Finite type over k is `LocallyOfFiniteType s ∧ QuasiCompact s`, exactly the
  recorded interface for def-weil-finite-type-morphism. Although properness implies
  these, they are retained because the node explicitly lists finite type.
- Dimension one is `topologicalKrullDim C = 1`, using the recorded topological
  Krull dimension with values in WithBot ℕ∞.
- The function field is `C.functionField`, Mathlib's definitional abbreviation
  for `C.presheaf.stalk (genericPoint C)`, not a freely supplied fraction field.
- Its field isomorphism to E is `e : C.functionField ≃+* E`. It is an isomorphism
  OVER k because the statement also requires
  `Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk (genericPoint C) ≫ s =
  Spec.map (CommRingCat.ofHom (algebraMap k E))`.
  This says the generic-point morphism induced by e is a k-morphism. By the
  fully faithful affine Spec correspondence it says exactly that e carries the
  structural copy of k in the generic stalk to the given copy in E. Thus a bare
  ring isomorphism has not silently replaced the required k-isomorphism. This
  diagram avoids introducing an arbitrary k-algebra structure on the stalk.
- The universal quantifier is over `(B : Subalgebra k E) [ValuationRing B]
  [IsFractionRing B E]`. A subalgebra is precisely a subring of E containing the
  given image of k. Its algebra map B to E is the canonical inclusion. Thus the
  last instance is exactly the live condition Frac(B)=E for that inclusion,
  not a fraction field attached to a different embedding.
- The centre is `∃ f : Spec (.of B) ⟶ C`. The equality
  `Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫ f =
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk (genericPoint C)`
  specifies that it EXTENDS the chosen generic-point morphism, rather than just
  asserting existence of an unrelated B-point.
- The equality `f ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k B))` says
  that this extension is a k-morphism, with B's canonical base map.
  No uniqueness of the extension, projectivity, choice of a point, or extra
  hypotheses on B are asserted.

Recorded statement dependency declarations used:

| Node | Module | Declaration / use |
| --- | --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs (through the field imports) | Field |
| def-kun-transcendence-degree | Mathlib.RingTheory.AlgebraicIndependent.Basic | Algebra.trdeg |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth | AlgebraicGeometry.Smooth |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties (publicly imported by FunctionField) | AlgebraicGeometry.IsIntegral |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | AlgebraicGeometry.IsProper |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact | AlgebraicGeometry.LocallyOfFiniteType; AlgebraicGeometry.QuasiCompact |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension | topologicalKrullDim |
| def-trf-valuation-ring | Mathlib.RingTheory.Valuation.ValuationRing | ValuationRing; ValuationRing.TFAE identifies the fraction-field alternative |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Spec; AlgebraicGeometry.Spec.map |

Additional existing mathematical interfaces are
`Mathlib.AlgebraicGeometry.FunctionField` / `Scheme.functionField`,
`Mathlib.AlgebraicGeometry.Stalk` / `Scheme.fromSpecStalk`,
`Mathlib.FieldTheory.IntermediateField.Adjoin.Defs` / `IntermediateField.FG`,
`Mathlib.RingTheory.Localization.FractionRing` / `IsFractionRing`, and
`Mathlib.Algebra.Algebra.Subalgebra.Basic` / `Subalgebra` (available through the
public imports). No copy of any notion has been introduced.

Every stated proof dependency's module is imported. In particular this includes
`WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg`,
`Sheaf.AlgebraicGeometry.AffineProjectiveCompactification`,
`Sheaf.TraceFormula.ReducedSchemeImage`,
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`,
`WeilConjectures.AlgebraicGeometry.Regular`, and
`Mathlib.AlgebraicGeometry.ValuativeCriterion`. The first generic-stalk/fraction-field
lemma is in the publicly imported Mathlib FunctionField module. The existing
normalization-properties record's displayed signature is stale relative to its
actual upstream source; the theorem's actual signature was read. This statement
only imports that proof interface and does not apply or restate it.

Edge cases checked before writing:

- For E=k(t), P¹ over k supplies the geometric model and its generic stalk; the
  degree-one hypothesis allows this basic transcendental extension.
- The empty scheme cannot witness the conclusion: IsIntegral includes Nonempty,
  and its dimension would be bottom rather than one.
- E=k does not satisfy the transcendence-degree-one hypothesis; there is no
  accidental claim that a zero-dimensional field extension has a curve model.
- B=E with its identity inclusion is allowed: a field is a valuation ring and
  its own fraction field, and the required extension is the generic map itself.
- B=k inside a transcendental E is excluded by the live Frac(B)=E hypothesis.
  This is the precise condition that was already repaired in the live stage-1
  node; no new statement correction is made here.
- Higher-rank valuation rings are included: no rank, discreteness, noetherianity,
  nontriviality or finite-height hypothesis is added.
- Both characteristic zero and positive characteristic are included. Perfectness
  is a consequence of algebraic closedness in the proof, not an extra hypothesis.
- Both diagram equalities use the same existential e, C and s and the canonical
  inclusion of B, so the centre is tied to the specified field identification.

Searches for an existing statement (2026-10-22):

- `msearch.py ... leanfinder "A finitely generated field of transcendence degree one
  over an algebraically closed field has a smooth proper integral curve model"`:
  eight hits, including WeierstrassCurve.integralModel and exists_isIntegral and
  standard smooth presentations. No general curve-model existence theorem.
- `msearch.py ... loogle "Algebra.trdeg, IsIntegral, Smooth, IsProper"`: zero hits;
  Loogle reported unknown identifier Smooth, so this is recorded as an inconclusive
  name search, not as proof of absence.
- `msearch.py ... leansearch "Every function field of transcendence degree one over
  an algebraically closed field has a smooth proper curve model"`: eight hits,
  including Scheme.functionField, its Field instance, functionField_iff and the
  function-field ring of integers. Reading these found no general proper-model
  theorem: functionField_iff compares algebraic finite-dimensionality, while
  Scheme.functionField defines the generic stalk.
- `msearch.py ... grep "exists.*(smooth|proper).*functionField|algclosed.*curve.*model"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg -n 'lem-trf-algclosed-curve-model|algclosed.*curve.*model|exists.*(proper|smooth).*functionField'
  lean/WeilConjectures lean/Sheaf`: the node is cited only in proof docstrings of
  ValuedCurveEtaleParameter, PurelyInseparableFrobenius and
  FrobeniusSeparableFactorization; no declaration of its statement. The unrelated
  RadicialSmoothing result does not assert existence of a proper curve model.
- `rg -n 'exists_smooth_proper_integral_curve_model'` in Mathlib,
  lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: zero hits.
  The new declaration name does not duplicate a recorded upstream name.

Source reading: literature/stacks-project/curves.tex, lines 159--226 (0BY1,
including the final compactify-then-normalize alternative), and lines 249--260
(0BY3); the proper valuative-criterion source and its recorded Mathlib API.
No statement correction, new node or dependency repair is needed. The inherited
split_report mentions the now-resolved Frac(B)=E dispute; it is left byte-for-byte
as in the live node because this repair must change only `lean`.

Return repairs:

1. H1: supplied the Lean module, its complete item lean record, and successful
   server compilation; this is now a stage-2 statement delivery.
2. H2/H7: reconstructed the item from the live Q17 reviewed node, retaining
   statement, all nine stmt_deps, all seven proof steps, proof_deps, proof_origin,
   split_report, mathlib_searches, reviewed and every other non-lean field.
3. H11: supplied the explicit second reading below, checking the actual final
   node and module, with both generic-point and base-map compatibility clauses.

Validation: prescribed `scompile.py O2 lem-trf-algclosed-curve-model` compiled
this module in both sandbox and library modes with no errors and no warnings.

## Second reading by O2

This is a separate reading pass by the same worker, with the final live node copy
and final Lean module open; no second agent was started, as the dispatcher forbids
it. Independent review remains the maintainer's delivery review.

I first read the prose without the proof plan, then read the complete theorem from
its binders to its final equality. The base is an algebraically closed field in
both. The extension is a finitely generated FIELD extension in both: `FG` uses
IntermediateField.adjoin, not Algebra.adjoin. Its transcendence degree is exactly
one. The conclusion supplies one k-scheme C, its structural morphism s, integrality,
smoothness, properness, both components of finite type and dimension one. The
existential integral instance makes C.functionField the generic stalk and a field.
The ring equivalence e has the correct direction C.functionField to E. I checked
contravariance: `Spec.map e` starts at Spec E, and its composite with
`C.fromSpecStalk (genericPoint C)` is exactly the prescribed generic point in C.
The following equality after composition with s makes e an isomorphism over k.

For the last sentence, Subalgebra k E restricts precisely to subrings of E
containing k. ValuationRing and IsFractionRing use that subring and its actual
inclusion in E. The two final equalities have the correct sources Spec E and
Spec B respectively, target C and Spec k respectively, and use the same e and s.
They express restriction to the generic point and the k-morphism condition
separately. The universal quantifier includes B=E and arbitrary valuation rank;
it excludes the problematic B=k because E/k has transcendence degree one.
No uniqueness, projectivity or extra geometric-integrality assertion is present.
The comparison found no missing or additional mathematical hypothesis or clause.

I also compared the JSON files programmatically: only `lean` differs from the
live reviewed node. In particular the seven-step compactify-then-normalize plan
has not been replaced by the old eight-step normalization-first delivery.
The exact signature was extracted from the final source between `theorem` and
`:= by`, preserving line breaks, for the lean.statement record. There are no
new nodes, no definitions with postponed data, and only the item's named theorem
has a postponed proof. No statement mismatch required a further edit in this pass.
