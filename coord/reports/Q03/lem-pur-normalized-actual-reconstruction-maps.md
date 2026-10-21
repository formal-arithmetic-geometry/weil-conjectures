## Worker report

Existing statement, no new Lean module: `WeilConjectures.purNormalizedReconstruction`,
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`, lines 58–65 in the read source.
Read the complete declaration and its docstring, and checked the current server source with
`scompile.py --source Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`.
The node copy changes only `lean`. Its signature is copied verbatim, including line breaks,
from the theorem keyword up to `:=`. No new definitions, proofs, or sorry declarations.

The source is the current blueprint's
`sec-smooth-purity/sk-thm-purity-transport/prop-pur-adic-reconstruction-trace-coherence.proof.md`,
the paragraph saying that the realized adjunction's counit and its transport are included in
reconstruction. The node is an extracted intermediate result. The existing theorem has exactly
its reconstruction assertions; clauses already carried by the specified evaluation-calculus
input remain carried by that input. Restating them in another conjunction would duplicate the
existing theorem and dependency fields.

Hypotheses and objects, checked against the declaration and definitions:

| Node | Lean rendering |
| --- | --- |
| Prime ell | Section binder `(l : ℕ) [Fact l.Prime]`. |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. |
| Its valuation ring and chosen uniformizer | The imported `Padic.coefficientExtensionIntegers l E` and `Padic.coefficientExtensionUniformizer l E`; the quotient ideal is `Padic.coefficientExtensionIdeal l E n`. These are the recorded constructions, not new parameters. |
| Scheme W, ell invertible | `(W : Scheme.{t})` and `(_hl : IsUnit (l : Γ(W, ⊤)))`. Invertibility of the integer scalar is equivalently invertibility on global sections. It imposes no field or characteristic choice on W. |
| Fixed small pro-etale site and size convention | `Scheme.ProEt.topology W`, with site objects in `Type (t+1)` and morphisms in universe t; coefficient sheaves/modules in `max u (t+1)`. The theorem keeps t and u independent. |
| Positive B_n and completed ring | `integralCoefficientSheaf l E W n` uses quotient exponent n+1. `completedIntegralCoefficientSheafUnrestricted l E W` is the inverse limit of these exact constant quotient sheaves. |
| Abelian strict semilinear system category and unbounded derived category | `coefficientSequenceModules l E W`, modules over the coefficient ring on the sequence site; `coefficientSequenceDerived l E W` is its ordinary unbounded derived localization. Horizontal restriction maps are precisely quotient-semilinear transitions. |
| Normalized full subcategory | `IsNormalizedCoefficientSequence l E W N`, not an arbitrary compatible family of finite-level objects. It tests every n ≤ m by the universal Hom bijection for the actual transition. Under the recorded derived scalar adjunction this is precisely invertibility of its transition adjoint, by Yoneda. This is the same normalization criterion as `NormalizedDVRTower.normalization`. |
| Complete full subcategory | `IntegralOnSlice.IsComplete l E W none K` definitionally uses the global `IsDerivedCompleteUnrestricted`. This is the recorded augmented Roos-triangle predicate; no chosen completion isomorphism replaces it. |
| The specified reduction/limit adjunction | `(S : CoefficientDerivedSystemCalculus l E W)` is exactly the construction package of `lem-coef-derived-system-evaluation-calculus`, whose existence is stated by `coefficientDerivedSystemEvaluationCalculus`. `S.reduction` is R; the fixed `coefficientSequenceLimit l E W` is L; `S.adjunction` is their adjunction. The theorem is valid for every such specified calculus. |
| No finiteness or local-model hypotheses on input complexes | The only input predicates are normalization of N or completeness of K. No bounds, constructibility, Tor interval, or equipped model of either input occurs. `S.reductionModel` characterizes the canonical functor on K-flat representatives for all inputs; it is not an extra equipped local model on N or K. |

Every conclusion clause, including those supplied by the specified adjunction data:

1. Reduction is normalized for every ambient P: `S.reduction_normalized P`, inherited from
   `CoefficientDerivedSystemReductionModel`. Its domain is the whole
   `DerivedCategory (scalarReductionSource l E W)`.
2. For every normalized N, L(N) is complete: the first conjunct of
   `(purNormalizedReconstruction l E W hl S).1 N hN` is exactly
   `IntegralOnSlice.IsComplete l E W none ((coefficientSequenceLimit l E W).obj N)`.
3. The actual counit is invertible in the derived strict-system category: the second conjunct
   is `IsIso (S.adjunction.counit.app N)`. It is a system morphism already, not a lift of a
   family of levelwise isomorphisms.
4. Its evaluation at n is the specified scalar-extension adjunct of the total-limit projection:
   `S.counit_projection N n` says exactly

   ```lean
   (coefficientFiniteAdjunction l E W n).homEquiv _ _
     ((S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj N) ≫
       (coefficientSequenceDerivedEvaluation l E W n).map (S.adjunction.counit.app N)) =
     (coefficientSequenceProjection l E W n).app N
   ```

   The inverse of `S.reductionEvaluation n` converts finite scalar extension of L(N) to
   evaluation of R(L(N)); applying the Hom equivalence identifies the map with the actual
   projection. Equivalently, applying the inverse Hom equivalence to that projection gives
   precisely this evaluated counit. This field holds for every N, so in particular for every
   normalized N. It carries the requested map identity without choosing a different counit.
5. For every complete K, the actual unit is invertible: the theorem's second conjunct is
   `∀ K, IntegralOnSlice.IsComplete l E W none K → IsIso (S.adjunction.unit.app K)`.
6. Naturality in N and K: these are literally `S.adjunction.counit.naturality a` and
   `S.adjunction.unit.naturality b`, for morphisms in their ambient derived categories and
   hence in the stated full subcategories. In Lean composition order unit naturality is
   `b ≫ S.adjunction.unit.app K' = S.adjunction.unit.app K ≫
   (S.reduction ⋙ coefficientSequenceLimit l E W).map b`.
   Counit naturality is
   `(coefficientSequenceLimit l E W ⋙ S.reduction).map a ≫ S.adjunction.counit.app N' =
   S.adjunction.counit.app N ≫ a`.
7. Both triangle identities are fields of the very `S.adjunction`:
   `S.adjunction.left_triangle_components P` and
   `S.adjunction.right_triangle_components N`. They say respectively
   `S.reduction.map (S.adjunction.unit.app P) ≫
   S.adjunction.counit.app (S.reduction.obj P) = 𝟙 _` and
   `S.adjunction.unit.app ((coefficientSequenceLimit l E W).obj N) ≫
   (coefficientSequenceLimit l E W).map (S.adjunction.counit.app N) = 𝟙 _`.
   No unrelated adjunction or arbitrarily selected isomorphisms are substituted.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing all the recorded coefficient-extension
  constructions in `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and its topology.
- `def-weil-size-convention` has a convention-only binding; no declaration is missing.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`, importing the actual completed
  ring with independent coefficient/site universes.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemCalculus`, inherited `reduction`, `adjunction`,
  `reduction_normalized`, `reductionEvaluation`, `counit_projection`.
- Its `Sheaf.Paper.CoefficientRingedSequenceSite` dependency gives
  `coefficientSequenceDerived`, `IsNormalizedCoefficientSequence`,
  `coefficientSequenceLimit`, `coefficientSequenceProjection` and derived evaluations.
- `Sheaf.Paper.NormalizedDVRTower`: `WeilConjectures.NormalizedDVRTower`, in particular
  its actual-transition universal Hom criterion, compared with the strict-sequence predicate.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `WeilConjectures.IntegralOnSlice.IsComplete`, whose
  none branch is the exact global Roos predicate, without an auxiliary finite-field restriction.

Edge cases checked before binding:

- n=0 means exponent 1, the residue coefficient level, not the zero quotient at exponent 0.
  The quantifier over all natural n covers exactly every positive level. m=n is included in
  the normalization predicate, including the identity quotient transition.
- The zero complex and zero strict system are permitted. No nonzero or cohomological lower
  bound appears. Arbitrarily unbounded complexes are included.
- The empty scheme is permitted. The invertibility hypothesis makes sense in its global
  section ring and does not require a nonempty scheme or a geometric point.
- No finite-field datum, residue characteristic p or p ≠ l binder is introduced. The global
  completeness definition's existential finite-field presentation is auxiliary and ignores
  the scheme. Characteristic zero and mixed characteristic schemes with l invertible remain.
- Independent site and extension universes are retained, including either relative size.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query “The canonical reduction and derived inverse limit
  adjunction on unbounded sheaf complexes has invertible counit on normalized systems and
  invertible unit on derived complete objects”: 8 hits, including derived-adjunction counit
  formulas and condensed adjunctions; no reconstruction theorem for these sheaf systems.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.IsIso"`: 12 hits,
  including `Adjunction.toEquivalence`, fully faithful criteria and isomorphism instances;
  generic category theory, not the DVR reconstruction assertion.
- `msearch.py ... grep "normalized.*system|derivedComplete.*counit|reduction.*limit.*adjunction"`:
  zero Mathlib hits.
- `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf` with
  `normalized.*[Rr]econstruction|[Aa]ctualReconstruction|derivedComplete.*counit|lem-pur-normalized-actual-reconstruction-maps`:
  found `Sheaf/Paper/PurNormalizedReconstructionAdjunctionCalculus.lean`; reading it reveals
  the exact reconstruction theorem described above. No upstream declaration directly carried
  this new node id. The existing parent module already states the intermediate theorem.

No statement correction, new node, or dependency repair is necessary. No STATEMENT-DISPUTED
issue was found. The existing theorem remains a stage-2 statement with a sorry proof; this
binding does not claim the result is proved. Its older docstring proposes a Nakayama route
for the unit. The present node supplies the newer complete six-step proof plan, in particular
its Roos/intrinsic comparison and naturality argument; stage 3 should follow that DAG proof
rather than infer that a proof was supplied here.

Validation: the delivery wrapper's existing-declaration probe imports the existing module
and checks the fully qualified theorem on the server; the dry run also runs preflight.

## Second reading by Q03

No second worker was started, as required by the dispatch brief. The maintainer's independent
review reads this existing binding and its clause correspondence. Worker self-check: read the
node and existing theorem together, then inspected the inherited reduction/projection fields,
normalization criterion, and global completeness branch. All clauses are represented above;
no source or dependency was changed.
