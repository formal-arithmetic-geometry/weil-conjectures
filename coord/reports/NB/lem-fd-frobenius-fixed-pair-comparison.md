## Worker report

The module `Sheaf.Paper.FrobeniusFixedPairComparison` states
`WeilConjectures.frobeniusFixedPairComparison`, with its entire proof `sorry`.
Its three auxiliary definitions are explicit Prop-valued descriptions of the
conclusion of this same node; they introduce no replacement categories, maps,
or new independent notions. No dependency node or mathematical statement was
changed, and no new DAG node is needed.

Source read: the current main-20261015 blueprint
`sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`, final sentence,
and the item's complete ten-step auxiliary proof, extracted from the coefficient
comparison's old steps 10–11. The blueprint's final sentence puts local Frobenius
in the PBC coefficient category. This auxiliary gives precisely the transport
from the framework category for a system already supplied. It makes no assertion
of existence of that system or of scheme-composition coherence.

Hypothesis and clause correspondence:

- The global `(p,a,q,k₀,k)` is `(D : FiniteFieldDatum.{u})`. This recorded structure
  includes prime p, positive a, q=p^a, the cardinality of k₀, and an arbitrary
  specified algebraic closure k with its algebra structure.
- The prime l is `(l : ℕ) [Fact l.Prime]`; `hl : l ≠ D.p` is explicit and is used
  by the recorded framework Weil categories. The arbitrary algebraic closure
  of Q_l is `(Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]
  [IsAlgClosure ℚ_[l] Ω]`. Its universe w is independent of scheme universe u.
- A separated finite-type k₀-scheme is
  `X₀ : Over (Spec (.of D.k₀))`, with `[LocallyOfFiniteType X₀.hom]`,
  `[QuasiCompact X₀.hom]` and `[IsSeparated X₀.hom]`. Finite type is exactly the
  first two classes, as specified by the recorded finite-type node; properness
  is not assumed.
- The geometric fibre is exactly `(D.geometricFiber X₀).left`, with no alternative
  model. Its geometric Frobenius is `D.geometricFrobenius X₀`, already typed as an
  `Aut` of this scheme, with the recorded arithmetic-Frobenius inverse. No
  morphism-over-k condition is imposed.
- The supplied simultaneous datum is `S : FdCoefficientComparisonSystem.{u} l Ω`.
  It quantifies over all allowed schemes and includes the realization and mixed
  scalar comparisons. The theorem is universally quantified in S and does not
  assert its existence or impose an additional coherence condition.
- The three geometric conclusions are existential witnesses `_hN : IsNoetherian X`,
  `_hD : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)`, and
  `_hI : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))`. These are conclusions,
  not hypotheses. They are supplied explicitly to `FdGeometricFixedPairComparison`.
- `FdGeometricFixedPairComparison` includes both an equivalence from
  `sfCommonStageWeilComplex D l hl X₀ Ω` to the actual PBC common-stage fixed pairs
  and one from `sfWeilComplex D l hl X₀ (pbcFiniteField l Ω E)` for every finite
  `E : Padic.FiniteCoefficientFields l Ω` to the actual PBC finite fixed pairs.
  Their functors are fixed by HEq to `IsoAlgebra.mapOfNatIso` of the supplied
  common `.pair` and finite `.rational` comparisons. This includes the specified
  framework Weil categories explicitly, rather than silently choosing another
  category of pairs or a derived category of Weil sheaves.
- The functor formula is the existing `IsoAlgebra.mapOfNatIso`. Its object is
  J(K) with structure `e.app K ≪≫ J.mapIso theta`, and its arrow has underlying
  map `J.map u`. Here e is the reverse comparison recorded by S, so e equals
  the inverse of b in the orientation of the node. The formula is exactly
  `J(theta) ∘ b_K⁻¹`, including its specified arrow map.
- `FdFixedPairComparison` asserts `IsEquivalence` of these exact finite and
  common transport functors. `Functor.IsEquivalence` supplies full faithfulness
  and essential surjectivity. Since `IsoAlgebra` arrows consist of just an
  underlying arrow satisfying the intertwining equation, the resulting Hom
  bijection is exactly the restriction of the J Hom bijection. No independently
  chosen Hom equivalence is substituted.
- Scalar compatibility is `FdFixedPairSquare` with the reverse `.sfFamily.β e`,
  the finite comparisons b_E and b_L, the reverse PBC `.β e`, and the inverse
  coefficient `.family.β e`. Its result is a natural isomorphism of the two
  actual lifted composites, whose every underlying component equals that
  specified coefficient comparison. It ranges over every E≤L, including E=L.
- Finite-to-common compatibility uses both pullback families'
  `.ιCompFunctorIso E`, the common comparison c, b_E, and the coefficient
  family's `.ιCompFunctorIso E`. The natural isomorphism again has exactly the
  supplied underlying coefficient component. Equalities of pair arrows are
  detected on their underlying arrows, so the inherited identity and scalar
  cocycle equations are retained without adding scheme-composition assumptions.
- In this predicate b and c are existentially quantified with HEq to the supplied
  finite and common comparisons. These equalities determine them, merely
  transporting dependent endpoints to the stage-family presentation. The actual
  pullbacks are fixed by `sfFinite` and `sfPair`; coefficient endpoints by
  `finite_functor` and `pair_functor`. There is no arbitrary-map hypothesis or
  unsupported choice from a mere existence assertion.

Recorded dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `.geometricFiber`, and the coefficient conventions in its docstrings.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`
  (defined in its Separated import), with the actual closed diagonal definition;
  `IsProper` was read and is deliberately not a hypothesis.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  its QuasiCompact import's `QuasiCompact` for finite type.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`, `galoisMap`,
  `galoisMap_inverse`, the projection identities and affine formula. It is a
  scheme automorphism, not necessarily an automorphism over k.
- `Sheaf.Paper.FdCoefficientComparisonSystem`:
  `WeilConjectures.FdCoefficientComparisonSystem` and `FdPullbackSystem`:
  coefficients, finite rational comparisons, actual-family identifications,
  mixed square, common comparison and its finite-component normalization.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `rationalPullbackScalarComparison`, `commonStageDerivedPullback`,
  `commonStagePullbackComparison`, and their unique prescribed object/map
  characterizations; these are retained through the supplied datum.
- `Sheaf.Paper.PbcQbarCompletedPullback`:
  `AlgebraicGeometry.Scheme.pbcQbarPullFamily` and `pbcQbarCompletedPull`.
  Both use the actual completed pullback and normalized scalar comparisons.
- `Sheaf.Paper.SfWeilSheafComplex`: `WeilConjectures.sfWeilComplex`,
  `sfCommonStageWeilComplex`, the finite/common Frobenius pullbacks, and
  `sfWeilStageObject`. This supplies exactly the framework categories in the
  statement, including their specified forgetful functors.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `AlgebraicGeometry.Scheme.integralStratifiedPerfectCharacterization` and
  `integralStratifiedPerfectDetailed`, used via the supplied coefficient datum
  to fix its ambient categories under the stated geometric hypotheses.
- Proof dependency `Sheaf.Paper.FdCoefficientComparison`:
  `WeilConjectures.FdCoefficientComparison`, its stage equivalences,
  `.family`, `.finite_functor`, `.pair_functor` and scalar comparisons.
- Proof dependencies `Mathlib.AlgebraicGeometry.Noetherian`:
  `LocallyOfFiniteType.isLocallyNoetherian`, `IsNoetherian`, the Noetherian Spec
  instance, and QuasiCompact's `compactSpace_of_compactSpace`.
- Proof dependency `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.exists_topologicalKrullDim_le`, with exactly a finite-type
  structure map to Spec of a field and a natural-number dimension bound.
- Proof dependency `Mathlib.CategoryTheory.Equivalence`:
  `CategoryTheory.Functor.asEquivalence` and `Functor.IsEquivalence`.
- Shared constructions reused directly:
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra` supplies
  `CategoryTheory.Endofunctor.IsoAlgebra`, `mapOfNatIso`, its object/structure
  and morphism formulas, and its faithful forgetful functor.
  `WeilConjectures.CategoryTheory.StageSystem.Functor` supplies actual family
  scalar comparisons and the normalized `ιCompFunctorIso`.

Edge cases checked by reading the source and the resulting signatures: the empty
scheme is permitted; its dimension ⊥ is bounded by a natural number and its
local-unit condition is vacuous. No nonempty hypothesis appears. Zero objects
and all structure isomorphisms remain in IsoAlgebra, with the original underlying
Hom sets. Identity coefficient inclusions E=E are included. The closure k/k₀ is
not required to be finite; only the base-changed structure morphism to Spec k
is finite type. The algebraic closure Ω may have an independent universe. The
scheme Frobenius is allowed to be semilinear. l=p is excluded exactly as stated.
No STATEMENT-DISPUTED flag and no node fault was found.

Searches actually run:

- msearch.py leanfinder: "A coefficient equivalence commuting with Frobenius
  pullback induces an equivalence of Weil fixed pair categories compatible with
  scalar extension and stage inclusions". Eight hits, headed by Witt-vector
  isocrystal Frobenius equivariance and isocrystal equivalences; no match for
  this statement on actual sheaf coefficient systems.
- msearch.py loogle: "CategoryTheory.Functor.IsEquivalence,
  CategoryTheory.Endofunctor". Zero hits; the service reported unknown identifier
  CategoryTheory.Endofunctor. This is not recorded as evidence that the project
  IsoAlgebra construction is absent.
- msearch.py grep: "IsoAlgebra|mapOfNatIso|geometricFrobenius". One Mathlib hit,
  AlgCat.algEquivIsoAlgebraIso, unrelated to fixed pairs of an endofunctor.
- msearch.py leansearch: "An equivalence commuting with two endofunctors induces
  an equivalence of fixed pair categories preserving the underlying morphism
  bijection". Eight hits, including algebra/coalgebra adjunction equivalence,
  Under.post equivalence, congrLeft and join equivalence; no exact match.
- rg of project Sheaf and WeilConjectures for fixed pairs and Frobenius found the
  existing IsoAlgebra API and RationalCoefficientCategoryComparison. The latter's
  FdFrobeniusComparison structure supplies finite/common equivalences, but omits
  the scalar and stage-inclusion clauses of this item; its theorem also asserts
  existence of S, whereas here S is given. It cannot be an existing attachment.
- rg of both source roots and dag/lean_names_upstream.json for the four delivered
  names found none. grep by this item's exact id in WeilConjectures found none.

Validation: scompile.py compiles this single module in both sandbox and library
presentations, with no errors or warnings (5.3 s and 5.5 s on the final compile).
Initial attempts to identify dependent finite coefficient models directly made
elaboration expensive. The final formulation retains their given HEq endpoint
identifications explicitly and compiles within the unchanged 60-second limit.
Only the node's lean field changes; its signature is copied verbatim from the file.

Independent review is performed by the maintainer after direct delivery, as the
worker brief specifies. No second-worker reading is claimed here.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
