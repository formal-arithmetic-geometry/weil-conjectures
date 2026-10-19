## Worker report

The module Sheaf.AlgebraicGeometry.UniformizationCompleteLocalDescent defines
AlgebraicGeometry.HasRegularAlterationCover, the proposition U_ell(S,Z) introduced
in this node, and states AlgebraicGeometry.uniformization_complete_local_descent.
Its only theorem proof is `sorry`; the helper proposition is written in full.
No statement correction, dependency repair, or new DAG node is needed.

Read the node and all nine statement dependencies, their records and source
signatures/docstrings. Read ILO III 6.1--6.2, printed pp. 43--45 (PDF pages 49--51),
and IX 1.3, printed p. 132 (PDF page 138). III 6.2 explicitly reduces to normal
integral local rings before completion; IX 1.3 uses the dimension-bounded
reduction in an induction. The node's corrected seven-step proof plan is included
in the theorem docstring, including punctured-scheme gluing rather than the
source's invalid prime-to-ell open-shrinking shortcut. Stage 3 must prove that
corrected plan; no claim that the erroneous shortcut works is introduced.

Hypotheses and conclusions, clause by clause:

- A fixed prime ell is `(ell : ℕ) [Fact ell.Prime]`.
- A reduced Noetherian scheme is `(S : Scheme.{u}) [IsReduced S]
  [IsNoetherian S]`. The latter means locally Noetherian and quasi-compact,
  equivalently a finite affine Noetherian cover.
- Quasi-excellence is `∀ U : S.affineOpens, IsQuasiExcellent Γ(S, U)`.
  This uses the recorded ring predicate on every affine open, without adding
  universal catenarity or a finite-dimensionality requirement.
- Invertibility on S is `∀ s : S, IsUnit (ell : S.presheaf.stalk s)`.
- A nowhere dense closed subset is `Z : Set S`, `IsClosed Z`, and
  `IsNowhereDense Z`; no scheme structure on Z is selected or required.
- In U_ell, `∃ base : PrimeToEllAlteration.Alt S,
  base.obj = Over.mk (𝟙 S)` specifies precisely the identity over S as the
  target. `n : ℕ`, `T : Fin n → Alt S`, and `q : ∀ i, T i ⟶ base`
  specify a finite family in alt/S. The structural arrows `(T i).obj.hom`
  are the underlying morphisms to S. `IsCoveringFamily ell T q` uses exactly
  the recorded generated-sieve alteration topology, not mere surjectivity.
- Every source is regular Noetherian by
  `∀ i, IsRegularScheme (T i).obj.left ∧ IsNoetherian (T i).obj.left`.
- Every inverse image is the support of an SNC boundary by the existential
  `H : (T i).obj.left.IdealSheafData`, `IsStrictNormalCrossingsBoundary H`,
  and `(H.support : Set (T i).obj.left) = (T i).obj.hom ⁻¹' Z`.
  This is equality of underlying closed subsets, not equality of nonreduced
  inverse-image subschemes. The boundary definition permits zero components.
- Normal complete local Noetherian bases are `Spec (.of A)` with
  `[CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  [IsIntegrallyClosed A]` and
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`. For a Noetherian local
  scheme normality is equivalently its affine ring being an integrally closed
  domain: localizations of an integrally closed domain are integrally closed,
  and the converse includes the stalk at the closed point. Thus these ring
  binders express all the stated normal complete local bases, with no henselian,
  characteristic, coefficient-field, or extra excellence hypothesis. `IsUnit
  (ell : A)` expresses the same invertibility condition on this affine scheme.
  Z has the same closed/nowhere-dense hypotheses as in the conclusion.
- The first conjunct is the unbounded implication from all such complete local
  pairs to all reduced quasi-excellent Noetherian pairs. There is no dimension
  binder or finite-dimensionality hypothesis anywhere in that conjunct.
- The second conjunct quantifies `∀ d : ℕ`, exactly the integers d ≥ 0, and
  adds `topologicalKrullDim (Spec (.of A)) ≤ d` only to the complete local
  hypothesis and `topologicalKrullDim S ≤ d` to the general conclusion.
  Dimension uses precisely the supremum of irreducible-closed chain lengths,
  valued in `WithBot ℕ∞`, with the natural number bound coerced into that type.

Dependency interfaces used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsReduced.
- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing; scheme Noetherianity is
  Mathlib.AlgebraicGeometry.Noetherian.AlgebraicGeometry.IsNoetherian.
- Sheaf.RingTheory.ExcellentRing: IsQuasiExcellent, built from IsGRing and
  openness of the regular locus of every finite-type algebra.
- Sheaf.AlgebraicGeometry.IsRegularScheme: AlgebraicGeometry.IsRegularScheme,
  imported through the boundary module, includes local Noetherianity.
- Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary:
  AlgebraicGeometry.IsStrictNormalCrossingsBoundary, with genuine ideal data.
- Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology:
  AlgebraicGeometry.PrimeToEllAlteration.Alt and IsCoveringFamily, which uses
  topology. All its objects have the required reduced finite-type,
  maximally dominant, generically finite structural morphisms.
- Mathlib.RingTheory.AdicCompletion.Basic: IsAdicComplete, equivalent to
  bijectivity of the canonical map into AdicCompletion (of_bijective_iff).
- Mathlib.Topology.KrullDimension: topologicalKrullDim.

The already stated proof interfaces are imported non-publicly:
AlterationCoverCalculus.alteration_cover_calculus,
CompletelyDecomposedEtaleFiniteSubcover.completelyDecomposed_etale_finite_subcover,
CompleteLocalExcellent.isExcellent_of_isNoetherianRing_of_isAdicComplete,
CompletionDimension.RingTheory.completion_dimension,
HenselianPairApproximation.henselian_pair_approximation, and
Mathlib.RingTheory.FinitePresentation.Algebra.FinitePresentation.of_finiteType.
Here the leading file names identify their modules, not declaration namespaces;
the scheme declarations are in AlgebraicGeometry (the calculus is additionally
in PrimeToEllAlteration), and the excellence and approximation declarations are
at the root. Other proof nodes lack recorded statements and are described in the
proof docstring; they are not required to type this statement. No downstream
uniformization module is imported.

Edge cases checked before writing and on rereading: the empty scheme has
Krull dimension minus infinity and permits n = 0, so it is included for every
bound. Empty Z is allowed: the SNC definition's zero-component boundary is
permitted. Dimension zero and d = 0 appear without exceptional restrictions.
A nonempty S cannot be covered by the empty family in this generated topology;
we do not assert that it can. Complete local bases are nonzero because local
rings/domains have that convention; normal local schemes are nonempty spectra.
No connectedness or irreducibility restriction is imposed on general S or on
members of the final covering. No finite global dimension or common bound on
all local dimensions is assumed in the unbounded clause. All scheme/ring
objects use the same arbitrary universe u; finite index sets lose no finite
family and there is no independent lower test-ring universe.

Searches actually run:

- msearch leanfinder: "Approximation reduction regular alteration coverings strict
  normal crossings from complete normal local bases to quasi excellent schemes".
  Eight hits, concerning affine transition limits, normalization, smooth loci,
  and etale objects. None is this reduction theorem.
- msearch loogle: `"IsAdicComplete", "IsLocalRing"`. One hit:
  isLocalRing_of_isAdicComplete_maximal. It supplies a local-ring property,
  not alteration uniformization.
- msearch grep: `uniformi[sz]ation|approximation.*alteration|alteration.*complet`.
  Zero Mathlib hits.
- msearch leansearch: "regular alteration covering descent from complete local
  schemes with normal crossings boundary". Eight hits on descent of general
  morphism properties, reducedness and normalization. None is this assertion.
- rg in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the node id,
  uniformization/Uniformization/IsQuasiExcellent and the alteration approximation
  patterns: no corresponding declaration. The literal node-id search also found
  no match. No matching full declaration name in dag/lean_names_upstream.json.
- rg in lean/Sheaf for IsQuasiExcellent, uniformization, and regular alteration
  covers found UniformizationNodalQuotientReduction, RegularPairAlterationPullback,
  and PrimeToEllUniformizationStandardForm. Read their relevant interfaces.
  The first uses the same fully expanded U_ell conclusion but states a distinct,
  downstream nodal-model implication; it cannot supply complete-local descent.
  There is no existing declaration of HasRegularAlterationCover or
  uniformization_complete_local_descent. The helper abbreviates exactly the
  proposition introduced by this item, and copies no existing named definition.

Validation: scompile.py compiled this module both as a sandbox module and under
its final library name, cleanly (2.1 s and 2.0 s); no warnings or errors.

## Second reading by Q89

A fresh reading compared the final Lean file with the node and ILO III 6.2 and
IX 1.3. The two conjuncts preserve the direction of implication, and only the
bounded conjunct uses d. Each general-pair antecedent includes reducedness,
Noetherianity, quasi-excellence on all affine opens, stalkwise invertibility,
and closed nowhere-dense Z. Each complete-local antecedent uses the maximal
ideal for completeness and an integrally closed domain for normality; it adds
no finite-dimensionality requirement to the unbounded clause. Expanding
HasRegularAlterationCover gives exactly the recorded alteration topology,
a finite family, regular Noetherian sources, and exact inverse-image supports
of SNC boundaries. The identity target equation avoids assuming a separately
constructed base object, and boundary existence does not choose hollow data.
The empty boundary and d = 0 cases remain present. No mismatch or change was
found on this second reading. No theorem has been proved at stage 2.
