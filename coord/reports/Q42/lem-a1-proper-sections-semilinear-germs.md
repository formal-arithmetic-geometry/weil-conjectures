## Worker report

Q42 states `lem-a1-proper-sections-semilinear-germs` in
`lean/Sheaf/Paper/ProperSectionsSemilinearGerms.lean`. Nothing is proved. There are
three named postponed theorems: the two moving-point properties already asserted
in the node; the finite-extension formula and naturality; and the algebraically
closed formula and naturality. Each has a source/blueprint docstring and a full
proof plan. The other declarations are actual constructions of this node's
canonical maps. No arbitrary map or arbitrary natural isomorphism is an input.
The node statement and proof are retained. The statement-dependency list gains the three
already-landed owners of the canonical helper declarations used below; no dependency
node is restated or changed.

The retained earlier report described an unavailable published olean. That
artifact failure has cleared: the import-only probe compiled, and the new full
module compiled through scompile.py. The retained abstract draft under scratch/
is explicitly invalid and is not a delivered module. The present construction
replaces that draft with the actual system counit and actual coefficient maps.

Hypotheses and objects, clause by clause:

1. The complete finite-field datum p,a,q,k0,k is `D : FiniteFieldDatum.{u}`.
   It includes the algebraically closed geometric field, its algebra structure,
   the finite base field and q=p^a. `Y₀ : Over (Spec (.of D.k₀))` is the specified
   scheme over that field. `[IsProper Y₀.hom]` includes separatedness and local
   finite type, and implies quasi-compactness, hence finite type. No extra
   locally-finite-type or quasi-compact hypothesis is imposed.
2. The prime and invertibility hypotheses are `(l : ℕ) [Fact l.Prime]
   [Fact (l ≠ D.p)]`. Prime invertibility on the point and geometric fibre uses
   the recorded proper-Frobenius instances. In the rational theorem the finite
   extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`. This is the dependency convention for any finite
   extension in the chosen closure; choosing its embedding introduces no further
   restriction. The algebraically closed theorem uses `(Ω : Type v) [Field Ω]
   [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`. Scheme and coefficient universes
   are independent, not identified to accommodate a specialized point API.
3. Y and its structure map are `(D.geometricFiber Y₀).left` and
   `(D.geometricFiber Y₀).hom`. The point s is `Spec (.of D.k)`.
   g is `(D.geometricFrobenius Y₀).hom`, and h is `(frobeniusPointIso D).hom`.
   These are the recorded geometric Frobenius with inverse-q field automorphism,
   not the absolute q-power scheme Frobenius.
4. `sfRationalConstructibleCategory` and
   `generalAlgebraicallyClosedConstructibleCategory` are precisely the recorded
   raw rationalization and common-stage pair category. Objects M are arbitrary
   in those categories. Neither a Weil structure nor finite Tor dimension is
   a binder or hidden subcategory condition here.
5. `rationalDerivedPullback` gives P_r and Q_r, using the existing
   `localPositivePower g r`/`localPositivePower h r`. This existing convention
   uses exponent r+1. Quantifying `(r : ℕ)` therefore covers exactly all positive
   exponents, including exponent one at r=0. It neither loses exponent one nor
   adds a degree-zero assertion. `localPullbackComposition` is exactly the
   scalar localization of `(integralPullbackComposition l E).choose` read in
   the dependency. No second composition comparison is introduced.
6. `ProperSemilinearGerms.rationalSections` is compact direct image at the
   identity compactification (`properFrobeniusRationalFunctor ... true`), then
   the recorded `pointRationalFibre`. Its one-step transport is the compact
   component `.2` of `frobeniusCohomologyTransportRational` with
   `Compactification.ofIsProper Y₀.hom`. Thus C is compact cohomology, with
   exactly the proper-case comparison in the node.
7. A k-point is the binder `z : Spec (.of D.k) ⟶ ...` together with
   `hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _`. The fibre C_z is the existing
   `rationalDerivedPullback l E z ⋙ pointRationalFibre`, named `rationalFibre`.
8. The germ is constructed, not postulated. `integralCounit` first uses the
   completed pullback realization, then applies `coefficientSequenceLimit.map`
   to the reconstruction counit followed by `systemAdjunction.counit`, and
   finally uses the inverse completeness unit. This is the counit of the
   ordinary direct image before any reduction. `integralGerm` precomposes with
   the inverse identity-pullback unit, transports along hz, uses the recorded
   integral compositor, and applies z-pullback to that counit. `rationalGerm`
   precomposes with `properFrobeniusRationalIso.hom`, localizes this integral
   arrow and applies the actual point fibre. The object comparison at its end
   only identifies the unchanged object of raw rationalization with the
   recorded rational-pullback object. In particular no equality is inferred
   merely from equality at finite coefficient reductions.
9. `movingPoint D Y₀ z r` is h^(-(r+1)) ≫ z ≫ g^(r+1) in Lean composition
   order, hence z_r=g^(r+1) z h^(-(r+1)) in the node's functional order.
   `movingPoint_properties` states both a_Y z_r=id and h^(r+1) ≫ z_r = z ≫ g^(r+1).
   Its named postponed proof is only of these two clauses already in the node.
   `rationalSquare` is the inverse h-power/z_r compositor, transport through
   that square equality, and the z/g-power compositor: exactly b_(r+1,z,M).
10. `rationalTransport` iterates the actual compact one-step transports, with
    the final inverse `localPullbackComposition` at each recursion. This is the
    uncontracted iteration followed by d_r^{-1}; reassociation is by the same
    specified coherent family. The point side reuses `localPointTransportIterate`
    unchanged. It is the successive actual restriction/insertion/kappa maps
    followed by the inverse Q-power compositor. No substitute fibre isomorphism
    is used. The recurrence orders agree with those in the node for r=1,2,3.
11. `rationalLeft` is tau followed by the germ at z on P_(r+1)M.
    `rationalRight` is the germ at z_(r+1), then the recorded iterated point
    transport on Lz_(r+1)^*M, then `pointRationalFibre.map rationalSquare.hom`.
    The first conjunct of `properSectionsSemilinearGermsRational` equates these
    arrows for every M. The second conjunct is their naturality square for every
    actual localized morphism f:M⟶N. Equality of the two sides makes naturality
    of the left side also naturality of the right side.
12. For Ω, `qbarLeft` and `qbarRight` use the actual stage `M.stage` of each
    recorded common-stage object, then `stageRealization.map`. The latter is
    the full-subcategory inclusion for bounded finite-dimensional point
    complexes followed by `frobeniusCohomologyCoefficientExtension` along the
    canonical finite-subfield embedding. This is exactly the derived realization
    used by `frobeniusTransportQbar`/`frobeniusCohomologyTransport`, including
    their ULift universe transports, not a new cohomology theory. It is faithful
    because scalar extension between fields is faithfully flat and bounded
    complexes over a field split into their cohomology; the endpoints remain
    bounded and finite dimensional. Thus writing the equality in ambient D(Ω)
    is equivalent to its equality in D^b_fd(Ω).
13. The first conjunct of `properSectionsSemilinearGerms` covers every actual
    common-stage object; its second conjunct gives naturality on all morphisms at
    each finite stage. Its third conjunct now explicitly relates these stages:
    for every common-stage object M, every coefficient stage L and every
    `h : M.stage ≤ L`, it states
    `realizedSourceComparison.inv ≫ qbarLeft M ≫ realizedTargetComparison.hom =
    stageRealization L |>.map (rationalLeft ... (M.toStage h))`.
    The source comparison is the existing `frobeniusCohomologyRealizedComparison`
    with `compact=true` at the identity compactification. The target comparison
    first uses the canonical balanced tensor tower and point-fibre scalar
    comparison, then the two actual `commonStagePullbackComparison`s for z and
    g^(r+1). No comparison is a theorem hypothesis or an arbitrary choice. Thus
    the formula is compatible with further coefficient extension, including the
    identity extension L=M.stage. Finite-stage naturality and this explicit
    compatibility yield naturality for a Pair morphism represented at a common
    stage, with endpoint comparisons, independently of further representatives.

Dependency declarations and imports (all statement/proof modules imported
explicitly; proof-only imports are non-public):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-rationalization-karoubi`: `Sheaf.Paper.SfRationalizationKaroubi`, `WeilConjectures.sfRationalConstructibleCategory`.
- `def-weil-algebraically-closed-coefficients`: `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-frobenius-detailed`: `Sheaf.AlgebraicGeometry.FrobeniusDetailed`, `WeilConjectures.FiniteFieldDatum.geometricFrobenius`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `lem-pod-integral-pullback-composition`: `Sheaf.Paper.IntegralPullbackComposition`, `WeilConjectures.integralPullbackComposition`.
- `def-weil-ordinary-compact-cohomology`: `Sheaf.Paper.CommonStageCompactWeilCohomology`, `WeilConjectures.commonStageCompactWeilCohomology`.
- `lem-pod-proper-coincidence-frobenius`: `Sheaf.Paper.ProperCoincidenceFrobenius`, `WeilConjectures.properCoincidenceFrobenius`.
- `def-weil-frobenius-cohomology-transport`: `Sheaf.SixFunctors.FrobeniusCohomologyTransport`, `WeilConjectures.frobeniusCohomologyTransport`.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`.
- `def-weil-finite-coefficient-point`: `Sheaf.Paper.FiniteCoefficientPoint`, `WeilConjectures.pointQbarFibre`.
- `def-weil-frobenius-point-transport`: `Sheaf.SixFunctors.FrobeniusPointTransport`, `WeilConjectures.frobeniusPointTransportQbar`.
- `def-weil-local-frobenius-trace`: `Sheaf.Paper.LocalFrobeniusTrace`, the recorded
  `localPullbackObjectIso`, `localPullbackComposition`, `localPositivePower`,
  `localPointTransportIterate` helpers (no Weil-object argument).
- `lem-trf-integral-pullback-comparison-realization`:
  `Sheaf.Paper.IntegralPullbackComparisonRealization`,
  `integralPullbackComparisonRealization`, `integralComparisonUnit`.
- `lem-weil-frobenius-cohomology-transport-iso`:
  `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`,
  `frobeniusCohomologyRealizedComparison`, `frobeniusCohomologyStageEmbedding_comp`,
  `frobeniusCoefficientTower`. All are existing canonical constructions; the
  isomorphism theorem itself is not an assumption of this statement.
- `fix-prop-adjunctions`: `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`, `AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction_comp_eq`.
- `def-weil-frobenius-square-exchange`: `Sheaf.Paper.FrobeniusGeometricExchange`, `WeilConjectures.FrobeniusExchange.frobeniusCommonStage`.
- `lem-amb-mate-unit-counit`: `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv_counit`.
- `lem-fix-operation-reduction`: `Sheaf.Paper.BasicOperationsCoefficientReduction`, `WeilConjectures.basicOperationsCoefficientReduction`.
- `lem-coef-semilinear-derived-sections`: `Sheaf.Paper.SemilinearDerivedSections`, `WeilConjectures.SemilinearSections.semilinearDerivedSections`.
- `prop-weil-pbc-rlim-functoriality`: `Sheaf.Paper.CompletedRlimFunctor`, `AlgebraicGeometry.Scheme.completedRlim_computation`.
- `lem-weil-frobenius-point-transport-natural`: `Sheaf.SixFunctors.FrobeniusPointTransportNatural`, `WeilConjectures.frobeniusPointTransport_natural`.

The owning helpers additionally reuse `FrobeniusExchange.models`, `systemAdjunction`,
`coefficientSequenceLimit`, `integralComparisonUnit`, `integralPullbackComparisonRealization`,
`localPullbackObjectIso`, `localPullbackComposition`, `localPositivePower`, and
`localPointTransportIterate`. The last four are in `Sheaf.Paper.LocalFrobeniusTrace`;
reading their full definitions confirmed they have no Weil-complex parameter.
The recorded ordinary/compact common-stage cohomology declaration is specialized
to Weil objects, but the underlying no-Weil functors are already provided by the
proper-Frobenius and compact-support dependencies; these are used directly.
Likewise the generic étale adjunction record is imported, while the actual completed
counit is formed from the recorded system adjunction and reconstruction maps.
There is no restatement or private copy of an existing definition.

Source check: read the local Deligne Weil II PDF, printed pp.150–153
(PDF pages 15–18), especially (1.1.3), (1.1.7), (1.1.10), (1.1.14): raw rationalization,
finite coefficient stages, geometric Frobenius as the inverse q-power substitution,
and action by transport of structure. Read `sites-cohomology.tex`,
`lemma-derived-pullback-composition` (0D6D) and `remark-base-change` (07A7):
compositors and the unit-square-counit mate construction. The node correctly calls
its derived formula an agent calculation using those sources; it is not quoted as
a verbatim Deligne theorem.

Edge checks: exponent one is r=0, and exponent two expands to the two successive
transports followed by the inverse compositor. The moving point is reparametrized,
not required to be fixed. For Y₀=Spec(k₀), all the geometry reduces to the base point
and the formula is point-transport naturality. A closed point of degree greater
than one still uses h^{-r}, so no false fixed-point condition is imposed. M=0 is
included in both categories; all maps then have zero source/target. An empty Y₀
has no z satisfying the point binder, so this is the intended vacuous pointwise
assertion. Characteristic l=p is explicitly excluded; any other prime, including
2, is permitted. No connectedness, smoothness, dimension or Weil structure was
introduced. Independent scheme/closure universes are retained.

Searches (current pass, in addition to retained searches.jsonl):

- `msearch.py ... leanfinder "Derived evaluation of global sections at a geometric point
  commutes with semilinear Frobenius transport and iterated pullback"`: eight
  structure-sheaf/residue-field evaluation hits, including Scheme.Γevaluation_naturality;
  no constructible derived-coefficient germ theorem.
- `msearch.py ... loogle '"counit", "mate"'`: two hits,
  CategoryTheory.mateEquiv_counit and mateEquiv_counit_symm. The former is exactly
  the already recorded generic mate leaf; it does not state this geometric theorem.
- `msearch.py ... grep 'semilinear.*germ|germ.*transport|stalk.*transport'
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "Evaluation of derived global sections at geometric points
  commutes with semilinear Frobenius transport"`: eight unrelated residue-field
  or smooth-sheaf evaluation hits; no exact match.
- `rg` in WeilConjectures and lean/Sheaf for semilinear/germ/transport, together
  with the exact node-id grep in WeilConjectures: no exact statement. Existing
  LocalFrobeniusTrace gives the compositors and point iteration reused here, but
  its Weil-object return comparison is a different, fixed-return construction.
- Exact `properSectionsSemilinearGerms` search in Mathlib/upstream-name records,
  WeilConjectures and lean/Sheaf: no existing declaration before this delivery.

No statement dispute, statement correction, new node or dependency module is required.
The helper maps and moving-point facts belong to the same notion and are all listed
in this item's lean.declarations, with the same blueprint tag.

## Returned delivery repair

The maintainer returned immutable head d28e179ceca8 for H3: both original Qbar
conjuncts were direct images of the rational theorem and did not state the
compatibility with further coefficient extension required by node proof step 8.
The initial saved-packet dry run passed at commit 6e3f3e88d9, confirming that this
was a statement-content defect and not a compiler/preflight failure. That packet
was not pushed. The present repair adds the reviewer's explicitly offered second
alternative, as the third conjunct described in clause 13 above. It states a
new equality involving the original `qbarLeft M` and its canonical source/target
comparisons at every larger stage. This cannot be obtained just by applying
`Functor.map` to the rational equality/naturality at one fixed stage: it relates
the normalized scalar comparison maps to the counit/exchange/point-transport word.
The Qbar proof docstring now explains the factorwise coefficient-compatibility
argument for this exact conjugation clause.

The three helper definitions `realizedPointComparison`, `realizedTargetComparison`
and `realizedSourceComparison` have real data and are recorded in lean.declarations.
Their source and blueprint docstrings are in the owning module. No additional
postponed theorem is introduced. The report's earlier assertion that quantification
over finite-stage arrows alone tests full common-stage naturality was incorrect
and has been replaced by the explicit clause-by-clause account above.

The advisory about uncited helper owners is addressed by adding the already-landed
`def-weil-local-frobenius-trace`,
`lem-trf-integral-pullback-comparison-realization`, and
`lem-weil-frobenius-cohomology-transport-iso` to stmt_deps. An audit of both
statement and proof dependency edges found no path from any of those owners
back to this item. The six non-public proof imports are retained as required by
stages/2-statements.md §3(7). The identity-pullback unit and compositors are the
existing simultaneous-system constructions; their coherence is the standard
normalization already accepted by the stage-1 review, not a new input.

Additional repair search: msearch.py loogle on the fully qualified proposed
`realizedTargetComparison` name returned zero hits; rg for the three proposed
helper names in Mathlib, WeilConjectures and lean/Sheaf returned no hits.
Read the existing realized-source comparison, balanced coefficient tower,
pointRationalFibreScalarIso and commonStagePullbackComparison in full before
composing them, including their normalization and endpoint clauses.

## Second reading by Q42

This dispatch forbids other agents and assigns the independent reading to the
maintainer. This is therefore an explicitly identified worker self-check.

With the final node and module open, rechecked clauses 1--12 against the retained
construction and clause 13 against the new third conjunct. The datum, properness,
prime inequality, independent universes, arbitrary non-Weil object, actual counit,
identity compactification, moving point, oriented square, positive powers,
transport recursions and rational naturality are retained. For the returned H3
point, checked that the new quantifiers are over an actual Pair object M and
all L ≥ M.stage; both endpoints use the same `M.toStage h`. The inverse source
comparison changes enlarged compact sections back to M's original source;
the original `qbarLeft M` then lands in the original derived fibre of P_r M;
the forward target comparison changes that fibre to the enlarged derived fibre.
This is the requested conjugation orientation. The canonical comparisons preserve
independent universes and do not require L to be a strict extension.

New edge checks: L=M.stage is included without identifying the recorded transition
with a literal identity; the stage-system unit/tensor comparisons handle it.
For M represented at different finite fields, choose a common L and use the new
clause at each endpoint, followed by the existing finite-stage naturality square.
After a further extension, the same clause and the canonical tensor tower compare
the new representative. M=0 and r=0 (exponent one) remain covered. All helper
maps are explicitly constructed and every theorem proof remains `by sorry`.

Validation: the repaired full module compiled through scompile.py in both its
sandbox and library forms (17.4 s and 16.5 s), with no errors or warnings.
The final delivery dry run and push are run after installing this record.
