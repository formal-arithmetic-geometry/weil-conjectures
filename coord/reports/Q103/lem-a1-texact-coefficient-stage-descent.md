## Worker report

The delivery states `CategoryTheory.CoefficientStageDescent.texact_coefficient_stage_descent`
in `Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent`. Its sole theorem proof is
`sorry`. All eleven declarations are recorded in `lean.declarations`; the other ten are
transparent abbreviations, genuine constructions, structures, or explicit predicates packaging
this lemma's hypotheses and conclusions. There are no new independent notions, dependency
repairs, statement changes, or disputed statements. The node changes only in `lean`.

The input and output structures are fully expanded in this module and have source/blueprint
docstrings. No comparison is selected from an unspecified existence assertion. In particular,
`FractionExtension` is the characterization of the functor already supplied in the statement,
not an arbitrary extra functor: it fixes every object, every pure-tensor map, the identity
factorization through localization, and its compatibility with the specified shift.

Hypothesis-by-hypothesis rendering:

1. The prime is `l : ℕ` with `[Fact l.Prime]`. The fixed closure is `Ω : Type w` with
   `[Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`. A temporary `#check @...`
   confirmed that the algebraic-closure hypothesis survives elaboration; it was removed.
   The index is exactly `Padic.FiniteCoefficientFields l Ω`, not an arbitrary directed type.
2. `integralRing l Ω E` abbreviates `Padic.coefficientExtensionIntegers l E.val`.
   `rationalStage l Ω E C` is exactly `ScalarLocalization` at the recorded
   `Padic.coefficientExtensionUniformizer l E.val`. The existing scalar-first Hom tensor
   order is identified with the node's Hom-first order by tensor commutativity.
3. `C₀ E`, `D₀ E` have the recorded category, preadditive, linear, zero-object, integer-shift,
   additive-shift, pretriangulated, and triangulated structures. The theorem explicitly
   binds linearity of every integral integer shift. Object and morphism universes for C₀
   and D₀ are separate; no universe equality is introduced.
4. `tC₀`, `tD₀`, `tC`, `tD`, `tCΩ`, `tDΩ` are the corresponding `TStructure`s.
   `hC₀`, `hD₀`, `hC`, `hD`, `hCΩ`, `hDΩ` assert `bounded = ⊤` separately in each case.
5. `hLC`, `hLD : IsLocalizedTStructure ...` give the stipulated rational triangulation
   and the isomorphism closures of the integral halves at zero. The triangle clause is
   an iff, including the shifted third arrow via the actual `Q.mapTriangle`. This is the
   reading of the node already documented in its stage-1 independent review. Both aisle
   clauses are also iff statements with explicit integral objects and isomorphisms.
6. `SC`, `SD : StageSystem ...` supply the rational coefficient transition functors,
   associators, and their cocycle equations. Their `CommShift` and `IsTriangulated`
   instances give exactness; `hTC`, `hTD` give t-exactness. The associators commute with
   shifts. `unitC`, `unitD`, their shift compatibilities and left/right unit equations
   spell out the supplied identity comparisons, which the generic StageSystem does not
   itself store. These are the usual identity/tower data, not strictification assumptions.
7. The pair categories are exactly `SC.PairCategory`, `SD.PairCategory`. The imported
   upstream implementation uses common-stage representatives modulo equality after further
   extension, giving the directed Hom colimits and their prescribed composition. Its actual
   triangulation consists precisely of triangles isomorphic to an included stage triangle.
   No extra pair category, completion, faithful transition, or abstract replacement is used.
8. `hCΩle`, `hCΩge`, `hDΩle`, `hDΩge` are the stipulated isomorphism closures of the
   finite-stage halves. `hTruncC`, `hTruncD : TruncationsComputedAt ...` explicitly assert
   finite-stage computation of both truncations with their canonical counit/unit maps.
   These hypotheses were retained even though they can be derived from the other data.
9. `F₀ E` has `Additive`, `Linear (integralRing ...)`, `CommShift ℤ`, and
   `IsTriangulated`. `hF₀` says it preserves each of the integral halves at zero. Shifts
   recover all integer cutoffs; no t-exactness of a rational F is assumed.
10. `M.Φ E` is the additive fraction extension F_E. `hF E : FractionExtension ...`
    fixes its object formula and its tensor-Hom map by `HEq`, allowing the dependent
    endpoints without an arbitrary cast. The `factor` components are identities and
    `factor_shift` fixes the rational shift comparison to the localized integral one.
11. `M.β h` is the supplied natural isomorphism
    `F_E ⋙ T_D ≅ T_C ⋙ F_L`. `M.coh` is its tower equation; the corresponding
    `NatTrans.CommShift` instances give shift compatibility. `hbetaId` is precisely its
    identity-stage normalization under `unitC` and `unitD`.
12. F_Ω is the existing, fully specified `M.functor`. Its object is `(E, M.Φ E K)`;
    `Morphism.mapAt` and `functor_map_mkHom` give the node's conjugation formula
    `β_source ≫ F_L.map u ≫ β_target.inv` in Lean's left-to-right composition order.
    It is not an arbitrary supplied functor on the pair categories.

Conclusion-by-conclusion rendering:

1. The outer existential supplies F_Ω's `CommShift ℤ`; its normalization equation for
   every `E`, `X`, `n` is exactly the stage image of F_E's shift comparison. Thus the
   theorem asserts existence of this descent data instead of assuming it.
2. `cE E : Comparisons (tC E) (tD E) (M.Φ E)` and
   `cO : Comparisons tCΩ tDΩ M.functor` give exactness and t-exactness in their `exact`
   and `tExact` fields. The auxiliary `cTC`, `cTD`, `cJC`, `cJD` record the same canonical
   comparisons for the transitions and inclusions that occur in the coherence equations.
3. `Comparisons.heart` expresses preservation of the intersection of the halves.
   `heartRestriction` is the actual `ObjectProperty.lift` of `heart.ι ⋙ F`, so its
   maps are exactly F's maps. `heartAdditive` and `heartExact` state additivity and
   preservation of every short exact sequence in the abelian heart. No exactness in the
   ambient triangulated category is substituted for short exactness in the heart.
4. `Comparisons.le m` uses `truncLT (m + 1)`, hence τ≤m; `ge m` uses `truncGE m`,
   hence τ≥m. `le_counit` and `ge_unit` are exactly the two displayed canonical-map
   equations. `le_unique` and `ge_unique` quantify over competing natural isomorphisms
   satisfying those same equations and identify them with the respective comparison.
5. `cohomology t j` is `(truncLT (j + 1) ⋙ truncGE j) ⋙ [j]` up to definitional
   associativity, exactly the node's H^j. `Comparisons.q j` is a natural isomorphism,
   and `q_formula` fixes its hom as the specified integer shift comparison followed by
   shifted α⁺ at τ≤j X followed by shifted τ≥j applied to α⁻. This is the formula of
   proof Step 9, for every integer j, including negative j.
6. `SquareCompatible (cE E) (cE L) (cTC ...) (cTD ...) (M.β h)` spells out the three
   beta equations, separately for τ≤m, τ≥m, and H^j. The two `CompositeCompatible`
   equations for `SC.assoc`, `SD.assoc` identify the successive comparisons with the
   comparison of the tower composite. Together with the input `M.coh`, these are the
   compatibility with successive coefficient extensions. Reflexive inclusions are retained.
7. The square with `M.ιCompFunctorIso E` identifies the Ω comparison with the included
   finite-stage comparison under the canonical truncation identifications `cJC`, `cJD`.
   It includes both truncations and cohomology. The final two composite equations, using
   `SC.transIso h` and `SD.transIso h`, identify these inclusion comparisons after every
   further enlargement. Combined with the beta square, this is the explicit independence
   of the finite-stage representative; it does not assert unjustified faithfulness.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`,
  `finiteCoefficientCompositum`, `finiteCoefficientFields_properties`,
  `finiteCoefficientBase`. The already existing directed/nonempty instances are imported
  from `Sheaf.Paper.FiniteStagePairCategory`, rather than declared again.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension` import: `Padic.coefficientExtensionIntegers` and
  `coefficientExtensionUniformizer`; the positive-level finiteness declaration was read,
  but the abstract node needs neither finite quotients nor extra choices of them.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear`;
  `Mathlib.CategoryTheory.Linear.LinearFunctor`: `Functor.Linear`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`, `.Functor`:
  `Pretriangulated`, `IsTriangulated`, `Functor.IsTriangulated`, and `mapTriangle`.
- `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`, `.Heart`, `.TruncLTGE`:
  `TStructure`, `bounded`, `heart`, `truncLT`, `truncGE`, `truncLTι`, `truncGEπ`.
- `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization`, `localization`, and
  the actual tensor-Hom category/linear instances, not merely the earlier existence theorem.
- `WeilConjectures.CategoryTheory.StageSystem.Basic`, `.Functor`, `.Pretriangulated`,
  `.Triangulated`: `StageSystem`, `Morphism`, `PairCategory`, `Morphism.functor`,
  `Morphism.mapAt`, `Morphism.ιCompFunctorIso`, `transIso`, and the canonical stage
  triangulation. The generic pair descent interface in the other existing DAG node
  `lem-sbc-coherent-pair-functor-descent` was also read; no duplicate descent construction
  is required here.
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`:
  `Functor.IsTExact`; `eTruncLTIso` and `eTruncGEIso` were read as the canonical comparison
  infrastructure, but no preexisting t-exactness of F_E or F_Ω is assumed to use them.
- Proof imports: `Mathlib.LinearAlgebra.TensorProduct.Tower` (`LinearMap.baseChange`),
  `Mathlib.Algebra.Colimit.Module` (`AddCommGroup.DirectLimit`), the recorded
  `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology` (publicly importing
  `shortExact_iff_exists_distTriang`), and
  `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`
  (`TStructure.texact_truncation_comparison`). The ten-step proof docstring specifies
  where these are to be used in stage 3; there is no theorem proof in this delivery.

Edge cases checked before finalizing the statement: zero categories and zero functors;
identity functors and E = L; repeated fields in a tower; arbitrary positive and negative
cutoffs and negative cohomology degrees; torsion objects becoming zero under rationalization;
non-faithful transition functors; unequal object and morphism universes; an arbitrary chosen
algebraic closure; and every finite coefficient field including the base field. The coefficient
index is provably nonempty, so the theorem does not introduce an empty-index special case.
The raw category contains no idempotent completion. Boundedness and every specified canonical
map remain present. There is no claim that Bhatt--Scholze itself states this abstract lemma;
I read its Proposition 6.8.14 and Remark 6.8.15 locally using `pdftotext`.

Searches (all performed before writing the statement):

- `msearch.py ... leanfinder` query: "Compatible linear t exact functors descend through raw
  scalar localization and directed finite coefficient stages with canonical truncation
  comparison isomorphisms". Eight infrastructure hits, including
  `Localization.functor_linear_iff`, derived functor linearity, and
  `Functor.mapExactFunctor_smul`; none gives this combined descent statement.
- `msearch.py ... loogle` query:
  `CategoryTheory.Functor.IsTExact, CategoryTheory.StageSystem.Morphism.functor`.
  Zero hits; Loogle reports the upstream identifier IsTExact unknown in its Mathlib index.
  The actual upstream signature was therefore read directly, not inferred from this search.
- `msearch.py ... grep` query: `IsTExact|eTruncLTIso`, subdirectory
  `CategoryTheory/Triangulated`. Zero Mathlib hits. These notions are in the upstream
  extension, which was opened and read.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for StageSystem, pair/truncation,
  coefficient/scalar t-exactness, and the exact item id: found the generic stage-system
  implementation, scalar localization, and generic truncation comparison module; no
  declaration of this combined statement. Direct reads of the StageSystem and localization
  modules identified the precise representative and normalization interfaces used above.
- The DAG dependencies and `lem-sbc-coherent-pair-functor-descent` were read to check for
  duplication. Its statement supplies coherent descent of functors, not the localized
  t-exactness, canonical-map uniqueness, heart exactness, and all comparison coherences here.

Validation: repeated prescribed `scompile.py` checks of the one module, each file separately,
under the default 60-second limit. The complete statement and helper definitions compiled
without warnings or errors (the final signature-inspection check took 34.8 s sandbox and
24.8 s library). The temporary inspection command has been removed. The delivery dry run
will validate and compile the final artifact again.

## Second reading by Q103

This is a second pass by the same worker. The dispatch brief forbids starting another agent
and specifies independent review by the maintainer; no independent worker review is claimed.
I reopened the node and the final module and checked the twelve input clauses and seven
output clauses above. The first pass exposed Lean binder syntax and line-width issues, which
were repaired. The second pass retained the finite-stage canonical-map hypotheses explicitly,
and moved integral shift-linearity into explicit theorem binders so section-variable pruning
cannot discard it. The elaborated signature confirms the fixed algebraic closure and separate
category universes. I rechecked the orientation of the beta, inclusion, tower, and q formulas
against proof Steps 8--10. Both signs, uniqueness, the heart restriction, and negative shifts
are present. No statement correction or dependency repair is necessary.
