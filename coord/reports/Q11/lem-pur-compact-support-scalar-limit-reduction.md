## Worker report

This repairs returned head `143907082a8a`. The saved packet's initial prescribed
`deliver2.py --no-push` passed mechanically (dry-run commit `12b70762c97`), but its
private arbitrary-category record did not state this node. I retained the node's
mathematical statement and replaced that Lean interface. The current shared node
has no Lean binding; the delivery wrapper performs the comparison and rebase against
current main. No direct Git command or edit was made in the shared repository.

The delivery has one module,
`lean/Sheaf/Paper/CompactSupportScalarLimitReduction.lean`, with primary theorem
`WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`. Its canonical
helpers and the explicit augmentation theorem belong to this same node and are all
listed in `lean.declarations`. There is no new independent definition node,
dependency repair, statement correction, arbitrary coherence proposition, or
`STATEMENT-DISPUTED` claim.

The theorem's data and hypotheses render the node as follows. The section binders
are part of the elaborated theorem; `include` retains every geometry hypothesis.

| Node data / hypothesis | Lean rendering |
| --- | --- |
| Finite-field datum, its algebraic closure k and characteristic p | `D : FiniteFieldDatum.{u}`, with base `Spec (.of D.k)` |
| Prime ell, different from p | `(l : ℕ) [Fact l.Prime]`, `(hl : l ≠ D.p)` |
| Finite extensions E and F of Q_ell, with inclusion | `E F : Type u`, their `Field`, `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]` instances, and `i : E →ₐ[ℚ_[l]] F`; a field algebra hom is injective |
| Valuation rings and their specified uniformizer quotients | Existing `Padic.coefficientExtensionIntegers`, `PurCompactSupport.finite`, `PurCompactSupport.projection` and `integralCoefficientCommRingSheaf` |
| e positive, tB = v^eB | `(e : ℕ)`, `he : PurCompactSupport.Ramification l E F i e`, `hepos : 1 ≤ e`; Ramification is the actual equality of generated ideals |
| X and Y separated finite type over k | `X.Over`, `Y.Over`, and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on their structure maps |
| f separated finite type and over k | `f : X ⟶ Y`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` |
| Fixed compactification j then p_c | `c : Compactification f`, with its recorded open `c.i` and proper `c.g` |
| Small pro-etale sites, completed R_W and S_W | Existing `W.ProEt`, `ProEt.topology W`, `scalarReductionSource l E W` and its F analogue |
| C_W, actual derived completed scalar extension | `pbcDerivedExtend (completedCoefficientMap l E F i W)` |
| M in derived-complete bounded constructible uniform finite-Tor category | `M : finiteTorConstructibleIntegralCategory l E X`; `M.property` contains completeness, constructible reductions, uniform cohomological bounds and one uniform Tor interval |
| Finite reductions M_n and C^(n) | Actual `pbcDerivedExtend` along `projection` and the ramification-normalized `finiteChange` |
| Chosen coherent strict reduction lifts | `S`, `S' : CoefficientDerivedSystemCalculus`; their recorded `reduction` and native separately derived proper/open functors are used, as in the strict-mate declaration |

The conclusions and constructions match each remaining clause as follows.

1. **The specified objects, not unrelated towers.** `scalarSupportNative` is exactly
   `S.reduction` followed by the existing varying-ring derived open extension and
   proper direct image. `scalarSupportCompletedTower` restricts that same system
   to the completed coefficient ring. Existing `support l E c S` restricts it to
   the discrete constant valuation ring. `scalarSupport` is its
   `coefficientSequenceLimit`, the recorded total right-derived inverse limit;
   `scalarLimit` is Mathlib's actual right-derived constant-tower limit.
   `scalarSupportLimit` is assembled from canonical derived-composite comparisons,
   ordinary preservation of limits, and exact restriction composition. It does
   not identify an independently selected proper/open completed value with the limit.
2. **Full normalization, with the correct transitions.** The theorem supplies
   `RE` and `RF : CoefCompactSupportRealization` satisfying their existing
   `CoefCompactSupportRealizationSpec`, with equality of their `normalized.tower`
   to the specified native completed tower objects. Their `NormalizedDVRTower`
   fields give identity, all quotient cocycles, and invertibility of transition
   adjuncts. In RF every index is a power of v: it is the full F tower, before
   arithmetic subsequence restriction. No identification of coherent towers is
   inferred merely from evaluation isomorphisms.
3. **Effectivity and the actual projection adjuncts.** `scalarSupportProjection`
   is `coefficientSequenceProjection` followed by its canonical finite evaluation
   presentation. `scalarSupportCounit` is its adjunct under the actual
   `pbcDerivedScalarAdjunction`. Positive-exponent versions retain the exponent
   e(n+1), including the predecessor transport. `scalarSupportNativeCounit` is
   the same adjunction before the finite proper/open presentation. The theorem
   asserts invertibility of these finite comparisons at every E and F level,
   completeness `IsSfDerivedComplete` of both total limits, and two explicit
   equations for the native epsilon maps and `coefficientSequenceDerivedTransition`
   for every m >= n, including identity reductions.
4. **The recorded strict scalar map.** `scalarLimitArrow` applies the actual limit
   functor to `(arrow l E F i c S S' e he hepos).app M`. This is the strict-mate
   dependency's canonical map. It is not an arbitrary map q. Its evaluations use
   the same dependency's `finiteTensorMap`, `supportEvaluation`,
   `positiveSupportEvaluation` and `finiteBalancing`.
5. **The actual tau and r_e.** `scalarLimitTensor` is a real composite of canonical
   unit-normalized derived-composite comparisons and `preservesLimitNatIso` for
   finite-free ordinary tensor. `scalarLimitRestrictionOrdinary` is `limit.pre`
   along the recorded arithmetic index e(n+1)-1. Its `rightDerivedPullback` is
   `scalarLimitRestriction`; `scalarLimitCofinalInverse` takes the inverse of
   this particular map, using its cofinality theorem. `scalarRoosRestriction`
   uses the actual witness of `compactSupportRoosCofinality`, whose selection/block
   coordinates determine the chain map. `scalarRoosNormalization` records those
   coordinates, the quasi-isomorphism and its equality with derived restriction.
   `scalarRoosTensor` uses `strictRoosAdditiveComparison` and the actual product
   comparison. `scalarRoosTensorNormalization` equates its localization with tau.
6. **Roos model and augmentations.** `roosF`, `roosι`, `strictRoosCoordinates` and
   `roosAugment` are existing definitions of the cone of 1-shift, shifted by -1,
   and its coordinates. `scalarRoosComparison` is uniquely normalized by the
   ordinary kernel inclusion and the universal derived unit on every complex;
   this determines the whole-system comparison, not just finite projections.
   `scalarRoosNormalization` and `scalarRoosTensorNormalization` spell out their
   augmentation equations. `scalarLimitMapAugmentation` handles the middle map.
   The explicit theorem `scalarLimitArrow_augmentation` applies them to the actual
   compact-support arrow and every strict source representative, cone and
   augmentation, with the zero shifted-product component. It states the resulting
   equation for the actual three-factor composite, rather than a free predicate.
7. **Completed comparison, naturality and S_Y action.** The main theorem supplies
   a single natural transformation `γ` between functors on the actual full
   finite-Tor category, with `IsIso γ`. Its components are morphisms in the
   derived category of modules over the completed F coefficient sheaf; thus the
   S_Y action is part of their type. The displayed equation with
   `scalarSupportLimit` and `scalarCompletion` identifies its constant restriction
   with `scalarLimitArrow`, whose definition is tau, R(q), then r_e inverse.
   `scalarCompletionOrdinary` is uniquely fixed by every local pure tensor;
   `scalarCompletion` is uniquely fixed on all complex counits. Neither is chosen
   from a bare `Nonempty` isomorphism. This is the completed/constant transport
   appearing in the node, with its specified ordinary/strict scalar comparison.
8. **Projection reduction.** The first explicit equation for every n starts with
   `scalarLimitArrow` and the actual retained `scalarLimitProjection` at
   e(n+1)-1. After the recorded target presentation it equals `baseTensor.map`
   of the E projection, followed by `finiteBalancing`, then restriction of
   `finiteTensorMap`. This is precisely pF_en gamma = Res(q_n) iota_n T(pE_n).
9. **Adjoint finite reduction.** A second equation states the same projection
   identity in completed coefficients with the actual
   `scalarSupportPositiveProjection`. The following equation states its adjunct:
   reduction of `γ.app M`, then epsilonF and the target input associator, equals
   `scalarReductionBalancing` at Y, then C^(n)(epsilonE), then `finiteTensorMap`.
   `scalarReductionBalancing` is a real `PurCompactSupport.tensorSquare` built
   from `ramified_reduction_square`; it is exactly d_n. The target input
   associator identifies reduction of C_X M with C_X^(n)(M_n). The arrows and
   their order are explicit; there is no `projection_coherence : Prop` field.
10. **All quotient/mate squares.** The two native epsilon cocycle equations retain
    the actual projection adjuncts. The finite ramified m-to-n clause uses the
    dependency's `ComparisonSquareEquation`, actual `finiteQuotientChange` maps
    and `ramified_quotient_square`. The last clause writes both pasted paths of
    an arbitrary commuting coefficient square out in full, including the common
    `tensorSquare` associator at X and Y. This includes the quotient squares and
    their identity cases; there is no `quotient_coherence : Prop` field.

Dependency declarations actually used include:

- `Sheaf.Paper.CompactSupportStrictScalarMate`:
  `PurStrictScalar.arrow`, `baseTensor`, `baseTensorCounit`, `finiteBalancing`,
  `supportEvaluation`, `positiveSupportEvaluation`, and the theorem
  `compactSupportStrictScalarMate` in the proof plan.
- `Sheaf.Paper.NativeConstantSupportModel` and its public prerequisites:
  `support`, `constantRestriction`, `systemU`, `toConstant`,
  `towerConstantRestriction`, and `CoefficientDerivedSystemCalculus`.
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`:
  `PurCompactSupport.Ramification`, `finiteChange`, `finiteTensorMap`,
  `finiteReductionIso`, `finiteImageIso`, `tensorSquare`,
  `ramified_reduction_square`, `finiteQuotientChange`,
  `ramified_quotient_square`, and `ComparisonSquareEquation`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `coefficientSequenceDerivedRestriction`, `coefficientSequenceLimit`,
  `coefficientSequenceProjection`, `coefficientFiniteAdjunction`,
  `coefficientSequenceDerivedTransition`, `coefficientConstantTowersKInjectives`.
- `Sheaf.Paper.CompactSupportNativeSystemEvaluation`:
  `compactSupportSystemEvaluation`.
- `Sheaf.Paper.CompactSupportNormalizedRealization`:
  `CoefCompactSupportRealization`, `CoefCompactSupportRealizationSpec`;
  `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`, `normalizedDVRRes`;
  `Sheaf.Paper.NormalizedDVREffectivity`: `normalizedDVRReductionTransition`
  and the effectivity theorem in the proof plan.
- `Sheaf.CategoryTheory.CompactSupportRoosCofinality`:
  `compactSupportRoosCofinality`; `StrictRoosModel`: `roosF`, `roosι`,
  `roosAugment`; `StrictRoosAdditiveComparison`:
  `strictRoosAdditiveComparison`; `StrictTowerArithmeticRestriction`:
  `index`, `block`, `selection`, `complexRestriction`;
  `StrictRoosComparison`: `strictRoosComparison` in the proof plan.
- `Sheaf.Paper.FiniteTorAmplitudeSites` publicly carries
  `finiteTorConstructibleIntegral`, `finiteTorConstructibleIntegralCategory`;
  `SfIntegralConstructible` carries the integral completeness and constructibility
  predicate; `PurityFiniteSetting` supplies the recorded finite-field convention.
  These are used through the existing public dependency imports, not redefined.
- Mathlib's standard `DerivedCategory`, functor categories, `lim`, `limit.pre`,
  scalar restriction and limit-preservation comparisons, together with the
  published unit-normalized derived-composite APIs.

Edge checks: Lean n=0 means exponent 1, so no quotient at exponent zero is
substituted. For e=1 and identity field inclusion the same constructions apply;
no e>1 or nonidentity hypothesis is imposed. All m=n quotient cases remain in the
cocycle and square statements. The F normalization covers indices not divisible
by e. Zero objects, arbitrary shifts and the empty scheme are admitted: there is
no nonzero, nonempty, bounded-below representative or product-epimorphism assumption.
Uniform Tor bounds are those in the existing integral domain, not separate
level-dependent intervals. Site object universe u+1 and morphism universe u remain
distinct, with module coefficients at u+1.

Searches (the sandbox's `searches.jsonl` retains the launcher outputs):

- `msearch.py ... leanfinder`, query “Derived inverse limit of normalized compact
  support towers commutes with finite free scalar extension and reduces to the
  canonical finite scalar mate”: eight unrelated condensed, supported-function
  and adic-completion hits; no exact theorem.
- `msearch.py ... leanfinder`, query “The canonical derived inverse limit map of
  compact support scalar extension is normalized by its finite coefficient
  projection adjoints”: eight unrelated condensed and supported-function hits.
- `msearch.py ... loogle`, query
  `CategoryTheory.Limits.lim, CategoryTheory.Functor.mapDerivedCategory`: no hits.
  The repair query with `rightDerivedFunctor` also had no hits and reported that
  Loogle does not index that identifier; this was not treated as absence of the API.
  Its actual published source was read and used.
- `msearch.py ... grep`, query
  `scalar.*[Ll]imit|[Ll]imit.*scalar|normalizedDVRTower`: 25 generic Mathlib hits;
  no exact statement. Query
  `compactSupportScalarLimitReduction|scalarSupportCounit|scalarRoosTensor`: no hits.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf`, and the prescribed
  `grep -rn` on `lean/WeilConjectures`, for this item id and these declaration
  names: no existing statement. Focused reads instead found the reusable strict
  mate, exact tensor, finite balancing, native system evaluation and Roos maps,
  all reused above. No private copy of any of those notions remains.

The seven-step proof in the node is written out in the main theorem's docstring.
Every postponed helper has its own source/proof docstring and this node's blueprint
tag. Definitions contain actual constructions; selections are only from unique
characterizations or coordinate-determined maps. All theorem proofs remain `sorry`.

Final compile validation: the prescribed `scompile.py` passed the final module in
both sandbox and library modes (51.8 s and 42.9 s), with no error or non-sorry
warning. The local packet self-check confirms that only `lean` differs from the
current node, the recorded signature matches verbatim, all 12 theorem proofs are
`sorry`, every source line is at most 100 characters, and the old arbitrary record
and free coherence fields are absent.

## Second reading by Q11

This is a fresh self-reading against the node and the final Lean file, not a claim
that another worker reviewed the packet. The dispatcher prohibits starting agents;
the maintainer's delivery review remains independent.

I found the original arbitrary categories, arbitrary q and isomorphisms, and two
free Prop fields did not express any of the named geometric or coefficient objects.
They are removed. I checked the finite-field datum, prime condition, both structure
maps and their separated/finite-type hypotheses, f over k, compactification,
field inclusion, ideal ramification and positive exponent against the actual
section binders and theorem. M is now in the existing uniform finite-Tor integral
full subcategory; arbitrary abelian categories and arbitrary towers are absent.

I checked that U_E and U_F are formed from the recorded native reduction and
separately derived open/proper operations, not merely objects with the right
finite evaluations. The normalization conclusion has equality to those coherent
completed tower objects and uses `NormalizedDVRTower` through the recorded
realization structures. Its F statement uses every v power. The actual inverse
limits are the `coefficientSequenceLimit` of those native systems. During repair
I rejected an intermediate identification with completed proper/open image and
replaced it with the actual native total limit and canonical limit/restriction
comparison; that intermediate version is not delivered.

I expanded the finite-reduction and quotient clauses instead of retaining a
coherence predicate. I checked the source, target and order of every arrow in
both projection equations and the epsilon equation: the Y tensor associator is
on the source route, the X tensor associator is applied inside finite F support
on the target route, and the middle finite arrow is the recorded
`finiteTensorMap`. The epsilon definitions are adjoints of the actual
`coefficientSequenceProjection`; they are not a renamed coefficient-comparison
map. Both E and F quotient cocycles are now equations for these native adjuncts.
The ramified finite quotient squares and the general pasted square retain their
common tensor associators.

I checked the canonical-composite clause by opening `scalarLimitArrow`: it is tau,
then the actual total-limit image of the strict-mate arrow, then the inverse of
the actual arithmetic restriction. The Roos helper equations fix its block and
selection coordinates, tensor/product coordinates and augmentation normalization.
`scalarLimitArrow_augmentation` now states the augmentation equation for this
very compact-support map. The main gamma is one natural transformation on the
whole finite-Tor domain and has completed F-module morphisms as components;
naturality and the S_Y action therefore cannot be omitted by changing a free field.

I also checked e=1, identity field inclusion, m=n, exponent-one indexing, zero
complexes and the empty scheme, and re-read the seven proof steps in the docstring.
The JSON signature is extracted verbatim from the final theorem, and all helper
declarations are registered. Validation uses only `scompile.py` and the prescribed
delivery wrapper; no global build or local forbidden preflight was run.

## Original auxiliary argument

The following seven steps and their source references are retained verbatim from
the current DAG node, so the original argument remains available alongside the
Lean proof docstring.

1. First check the full towers, before restricting indices. By [lem-pur-compact-support-coefficient-models], $C_XM$ is derived complete and bounded constructible with the same uniform Tor bounds as $M$; its finite reductions are the stated balanced tensors. Apply [lem-coef-compact-support-normalized-realization] with coefficient field $E$ to $M$, and separately with coefficient field $F$ to $C_XM$. Its description of the transition adjoint is the compact-support tensor comparison followed by the input iterated-reduction isomorphism; both arrows are isomorphisms, and its transitions have identity units and the quotient cocycle. The evaluated transitions of our specified lifts are exactly these maps by [lem-weil-compact-support-reduction-tower-functor]. Those lifts already supply the coherent strict-tower datum in [def-coef-normalized-dvr-tower]. Thus the evaluated adjoints and cocycles just checked prove normalization for these lifts themselves; no identification of two objects of a derived tower category is inferred merely from their evaluations. The second application uses every quotient $B/v^a$, $a\geq1$, so it proves full $v$-normalization, including indices not divisible by $e$.

Source: {"document": "literature/stacks-project/more-etale.tex", "place": "Tag 0GL6 (remark-Rf-lower-shriek-change-of-rings); application of the existing normalized-realization statement to the two coefficient fields"}

Uses: lem-pur-compact-support-coefficient-models, lem-coef-compact-support-normalized-realization, lem-weil-compact-support-reduction-tower-functor, def-coef-normalized-dvr-tower

2. Put $L_H=R\lim U_H$ with completed coefficients. Apply [lem-coef-normalized-dvr-effectivity] to the two full normalized towers from Step 1. It gives derived completeness of $L_E,L_F$ and coherent isomorphisms $\epsilon^E_n:L_E\otimes^L_{R_Y}(A_n)_Y\to U_{E,n}$ and $\epsilon^F_a:L_F\otimes^L_{S_Y}(B/v^a)_Y\to U_{F,a}$. Here the finite levels on the right retain their finite scalars. These are the canonical counit comparisons: by [lem-weil-derived-scalar-extension-restriction-adjunction] they are adjoint to the actual limit projections $p^E_n,p^F_a$ after restriction of scalars. Their coherence is the quotient cocycle, not a choice of unrelated finite-level isomorphisms.

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 0941 (lemma-derived-limit-is-ok); normalized-DVR effectivity and the specified reduction adjunction"}

Uses: lem-coef-normalized-dvr-effectivity, lem-weil-derived-scalar-extension-restriction-adjunction

3. Use [det-pe-products-exact] for each constant integral ring sheaf on $Y_{\mathrm{proet}}$. Hence [lem-weil-strict-roos-comparison] identifies the stated termwise product-cone construction with total derived inverse limit, functorially on the ordinary derived category of strict towers, preserving each projection and every strict augmentation with zero shifted-product component. For $U_E$ and $U_F$, [lem-pur-compact-support-coefficient-models] supplies the canonical constant/completed identifications of these same limits and their quotient diagrams. It identifies $C_Y$ on the complete object $L_E$ with finite-free constant scalar extension $T$, with the specified quotient-normalized $\chi$. Consequently there is no replacement of the specified limits or scalar maps by abstractly isomorphic values in the remaining construction.

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 0941 (lemma-derived-limit-is-ok); functorial Roos realization and quotient-normalized coefficient models"}

Uses: det-pe-products-exact, lem-weil-strict-roos-comparison, lem-pur-compact-support-coefficient-models

4. The compatible $A$-basis of $B$ in [lem-pur-compact-support-coefficient-models] makes $B$ finite free. Apply [lem-pur-compact-support-roos-cofinality] to $U_E$ for tensor/product interchange, and to the full $B$-tower $U_F$ for its arithmetic restriction. This gives the specified maps $\tau:T\mathsf R(U_E)\xrightarrow{\sim}\mathsf R(TU_E)$ and $r_e:\mathsf R(U_F)\xrightarrow{\sim}\mathsf R(U_F^{(e)})$. By [lem-pur-compact-support-strict-scalar-mate], $q_\bullet^c$ is an invertible natural $B$-linear map of derived strict towers. Apply the total-limit functor of [lem-weil-pbc-ringed-strict-tower-homotopy-limit], realized as in Step 3, to this actual map, and define $\gamma=r_e^{-1}\mathsf R(q_\bullet^c)\tau$. Every factor is invertible and natural. Tensor/product interchange and $r_e$ preserve the specified augmentations; the middle factor sends an augmentation to its composite with $q_\bullet^c$. This proves the corresponding augmentation equation for $\gamma$, including the zero shifted coordinate in $\chi$. All factors are $B$-linear. Under the coefficient equivalence of Step 3 they are morphisms of the complete $S_Y$-objects, so $\gamma$ preserves the $S_Y$-action.

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 0941 (lemma-derived-limit-is-ok); canonical finite-free tensor/product and arithmetic-subsequence maps"}

Uses: lem-pur-compact-support-coefficient-models, lem-pur-compact-support-roos-cofinality, lem-pur-compact-support-strict-scalar-mate, lem-weil-pbc-ringed-strict-tower-homotopy-limit

5. Compute the projection of this particular composite. In the constant model, let $\iota_n:T U_{E,n}\xrightarrow{\sim}\operatorname{Res}_{B_n}^{B} C_Y^{(n)}U_{E,n}$ be the canonical balanced identification. It is given by $x\otimes b\mapsto x\otimes(b\bmod t^nB)$; its inverse uses the fact that the finite-level scalar structure factors through $A_n$. These are the finite quotient identifications of [lem-pur-compact-support-coefficient-models]. The product part of $\tau$ sends $(x_i)_i\otimes b$ to $(x_i\otimes b)_i$. The first component $a_e$ of the block map $r_e$ sends $(z_a)_a$ to $(z_{en})_n$. Therefore $p^{F,(e)}_n r_e=p^F_{en}$, while the other component of $r_e$ has no contribution to these cone projections. Functoriality and the projection normalization of [lem-weil-strict-roos-comparison], and the exact evaluated-map assertion in [lem-pur-compact-support-strict-scalar-mate], give
$$p^F_{en}\gamma=\operatorname{Res}_{B_n}^{B}(q_{n,M})\,\iota_n\,T(p^E_n).$$
This is an equation of morphisms with source $T L_E$ and target $\operatorname{Res}_{B_n}^{B}U_{F,en}$, obtained from the strict-tower map itself. The block and tensor maps used here are precisely [lem-pur-compact-support-roos-cofinality].

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 0941 (lemma-derived-limit-is-ok); explicit first product coordinate of the Roos maps"}

Uses: lem-pur-compact-support-coefficient-models, lem-weil-strict-roos-comparison, lem-pur-compact-support-strict-scalar-mate, lem-pur-compact-support-roos-cofinality

6. Transpose the projection identity of Step 5 using [lem-weil-derived-scalar-extension-restriction-adjunction] for $F$ at level $en$. Write $d_n:(C_YL_E)\otimes^L_{S_Y}(B_n)_Y\xrightarrow{\sim}C_Y^{(n)}(L_E\otimes^L_{R_Y}(A_n)_Y)$ for the canonical tensor reassociation from the coefficient models. The transpose of $p^F_{en}\gamma$ is $\epsilon^F_{en}(\gamma\otimes^L B_n)$ by naturality of the adjunction. The transpose of the other side is $q_{n,M} C_Y^{(n)}(\epsilon^E_n)d_n$: the unit sends $x$ to $x\otimes1$, and the balancing identification sends $(x\otimes b)\otimes\bar c$ to $x\otimes\overline{bc}$. Thus
$$\epsilon^F_{en}(\gamma\otimes^L B_n)=q_{n,M}\,C_Y^{(n)}(\epsilon^E_n)\,d_n.$$
The canonical tensor and unit identifications here are those of [lem-pur-compact-support-coefficient-models]. Since the two $\epsilon$ maps are the coherent isomorphisms of [lem-coef-normalized-dvr-effectivity], this proves exactly the asserted finite reduction of $\gamma$, with the specified projection adjoints.

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 07A6 (lemma-adjoint); transposition of the projection equation with the quotient-normalized tensor associator"}

Uses: lem-weil-derived-scalar-extension-restriction-adjunction, lem-pur-compact-support-coefficient-models, lem-coef-normalized-dvr-effectivity

7. Finally take any further quotient and apply it to the equation of Step 6. The $\epsilon$ maps obey the normalized quotient cocycle by [lem-coef-normalized-dvr-effectivity]. The quotient-transition squares of $q_\bullet^c$ commute before total limit by [lem-pur-compact-support-strict-scalar-mate]. The finite quotient and tensor identifications commute with coefficient maps by [lem-pur-compact-support-coefficient-models]. These three facts identify the two paths after further reduction, with the same reassociation $((x\otimes b)\otimes c)\mapsto x\otimes bc$. For a commuting coefficient quotient square, its two composites on quotient representatives have the same value; reassociation therefore supplies the same pullback/coefficient square on both paths. The proper factor of $q$ is the mate of that square and its open factor is tensor balancing, with composite-adjunction normalization, by the strict-scalar-mate statement. Apply clauses (1) and (2) of [lem-weil-pbc-mate-pasting] to these two paths: their mates are the pasted proper/open mates. Cancelling their common tensor associator gives the comparison equation for the square. This proves the claims for $A_m\to A_n$ and $B_m\to B_n$, including their identity cases, as equations of the specified comparison maps.

Source: {"document": "literature/stacks-project/more-etale.tex", "place": "Tag 0GL6 (remark-Rf-lower-shriek-change-of-rings); quotient cocycles and formal mate pasting with the common tensor associator"}

Uses: lem-coef-normalized-dvr-effectivity, lem-pur-compact-support-strict-scalar-mate, lem-pur-compact-support-coefficient-models, lem-weil-pbc-mate-pasting
