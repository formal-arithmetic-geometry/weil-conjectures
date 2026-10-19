## Worker report

This repairs the returned stage-1-only delivery df8af233c43d. The sandbox had no
retained Lean module or node record. I rebuilt the stage-2 delivery from the current
read-only shared node. Only its `lean` field changes; in particular its statement,
stmt_deps, proof, proof_deps and split_report are unchanged. There is one module,
`Sheaf.Paper.SfImmersionCompletedPullbackComparison`. All declarations are recorded
under this item's `lean.declarations`; they jointly state the item and normalize its
canonical constructions. All theorem proofs are `sorry`; definitions have actual
terms. No new independent notion, dependency replacement or statement correction
is required.

The source is the current main-20261015 smooth-purity localization blueprint,
`sec-smooth-purity/sk-prop-sf-localization/prop-sf-localization-all-stages.md`, Step 6,
and the item's full six-step proof. I also read the local Stacks proetale.tex:
09AA (`lemma-closed-immersion`), 099M (`lemma-naive-completion`), and 099N
(`lemma-pushforward-Noetherian-case`, especially (2),(5)). The module's main
docstring follows Steps 1--6 with their named proof dependencies. Every helper has
its own source/blueprint docstring, and every postponed theorem has a proof plan.

Hypotheses and clauses, in node order:

- A prime ell is `(l : ℕ) [Fact l.Prime]`. A finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. Its integer ring,
  uniformizer and positive quotients are the published `pbcIntegralDatum l E`
  and `Padic.coefficientExtensionRing l E (n + 1)`. No arbitrary adic datum is
  substituted. Natural index n always denotes the paper's positive index n+1.
- Schemes and the locally closed immersion are `{X Y : Scheme.{u}} (f : Y ⟶ X)
  `[IsImmersion f]`. Mathlib's immersion has its canonical closed immersion into
  `f.coborderRange`, followed by the open `f.coborderRange.ι`. Thus it expresses
  exactly the factorization the item specifies. No finite-field, characteristic,
  quasi-compactness, separation or Noetherian hypothesis is imposed on the schemes.
- The completed coefficients are the recorded actual `pbcAdicCompletion`.
  `quotientEquiv` is fixed on all quotient representatives, `finiteRingIso`
  transports its constant sheaves, and `completedRingIso` is fixed by *every*
  finite projection. These are unique-characterization constructions, not choices
  from mere existence. `transport` is derived scalar restriction along the inverse
  completed-ring isomorphism, into the recorded integral module category. Since
  the coefficient map is an isomorphism, this quantification covers every object
  of the paper's completed coefficient category, up to its canonical scalar
  transport; it is not a smaller coefficient category.
- The canonical inverse-image coefficient maps are
  `(pbcIntegralDatum l E).integralRingIso f` and `.finiteRingIso f n`, with
  `.projection_comm f n`. `moduleIso` identifies the actual ordinary module tensor
  pullback with this coefficient-normalized ordinary inverse image.
- Ordinary Lu* is exactly `pbcActualDerivedPull f (pbcIntegralDatum l E)`.
  `derivedIso_exists` identifies it with exact termwise inverse image `.pull f`.
  Its normalization is an equality of the original universal derived counits
  after localization of `moduleIso`; no arbitrary derived isomorphism is used.
  The main theorem asserts `PreservesFiniteLimits` and `PreservesFiniteColimits`
  of the actual module functor, together with countable product preservation.
- Completed Lu* and its specified comparison are *the recorded*
  `pbcActualStrictCompletedPull` and `pbcActualStrictCompletedPullUnit`, not a
  replacement completion object. `strictIso_exists` identifies its whole functor
  with the recorded exact tower presentation by the explicit equality of the
  original units. This normalization and the completion reflector determine it
  uniquely.
- For *every* K with `IntegralOnSlice.IsComplete l E X none ((transport ...).obj K)`,
  the main theorem asserts invertibility of the actual strict completed-pullback
  comparison and the same recorded completeness predicate on its ordinary
  pullback. It also identifies completeness with invertibility of the source's
  actual quotient completion unit through `.TowerComplete X K`; no intrinsic
  completeness hypothesis is substituted for the given predicate.
- `finiteComparison n` is an isomorphism of functors landing in the actual finite
  quotient module derived category. It is the recorded tensor comparison `.chi`
  transported along `derivedIso`. Thus it is linear over `(A_n)_Y`, not merely
  an isomorphism after forgetting coefficients.
- `reductionUnit`, `reductionTransition`, and `restrictedComparison` retain the
  canonical scalar units and *all* quotient maps. `finite_compatibility` states
  their unit squares, every b-to-a transition square, and the composite c-to-b-to-a
  identity, including equal and successive indices. `restrictedComparison` is
  constructed from `.chi` and the recorded restriction/pullback comparison,
  not from an independently chosen map.
- `completedProjection` is the actual `completedRlimProjection` followed by the
  identity-on-evaluations tower comparison and the recorded
  `completedReductionEvaluation`. `completedProjection_compatibility` explicitly
  states that ordinaryToCompleted followed by each finite projection equals
  pullback of the tensor unit, and that every quotient transition commutes with
  these finite projections. `actualCompletedProjection` composes these canonical
  transports into the actual strict functor, and
  `actualCompletedProjection_compatibility` states its unit and transition
  equations directly on the original actual strict comparison. These equations,
  `strictIso_exists` and
  `finite_compatibility` give the finite projection squares for the actual
  strict completed comparison, including successive quotients.
- `rlimComparison` is actual data: the right mate under the two recorded
  constant-tower/Rlim adjunctions of `.derivedConstantPullbackIso`. Its relation
  to the completion unit is the equality `ordinaryToCompleted_eq`.
  `productComparison` is formed by the genuine product projections and termwise
  evaluation identifications. `roosIso_exists` prescribes both Roos coordinates
  using that product comparison. `roosMap`, `roosInclusion` and `termwiseLimitIso`
  are likewise fixed by every coordinate or projection. `roosRlim_exists`
  characterizes the natural Roos identification on *all* complex maps and on
  every K-injective complex by the universal right-derived unit. This forces
  uniqueness. Finally `rlimComparison_roos` states that the actual mate is the
  localized coordinatewise `roosIso`, conjugated by exactly that normalization,
  and that it is invertible. Thus the derived-limit comparison is concretely
  the strict Roos comparison, rather than an unspecified cone map.
- The integral clause is the main theorem's last conjunct, using the dependency's
  exact `sfIntegralConstructible`. For every r≤s witnessing the original common
  interval, every reduction of the ordinary pullback has support in precisely
  `Set.Icc r s`, as well as belonging to the same integral category. There is no
  changed interval or added global finite-field datum.

Dependency interfaces read and used (including their docstrings/signatures):

| Node / notion | Module and declaration |
| --- | --- |
| finite coefficient extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`; underlying `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionRing` |
| schemes | `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` |
| closed/open immersions | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`; `Mathlib.AlgebraicGeometry.OpenImmersion`, `IsOpenImmersion`; their combined `IsImmersion` in `Mathlib.AlgebraicGeometry.Morphisms.Immersion` |
| small pro-etale site | `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt` and `ProEt.topology` |
| completed integral coefficients | `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses` and its unrestricted completed ring/projections |
| coefficient inverse image | `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`, `Scheme.proEtale_profinite_coefficient_inverse_image`; specialization through `.integralRingIso` and `.finiteRingIso` |
| strict completed pullback | `Sheaf.Paper.PbcActualStrictPullback`, `Scheme.pbcActualStrictCompletedPull`, `pbcActualStrictCompletedPullUnit`; actual ordinary pullback/counit from its public imports |
| derived completeness | `Sheaf.Paper.DerivedCompleteOnSlices`, `WeilConjectures.IntegralOnSlice.IsComplete`, global branch `none` |
| derived category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `Q`, `Qh` |
| integral category | `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible` |

The proof-dependency modules with recorded declarations are explicitly imported,
including the strict Roos comparison, immersion limit preservation, constructible
origin, bounded constructible pullback, coefficient DVR/perfect quotients,
constant-completion equivalence, tensor reflector and ringed tensor comparisons.
The exact-functor Mathlib match is already supplied by the public exact-functor
imports. I did not replace a dependency interface.

Edge cases checked before and during the second reading:

- n=0 means exponent 1, never the zero quotient or an omitted initial quotient.
- a=b and a=b=c are included among quotient-transition and composite equations;
  b=a+1 and c=b+1 are included without changing the quotient system.
- The zero complex, empty schemes, identity immersion, open immersion and closed
  immersion are all allowed. No nonempty or positive-dimension hypotheses occur.
- Negative r,s and r=s are allowed. The bounds r≤s are the definition's own
  uniform interval witnesses; the zero object's reductions have empty support.
- Arbitrarily unbounded derived-complete K are allowed in the comparison clause;
  the boundedness/constructibility hypotheses occur only in the integral clause.
- There is no global characteristic p in the statement and hence no extraneous
  inequality l≠p. The coefficient field and schemes use u with the recorded
  pro-etale site's object universe u+1 and morphism universe u; neither site
  universe is forced equal to the other.
- Every variable and universe is explicit (`autoImplicit false`). A failed first
  attempt at a K-flat objectwise counit normalization exposed a universe issue;
  the final full homotopy-category counit equation avoids any added size axiom.
- An initially expensive product definition was replaced by a named equality
  of termwise evaluations and its explicit equality transport before forming
  the product lift. This retains the canonical projections and compiles within
  the unchanged wrapper limit.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "locally closed immersion pullback derived complete
  pro etale strict quotient tower comparison"`: eight hits concerning ordinary
  scheme/open-immersion pullback limits; none states this comparison.
- `msearch.py ... loogle "CategoryTheory.Limits.PreservesLimitsOfSize,
  CategoryTheory.Functor"`: twelve general functor/limit declarations; no exact match.
- `msearch.py ... grep "immersion.*complet|completed.*pullback" AlgebraicGeometry`:
  no Mathlib hit.
- `msearch.py ... leansearch "derived complete pullback immersion commutes with
  inverse limit Roos"`: eight ordinary open-immersion/pullback-limit hits; no exact match.
- `rg` of the item id in upstream `WeilConjectures` found no declaration. Searches
  for immersion/completion and completed pullback in upstream and `lean/Sheaf`
  found the recorded coefficient, pullback and Roos ingredients, but no theorem
  giving this item. The existing upstream ClosedImmersionStages material concerns
  a different completeness/full-faithfulness assertion.
- The DAG dependency records and upstream names were checked before introducing
  the namespace `AlgebraicGeometry.Scheme.ImmersionCompletedPullback`; no existing
  copy of these canonical comparison helpers was found.

No STATEMENT-DISPUTED flag or statement correction is needed.

## Second reading by Q53

The dispatcher explicitly prohibits starting other agents and supplies no lead.
This is therefore a fresh second pass by the same worker, not a claimed reading
by another person. I reread the node and the completed file together, independently
of the initial stage-1-only packet.

The returned packet's numbered faults are repaired: there is now a Lean module and
verbatim lean record (H1,H3,H8--H11); the proper Worker report heading and this
second-reading section are present (H1); and the copied node retains every non-lean
field, including split_report (H2). All signature clauses are accounted for above.

During this pass I found and repaired omissions of explicit finite-transition,
completion-unit and finite-projection equations. I also replaced an isolated Roos
isomorphism with an equation identifying the *actual* adjunction mate with the
localized, coordinate-normalized Roos map. I retained the exact integral category
and the same r,s in the output bounds. The coefficient choices are all uniquely
normalized, and the actual strict comparison is not replaced by an arbitrary
isomorphism. All postponed proofs remain named theorems in this item's declaration
record. No unrelated split metadata is changed.

Validation: scompile.py completed with exit 0 and no errors or warnings for
both the sandbox and library paths of the final module, using the unchanged
wrapper limits. The prescribed deliver2.py dry run is also required; the delivery packet contains only the module, this report and the lean-only
node record. No global build or direct git command is used.
