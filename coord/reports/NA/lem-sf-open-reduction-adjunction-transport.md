## Worker report

Item: `lem-sf-open-reduction-adjunction-transport`, group NA, stage 2, 2026-10-21.
The module is `Sheaf.Paper.SfOpenReductionAdjunctionTransport`, namespace
`WeilConjectures.OpenReductionAdjunctionTransport`. The main declaration is
`openReductionAdjunctionTransport`. Its sole proof is `sorry`. All other declarations
are explicit definitions or a structure packaging exactly the stated hypotheses.
No data is supplied by a new existence theorem, and no target or node statement is changed.
The node copy changes only `lean`.

The sources read are Stacks `sites-cohomology.tex`, Tag 0GL1,
`sites-modules.tex`, Tag 0E8I, the actual localized extension adjunction, and Tag 0941
in `sites-cohomology.tex`. The eight-step proof in the node is reproduced in the
main theorem's docstring. The system and realization identities are the agent
refinement in the node, not assertions attributed to a single Stacks tag.

The existing module `Sheaf.SixFunctors.IntegralOpenReductionComparison` already
contains the canonical coefficient identifications, open operations, and scalar-unit
representative normalizations needed here. They are imported and reused rather than
redefined. Its theorem `integralOpenReductionComparison` is NOT the present result:
it additionally assumes quasi-compactness, existentially supplies a comparison, and
restricts its comparison to complete objects. The present theorem has no
quasi-compactness hypothesis, starts with the specified ambient `r`, and supplies an
ambient `s`. Only that module's auxiliary definitions are used, never its existence
theorem. In particular this does not assume the parent result to prove its proof
prerequisite. For a later proof of the parent in its current source file, its shared
auxiliary definitions should first be factored into a common module: importing this
new result directly into the current parent source would make a source import cycle.
No dependency on the parent's theorem has been added to the DAG.

Hypothesis and object correspondence:

- Prime and finite coefficient extension: `(l : ℕ) [Fact l.Prime] (E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing l E (n+1)` fix R, t and every positive quotient. Choosing
  a generator of the same DVR maximal ideal does not change its powers. The actual
  quotient maps, not a family of unrelated rings, are used everywhere.
- Small pro-etale sites: `{U X : Scheme.{t}}` and `ProEt.topology` on `U.ProEt`
  and `X.ProEt`. The site object size is t+1, its morphism size is t, and coefficient
  size is `max u (t+1)`; no equality of t and u is imposed.
- Finite and completed coefficient sheaves: `integralCoefficientCommRingSheaf`
  and `completedIntegralCommRingSheafUnrestricted`. `Operations l E j` extends the
  existing `Coefficients`: its `finiteConstants` pins the finite transport on
  constants, `projections` pins the completed map on every finite projection,
  and `systemComponents` pins the system transport. Its equivalence functors are
  fixed to the concrete slice pushforwards. These are the coefficient identifications
  in the statement, not freely chosen unrelated functors.
- Open immersion and invertibility of l: `(j : U ⟶ X) [IsOpenImmersion j]` and
  `[∀ x : X, Invertible (l : X.residueField x)]`, with the identical condition on U.
  This is precisely invertibility of l on these schemes. No finiteness, support,
  constructibility, boundedness, or quasi-compactness condition is imposed.
- Strict semilinear categories and actual reduction adjunctions: `coefficientSequenceModules`,
  `coefficientSequenceDerived`, and the parameters `SU`, `SX` of type
  `CoefficientDerivedSystemCalculus`. Their `.reduction`, `.adjunction.unit`,
  `.adjunction.counit`, and `coefficientSequenceLimit` are the recorded R, u, e, L.
- Completeness is the existing `IntegralOpenReduction.complete`, definitionally
  `IntegralOnSlice.IsComplete ... none`, hence the quotient-tower Roos condition.
  It is not replaced by invertibility of a reconstruction map.
- Normalized systems use the existing `IsNormalizedCoefficientSequence`, quantified
  over every n ≤ m. Its bijective Hom-transpose condition is the universal
  characterization of the indicated transition-adjoint being an isomorphism.
- Exact open functors and actual adjunctions are the existing `extension`,
  `restriction`, `systemExtension`, `systemRestriction`, their derived functors
  `shriek`, `star`, `J`, `P`, and `openAdjunction`, `systemAdjunction`.
  These use the concrete localized ringed-site adjunction and its exact derived
  localization, including the actual equivalence adjunctions for coefficient transport.
- The seven reconstruction hypotheses are the seven fields of `Reconstruction`:
  `extension_complete`, `unit_U`, `unit_X`, `counit_U`, `counit_X`, `limit_U`,
  `limit_X`. Each has exactly the domain (complete objects or normalized systems)
  specified in the node. The two unit fields are about the actual u.
- The supplied natural isomorphism is
  `r : shriek ... ⋙ SX.reduction ≅ SU.reduction ⋙ J ...` on the full ambient
  derived category. `tensor : IntegralOpenReduction.TensorComparison` names the
  canonical ordinary open tensor maps: its `generators` fixes the image of every
  extension-summand scalar unit, and linearity fixes all coefficient multiples a.
  This is the node's canonical [x] tensor a formula, not an arbitrary isomorphism.
- `hr : ExtensionModel ... r` states the simultaneous flat-term K-flat representative
  requirement on ALL good complexes. It reuses `CoefficientReductionPresentation`
  and `AugmentedPresentation`; the former includes all m ≥ n quotient squares,
  and the latter requires one strict scalar-unit augmentation and its transpose
  for the actual reduction adjunction. The localized square identifies r itself
  with the one strict chain isomorphism f. Its finite components are the above
  `tensor.ordinary` maps. Thus a collection of evaluated isomorphisms is insufficient.
  The parent module's `StrictModel` could not simply be reused, since it only
  quantifies over complete representatives and complete-subcategory comparisons.

Conclusion correspondence, in theorem order:

1. `s : star ... ⋙ SU.reduction ≅ SX.reduction ⋙ P ...` is the requested ambient
   natural strict-system isomorphism. `hc` says ordinary restriction preserves the
   existing quotient completeness predicate for every complete H.
2. `RestrictionModel ... tensor s` supplies one strict chain comparison on each
   good representative, its localization square, both actual augmented quotient
   presentations, and every finite component. The finite component is
   `restrictionTensorComponent`, the explicit open-adjunction mate of the inverse
   canonical extension tensor map, using the actual finite unit and integral
   counit. Its section formula is x tensor a sent to the same restricted tensor.
   `restrictionEvaluationComponent` is constructed from the fixed coefficient
   equivalence units/counits and the recorded open-system evaluation map; it
   introduces no arbitrary evaluation isomorphism. This retains quotient
   transitions and scalar units before localization.
3. `CompletionModel` specifies the actual completion-unit square on each restricted
   good representative of a complete H, through `IntegralOnSlice.completionComparison`.
   Its second clause postcomposes with EVERY positive finite Roos projection
   `integralLineRoosProjection` and requires the actual quotient augmentation.
   The following `IsIso (completionUnit.app (star.obj H))` clause identifies ordinary
   restriction with its completion by this very map. This is independent of any
   arbitrary reconstruction isomorphism; the finite comparison to the restricted
   quotient models is fixed in `RestrictionModel`.
4. The next two conjuncts are verbatim the reduced-unit and reduced-counit equations:
   `SU.reduction.map eta_o ≫ s ≫ P.map r = eta_S`, and
   `SX.reduction.map epsilon_o = r ≫ J.map s ≫ epsilon_S`.
   They are morphism equalities in the derived categories of strict systems.
5. `di` and `bi` are natural isomorphisms on the full subcategories of complete
   objects with exactly the sources and targets of d and b. Their component
   equations are `di.hom.app K = d ... K` and `bi.hom.app H = b ... H ...`.
   The explicit definitions d,b apply L to the inverse r,s and then invert the
   ACTUAL reconstruction unit. Proofs of invertibility come from h and hc, not
   new object choices. Naturality and invertibility are asserted by the natural
   isomorphism types themselves.
6. The next conjunct is `SX.reduction.map (di.hom.app K) ≫ r.hom.app K.obj =
   SX.adjunction.counit.app (J.obj (SU.reduction.obj K.obj))`, precisely the
   normalization r after R(d) equals the actual counit e.
7. The penultimate conjunct is the realized-unit equation, in order
   `u_K ≫ L_U(eta_S) ≫ L_U(P(r inverse)) ≫ bi_(j!K) = eta_o`.
   Completeness of j!K is the given `h.extension_complete`.
8. The last conjunct is the realized-counit equation, in order
   `di_(j*H) inverse ≫ L_X(J(s_H)) ≫ L_X(epsilon_S) ≫ u_H inverse = epsilon_o`.
   Completeness of j*H is the conclusion hc. These, together with the natural
   isomorphisms, are the stated identification of the realized and actual adjunctions.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, publicly reexporting the recorded
  coefficient integers, uniformizer, ideals, rings and quotient maps.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `ProEt.topology`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientReductionPresentation`,
  `coefficientIntegralScalarUnitSection`, actual reduction adjunction and finite models.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete` and
  its imported actual completion, augmented tower and comparison constructions.
- `def-weil-scheme-morphism-properties` is a convention node, with no single
  declaration; its recorded `IsOpenImmersion` and `Scheme.residueField` are used.
- `Sheaf.SixFunctors.OpenTensorNormalization` and its public Data module:
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction` and the
  actual localized extension/restriction adjunction used by the reused operations.
- `Sheaf.Paper.SemilinearDerivedSections` and its public Calculus module:
  `SemilinearSections.OpenSystems`, `openRestriction`, its actual adjunction,
  evaluation and coefficient transport data.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, inside the existing good predicate.
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`:
  `AlgebraicGeometry.Scheme.ImmersionCompletedPullback.immersion_completed_pullback_comparison`
  and its actual finite/completion compatibilities are read and retained as a proof
  import. Its published pbc presentation has equal site/coefficient base universes;
  this statement uses the same canonical quotient-Roos formulas in the independent
  universes, rather than adding an equality of universe parameters.
- Proof import `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` provides
  the recorded independent-universe canonical pullback tensor comparison.
  The proof dependency `lem-sf-open-semilinear-tensor-model` has no recorded Lean
  module yet; its input conclusion is explicitly the supplied hr, so no unstated
  module is invented or imported. The other recorded proof dependencies are
  already publicly imported by the reused modules.
- Further existing helpers reused: `IntegralOpenReduction.Operations`,
  `TensorComparison`, `AugmentedPresentation`, `extensionEvaluation`, `complete`
  in `Sheaf.SixFunctors.IntegralOpenReductionComparison`, and
  `integralLineRoosProjection` in `Sheaf.Paper.IntegralLineTensorComparisonDefinitions`.

Edge cases checked by reading the types and defining formulas:

- The empty open and empty scheme remain allowed: direct sums over the empty
  extension-summand index, restriction to the empty slice, and zero categories
  are the existing constructions. No nonempty hypothesis is introduced.
- The identity open is allowed; its summand maps and adjunction-unit formulas give
  the usual identity comparison, with all actual equivalence transports retained.
- Zero complexes and unbounded complexes are allowed. No interval of degrees is
  fixed. Good means exactly K-flat with flat terms.
- n=0 means exponent one, never R/t^0; transition indices include n=m and all n ≤ m.
- An arbitrary prime l and arbitrary finite E/Q_l are allowed; both scheme
  invertibility hypotheses are explicit. Site and coefficient universes are
  independent, including cases in which either universe dominates the other.
- Replacing the actual units by unrelated reconstruction isomorphisms fails the
  specified augmented-presentation and d,b formulas. Likewise finite evaluations
  alone do not satisfy the required strict-chain localization squares.

Searches made (all negative for the exact theorem unless specified):

- `msearch.py leanfinder`: "Open extension restriction adjunction commutes with
  derived coefficient reduction and total limit with actual unit counit" returned
  generic derived adjunction results, no statement with these strict models or equations.
- `msearch.py loogle`: `"Adjunction", "conjugate"` returned eight general
  mate/conjugacy results, no canonical open-reduction transport theorem.
- `msearch.py grep`: `reduction.*adjunction|realiz.*adjunction`, in Mathlib's
  CategoryTheory directory, returned no match.
- `msearch.py leansearch`: "The canonical extension by zero tensor reduction map
  transports the actual adjunction unit counit through derived completion" returned
  eight generic results, none giving this theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item ID, reduction/adjunction and open/realization names found no exact
  declaration. A broader open-reduction search in `lean/Sheaf` found the parent
  module described above, whose full signature and docstrings were read. Its
  auxiliary constructions are reused; its extra quasi-compactness and existential
  complete-only r prevent an `existing: true` match for this item.
- Further source searches located the existing all-pairs normalization predicate,
  actual completion-unit normalization, and the independent-universe finite Roos
  projection. These were reused directly. No new independent notion/node is needed.

Validation: scompile.py compiled both its sandbox module and the final library module
with no errors or warnings (30.7 s and 33.2 s, under the unchanged 60 s limit).
All binders and universes are explicit, all lines are at most 100 characters, and
no `#check`, local notation, local instance, private duplicate, or new axiom remains.
The serialized `lean.statement` is the main signature verbatim. No statement dispute
or statement correction was needed. The required deliver2.py --no-push dry run passed the server preflight and per-file
compilation: commit a18234deb3e, nothing pushed. The module has exactly one sorry
(the main theorem), ten listed owned declarations, and the node differs only in lean.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
