## Worker report

Delivered module: `Sheaf.Paper.PodCompletionUnitScalarIntertwining`; namespace
`WeilConjectures.PodCompletionScalar`. The sole postponed theorem is
`completionUnitScalarIntertwining`; its proof is `sorry`. Every helper is either an
abbreviation for an existing construction, a fully written formula predicate, or the
explicit composite `actualSameIndex`. There is no choice of undetermined data in a
definition. No node statement, dependency list, or proof plan was changed. No new nodes
or dependency repairs were required.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`, especially its first sentence
about identity compact support. The detailed coefficient calculation is the item's
accepted nine-step extracted proof, which the theorem docstring reproduces step by step;
it is not presented as a verbatim Bhatt--Scholze theorem.

Hypotheses and clauses, in the order of the node:

- `D : FiniteFieldDatum.{t}` fixes the finite-field datum and its algebraic closure;
  `point D` is exactly `Spec (.of D.k)`. `l : ℕ`, `[Fact l.Prime]`, and `_hl : l ≠ D.p`
  express the coefficient prime restrictions.
- `E L : Type u` carry fields, `Algebra ℚ_[l]`, and `FiniteDimensional ℚ_[l]` instances.
  `ι : E →ₐ[ℚ_[l]] L` is the inclusion; representing it by an injective field algebra
  homomorphism does not require a proper extension or exclude the identity inclusion.
  The valuation rings, selected uniformizers and positive quotients are the existing
  `Padic.coefficientExtension*` objects, not new choices.
- The site is `(point D).ProEt`, with object universe `t+1` and hom universe `t`.
  Coefficients and modules have size `max u (t+1)`, and derived localization has size
  `max u (t+1)+1`, as in the evaluation calculus. No equality of site universes or
  coefficient and base-field universes is imposed.
- `completedIntegralCommRingSheafUnrestricted` supplies R and S and their actual
  projections. The opening `IsIso quotientComparison` assertions, for E and L, give
  the canonical cokernel/projection identifications. `QuotientTransitions` explicitly
  asserts compatibility with consecutive quotient maps. Its degree-zero single-complex
  embedding is faithful; it is exactly the equality of module-sheaf maps. Index `n`
  everywhere means exponent `n+1`, hence covers all and only the positive quotients.
- `completion D l E A` is just `A.reduction ⋙ coefficientSequenceLimit`, and similarly
  for B at L: these are H_E and H_L. Their units are `A.adjunction.unit` and
  `B.adjunction.unit`, not freely supplied transformations. `ME,ML` are the existing
  ordinary quotient-system models, and `NE,NL` their normalized derived models.
- `CR,CS` have the existing `PrincipalQuotientCompletion.Model` type. The natural
  isomorphisms `α,γ` satisfy `QuotientRealization`. That predicate identifies the whole
  units, and on every flat-term K-flat P identifies strict towers and their augmentations
  and the normalized Roos comparisons. Its `θ` is a tower isomorphism, so includes all
  transitions, rather than unrelated level isomorphisms. Its last equation fixes the
  normalized entire cone comparison.
- `F : scalarModel ...` uses the existing `DerivedChangeOfRingsCochainModel`, over the
  actual `completedCoefficientMap`. `hE` fixes its ordinary functor to the recorded
  coefficient extension, while `σ` is fixed by its equality with the recorded universal
  counit on complexes. Thus its T is the actual derived extension, up to the specified
  canonical comparison; it is not an arbitrary functor.
- `c : F.T ⋙ CS.completion ≅ integralScalarExtensionOfUniverses ...` identifies completed
  scalar extension with quotient completion of ordinary extension. `MultiplicationFormula`
  prescribes the tower isomorphism μ on the generators `(x tensor a) tensor 1`, whose
  image is `x tensor projection(a)`. Because these maps are linear over the finite
  target quotient, this is precisely `(x tensor a) tensor b ↦ x tensor ab`, including
  its inverse. The predicate also fixes both signed cone coordinates and the descended
  comparison with the published strict-tower localization comparison. The equation
  involving `completedScalarComparison` identifies χ with the actual target unit under
  this multiplication comparison. It is natural since c, γ and σ are natural.
- `b` is a natural transformation on the entire unbounded derived category.
  `SameIndexFormula` prescribes it on all resolving representatives before comparing
  it with exchange: `d` is a strict tower transformation at the SAME index n;
  `F(quotientMap_E,n) ≫ d_n = quotientMap_L,n` fixes its balanced residue map.
  Degreewise right exactness of tensor makes the quotient augmentation epic, so this
  equation uniquely determines d_n. Under the actual quotient identifications it says
  `(p tensor abar) tensor z ↦ p tensor iota_n(abar) zbar`: the defining residue
  compatibility of `completedCoefficientMap` is exactly `integralScalarQuotientSheafMap`.
  This characterization remains valid when the ramified finite quotient map is not
  injective. The formula for c uses the canonical product projections, and the formula
  for δ uses `scalarRoosCoordinates` on BOTH coordinates. The final equation specifies
  descent through the existing cochain counits. Thus this is not a map selected from
  the unit equation. `actualSameIndex` explicitly transports this map to H_E,H_L and T.
- `ε` is an isomorphism whose representative formula is the existing
  `PrincipalQuotientCompletion.RepresentativeComparison`: its arithmetic block/selection
  map, its inverse after localization, and its two-coordinate tensor/product comparison
  are retained. `1 ≤ e` permits every positive ramification index. The following unit
  equation is the finite-free completion-exchange normalization. For complete K,
  `b.app K = ε.hom.app K` compares these two independently specified maps.
- The complete-input binder is the dependency's exact
  `IntegralOnSlice.IsComplete ... none K`. Subsequent clauses retain completeness of
  H_E K, T K and completed T K. No boundedness, constructibility or Tor hypothesis is
  present. `uK` and `uX` have homs pinned to the ACTUAL adjunction units; their inverses
  therefore are v^E and v^L. `χK` and `χH` have homs pinned to the published χ at K and
  H_E K. `β` is pinned by
  `χH.inv ≫ actualSameIndex.app K ≫ H_L.map χK.hom`, exactly the node's conjugation in
  Lean's left-to-right composition notation. The final equality
  `β.hom ≫ uX.inv = completedT.map uK.inv` is the required equality of derived morphisms.
  These pointwise isomorphisms have specified homs made from natural transformations,
  so their uniquely determined inverses and β are natural on the full complete
  subcategory; no arbitrary complete-object lifting is being asserted.

Dependency declarations read and used (the recorded dependency modules are imported):

- `Sheaf.Paper.FiniteCoefficientPoint`: its geometric point and the given finite-field
  setting, notably `pointFibreBaseIsAlgClosed`; no fibre equivalence is used here.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, and the completed coefficient sheaf and
  projections it reexports.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `coefficientSequenceLimit`, `scalarReductionSource`.
- `Sheaf.Paper.CompletionUnitStrictQuotientModel`:
  `CompletionUnit.completionUnitStrictQuotientModel` and its reexported
  `OrdinaryModel`, `DerivedModel`, `tower`, `coneAugmentation`, `completionComparison`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete` (none branch).
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`:
  `purNormalizedReconstruction` and `purNormalizedReconstructionAdjunctionCalculus`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: its ordinary derived-change
  theorem is retained as the recorded proof interface; the existing generalized
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` supplies the cochain counit
  interface with the independent module/localization sizes required here.
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`: `integralScalarTowerFunctor`,
  `integralScalarTensorSection`, quotient maps and transitions; its public universe
  interface gives `integralScalarExtensionOfUniverses` and its normalized comparison.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: `completedCoefficientMap`,
  `completedOrdinaryScalarExtension`, `completedDerivedScalarExtension`,
  `completedScalarCounit`, `completedScalarTensorSection`, `completedScalarComparison`.
- `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange`:
  `PrincipalQuotientCompletion.Model`, `sourceTower`, `targetTower`,
  `scalarRoosCoordinates`, `RepresentativeComparison`, `finiteFreeCompletionExchange`.
  The current server source was also read with `scompile.py --source` while diagnosing
  inference; the interface was usable without a dependency repair.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `strictRoosComparison`, and the
  existing `roosF`, `roosP`, `roosχ` interface.
- `Sheaf.Paper.PrincipalKoszulStrictReplacement`: actual `uniformizer`,
  `quotientComparison`, `residueStep` and `completed_exact`.
  The remaining stated proof-dependency modules and Mathlib's localization universal
  property are imported privately for stage 3.

Edge cases checked: K=0; E=L and the identity inclusion; the first positive exponent;
unbounded K; residue-degree extensions; ramified index e>1. In the model t=w² the
same-index O_E/t² → O_L/w² need not be injective; neither the formula predicate nor
the theorem ever inverts this finite map. Only the descended map on complete inputs
is asserted invertible. The site and coefficient universes remain independent.

Searches actually run through msearch.py:

- LeanFinder, `finite free coefficient scalar extension intertwines actual derived
  completion units through quotient Roos cones`: eight hits on ordinary adic completion,
  formal smoothness and adic tensor products, no derived sheaf/unit statement.
- Loogle, `NatTrans.naturality, CategoryTheory.IsIso`: zero hits, unknown identifier
  `NatTrans.naturality`; not treated as evidence that naturality is absent.
- Mathlib grep, `completion.*[Uu]nit|[Uu]nit.*completion`, CategoryTheory: zero hits.
- LeanSearch, `derived completion scalar extension unit same index Roos cone comparison`:
  eight unrelated uniform-space/adic-completion hits, no match.
- Direct project rg of completion/unit and scalar-intertwining names found the existing
  finite-free comparison, strict quotient unit model, and other completed exchange
  interfaces. I read the relevant candidates; none states this coefficient-normalized
  same-index/arithmetic comparison and final actual-unit identity. The upstream
  `SixFunctors.ProEtale.FiniteCoefficient.Derived.CompletedExchange` works with a
  different discrete coefficient-ring sheaf encoding and geometric exchange maps.
  Direct grep for this node id in `lean/WeilConjectures` returned no match; direct rg for
  `completionUnitScalarIntertwining|PodCompletionScalar` and the upstream names index
  also returned no match before writing.

Validation: all compiler probes used module mode and scompile.py. The complete module
compiled in both sandbox and library positions within the 60-second limit. Inference
issues were repaired by explicit source/target ring and universe arguments, without
changing mathematical universes or imposing new hypotheses. All lines fit 100 columns.
There is one theorem and its proof is `sorry`; no proof was supplied at stage 2.

## Second reading by Q50

Worker's second pass, with the node and finished file reopened; the dispatcher's separate
maintainer review supplies the independent review. I checked the actual-unit equality
in QuotientRealization, both Roos coordinates in SameIndexFormula, multiplication's
residue and cone formulas, the independently normalized arithmetic RepresentativeComparison,
and the domains of every factor of β. This pass made quotient-transition compatibility
explicit as QuotientTransitions. The main hypotheses remain D, the prime and its
characteristic inequality, finite coefficient fields and their inclusion, and derived
completeness of the arbitrary input. In particular no finite-stage inverse was introduced
for ramified extensions. The inverse-unit equality uses uX at COMPLETED scalar extension,
not at ordinary scalar extension, as the node requires. No statement fault or
STATEMENT-DISPUTED issue was found.
