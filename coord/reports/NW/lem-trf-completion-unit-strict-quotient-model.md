## Worker report

The module `Sheaf.Paper.CompletionUnitStrictQuotientModel` states
`WeilConjectures.CompletionUnit.completionUnitStrictQuotientModel` with one `sorry`.
The source read is the current blueprint rational Frobenius integral-model proof,
(2)--(3), together with Stacks `sites-cohomology.tex`,
`lemma-derived-limit-is-ok` (0941), and `derived.tex`,
`definition-derived-limit` (08TC). The node is an agent normalization refinement,
not a verbatim Stacks assertion. Its seven proof steps are included in the theorem docstring.
No statement correction or new node is required. The definition-node binding repair below
records the existing pure-tensor section explicitly.

The additional definitions are helpers belonging to this node. `OrdinaryModel` and
`DerivedModel` package the specified canonical constructions with their normalization
conditions. Their existence is in the CONCLUSION, together with the unit formulas.
Neither is an extra assumption supplied by the caller. The theorem also supplies a
full coefficient calculus and its coherence, rather than assuming arbitrary reduction
functors or adjunctions. All helper definitions have actual data. In particular,
`coneAugmentation` is the ordinary augmentation followed by the already constructed
`roosι`, and `completionComparison` is an explicit composite of the normalized Roos
isomorphism, the exact-restriction localization isomorphism, and the universal
left-derived comparison. No arbitrary map or choice from a mere existence theorem
is used to define a canonical object.

Hypotheses and clauses, in statement order:

- The prime and finite extension are `(l : ℕ) [Fact l.Prime] (E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded
  `Padic` coefficient rings fix the valuation ring, uniformizer, positive-exponent
  quotients and actual reduction maps. Index `n : ℕ` means exponent `n+1` throughout.
- `(W : Scheme.{t})` and `[∀ x : W, Invertible (l : W.residueField x)]`
  render the scheme and invertibility hypothesis. The inherited `W.ProEt` and
  `Scheme.ProEt.topology W` are the actual small pro-etale site. The independent
  universes `t,u` give site object universe `t+1`, morphism universe `t`, and
  coefficient/module universe `max u (t+1)`. No universe equality is imposed.
- `scalarReductionSource l E W` is modules over the existing completed ring
  sheaf, the limit of the existing finite constant quotient sheaves. All `DerivedCategory`
  occurrences are the ordinary unbounded localization; there is no complete-object
  subcategory and no boundedness hypothesis.
- Every flat-term K-flat `Q` is quantified, with `Q.IsKFlatIndependentCoefficients`
  and `∀ p, (Q.X p).IsFlatOnSite`. For arbitrary derived `N`,
  `q : DerivedCategory.Q.obj Q ≅ N` is precisely the derived class of its
  representative map. This covers every choice of representative; it even allows
  every representative identification in the derived category, not just a selected
  quasi-isomorphism between complexes.
- `OrdinaryModel.tensor`, `evaluation`, and `transition` specify the actual sheaf
  scalar extension at every level and its quotient transitions. `quotient` applies
  it termwise. The `transition` equation uses the dependency's actual
  `coefficientOrdinaryQuotient`, for every ordered pair of levels. `tower` is the
  recorded exact `coefficientSequenceRestriction` applied to complexes.
- `OrdinaryModel.adjunction` is exactly tensor adjoint to ordinary limit of the
  restriction. `unit_tensor` fixes its unit on every section to the actual sheafified
  tensor `1 ⊗ x` (the scalar-first form of `x ⊗ 1`). This specifies the adjunction,
  not just an unrelated pair of functors. The first theorem conjunct repeats this
  formula for the chain augmentation degree by degree.
- `transpose a` is the ordinary complex-adjunction transpose, followed by the
  termwise-limit comparison. `augmentation` is the transpose of the identity.
  Thus its nth projection is `r_n`. The theorem's transpose equality identifies
  the transpose of any `a` with the augmentation followed by `lim U(a)`.
- The complex `H` is the existing `roosF`, with coordinates `roosχ`. Its shifted
  mapping-cone/biproduct convention gives exactly `(-db-(1-s)a, da)`.
  `coneAugmentation` is a chain map by its type. The explicit coordinate conjunct
  is `biprod.lift 0 (Pi.lift ...).f`, so the shifted coordinate is zero as required.
- `S.adjunction` is the reduction/`coefficientSequenceLimit` adjunction. `DerivedModel`
  fixes the left-derived comparison on flat-term K-flat complexes, with the existing
  finite-reduction comparison on every evaluation. `hom_normalization` extends the
  actual ordinary Hom correspondence, preventing a different unit with the same
  projections from being substituted. `systemUnit_composition` fixes the right
  comparison to exact ring restriction followed by sequence projection.
- `D.roos` is one natural Roos identification, normalized by
  `Q.map (roosι Z) ≫ D.roos.hom.app Z = D.limitUnit.app Z` for every tower.
  `limitUnit_normalization` pins that unit on every K-injective tower to the inverse
  of the existing `rightDerivedFunctorObjQIso`, through the ordinary termwise-limit
  identification. These fix the whole derived comparison, not just its projections.
- The main equality is
  `S.adjunction.unit.app N = q.inv ≫ Q.map (M.coneAugmentation ... Q) ≫
  (D.completionComparison ...).hom ≫ L.map (S.reduction.map q.hom)`.
  The final transport only expresses the target in terms of the arbitrary N.
  It is exactly the node's `rho_D [v_Q] [q]⁻¹` in Lean composition order.
- `I,a,J,j` are all universally quantified with precisely `QuasiIso`, K-injectivity,
  and injective degree terms. No K-injectivity of `U(I)` is required.
  `eI` identifies the ordinary-limit model using the system right-derived unit.
  `eJ` is explicitly the inverse-resolution transport of the normalized tower unit.
  The theorem asserts `lim j` is a quasi-isomorphism and that its localization
  carries `eJ` to `eI`: this is the required composition normalization.
- The strict equation
  `(transpose a ≫ lim j) ≫ roosι J = coneAugmentation Q ≫ roosF.map (U(a) ≫ j)`
  is the entire chain-map equality under the zero-coordinate inclusion. The following
  equation specifies the Roos comparison itself as `H(j U(a))`, inverse inclusion,
  and `eJ`. `eCone.hom = Q.map (roosι J)` fixes that inverse inclusion, and its
  quasi-isomorphism is asserted as well.
- The final resolution equality computes the actual unit via `transpose a ≫ lim j`
  and the normalized `eJ`, followed by the inverse resolution and inverse left-derived
  comparison. Every such resolution gives that same unit. Every `q` gives the same
  unit on N. The last theorem conjunct is actual adjunction-unit naturality for
  every derived morphism `h : N ⟶ N'`. Together these render resolution independence
  and naturality without restricting to maps of chosen complexes.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the actual integer ring,
  uniformizer and `Padic.coefficientExtensionRing` constructions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
  `def-weil-size-convention` is a metatheoretic convention; independent explicit
  universes and inherited sheafification/smallness instances implement it.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its public imports:
  `completedIntegralCommRingSheafUnrestricted`, its projection, and finite
  `integralCoefficientCommRingSheaf`. Their full signatures and constructions were read.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, the exact sheaf tensor predicate.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and the public scalar tensor interfaces.
- `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `coefficientSequenceModules`, exact restriction, evaluation, actual transition,
  localization factors, and `coefficientSequenceLimit`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `coefficientOrdinaryQuotient`, and `coefficientFiniteReductionModel`.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `strictRoosComparison`; its existing
  constructions from `Sheaf.CategoryTheory.StrictRoosModel` are used directly:
  `roosF`, `roosχ`, `roosι`, and `roosLimitFunctor`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`
  is imported for the proof plan.
- `Sheaf.Paper.IntegralReductionTowerCanonical` (the recorded definition-node module):
  its public imports expose `unrestrictedIntegralTensorSection`, the actual sheafified
  pure tensor, defined in `Sheaf.Paper.IntegralReductionTowerUnrestricted`. The spelling
  `unrestrictedTowerTensorSection` in the unchanged signature is definitionally that
  same term. The item cites `def-weil-integral-reduction-tower` for this notion, together
  with `def-weil-strict-roos-model` for the cone constructions. The resolution-independence
  theorem is not a statement dependency. No node or construction is duplicated.
- All remaining stated proof dependencies are imported without `public`, including
  exact products, the sequence-projection adjunction, resolving normalization,
  derived pushforward composition, pushforward/limit projections and the
  sequence-site equivalence. Their relevant signatures were read.

Edge cases checked: Q=0 and the empty scheme give zero maps; a point with N=R
has the ordinary compatible quotient augmentation; a point with N=E has zero
quotients and zero completed reduction, so the unit need not be invertible.
Unbounded complexes are allowed in all integer degrees. Level zero in Lean is
exponent one, so the finite tower never accidentally includes the exponent-zero
quotient. Arbitrary q and arbitrary a,j, including identity resolutions whenever
they satisfy the stated conditions, are retained. No completeness assumption occurs.

Searches actually run using `msearch.py` for NW and this item:

- LeanFinder: "The actual derived completion adjunction unit on a strict K flat
  quotient tower is its zero shifted coordinate Roos augmentation" — eight generic
  derived-adjunction hits (`derived_unit`, `derivedη` etc.); none states this quotient
  system or two-resolution normalization.
- Loogle: `CategoryTheory.Adjunction.derived_unit` — one generic theorem. Read the
  derived unit/factorization API in Mathlib's `Functor/Derived/Adjunction.lean`;
  it is an ingredient, not this assertion.
- grep: `Roos|derived_unit`, subdirectory `CategoryTheory` — zero hits reported
  by the wrapper. Direct project searches below found the existing Roos ingredients.
- LeanSearch: "Derived completion adjunction unit is the strict quotient tower Roos
  augmentation with zero shifted coordinate" — eight generic adjunction or completion
  hits, with no exact assertion.
- Direct `rg` searches of both `lean/WeilConjectures` and `lean/Sheaf` for completion
  units, Roos, strict quotients, and the node id found the existing completion and
  Roos constructions but no declaration for this node. The upstream adic completion
  unit only has reduction invertibility/completion statements. The strict-Roos theorem
  computes a general augmentation, not its identification with this adjunction's unit.
  No exact-match declaration is available.

Validation: compiled through the prescribed `scompile.py` against the live server.
Only the displayed theorem is postponed; no additional theorem is proved here.

## Repair of returned head 43763eb2cdb6

H2/C5: removed `lem-weil-integral-reduction-tower-well-defined` from the saved
item's statement dependencies and added the existing definition node
`def-weil-integral-reduction-tower`. The current base did not list the removed
theorem dependency: it had been introduced only by this delivery. The new direct
import is the definition node's recorded `IntegralReductionTowerCanonical` module.
Read `unrestrictedTowerTensorSection` in the former theorem module: its entire
body is `unrestrictedIntegralTensorSection l E Y n M U s x`. Read the latter
definition in `IntegralReductionTowerUnrestricted`: it sheafifies the sectionwise
pure tensor and transports along the scalar-extension object's defining equality.
Its docstring already names `def-weil-integral-reduction-tower` as its blueprint.
Thus this is the existing definition the return requested. No use is made of the
well-definedness theorem conclusion, and no choice of that theorem is involved
in this wrapper. `lean.statement` and the complete theorem declaration are
verbatim unchanged; the only Lean-file edit is this direct import.

The original saved packet first passed the required `deliver2.py --no-push`
(commit 0a2895e9ed5). It was then repaired as above, rather than re-pushed unchanged.
All original hypothesis, clause, universe and edge-case checks above still apply.
The advisory about the dependency's existential calculus S is retained: the item
states existence of S together with its coherence and the explicitly normalized
ordinary/derived models, as accepted in the return.

## Dependency modules

`def-weil-integral-reduction-tower`: lean-only §1(B) binding repair; no new module.
Retains `WeilConjectures.canonicalIntegralReductionTower` and the other previously
recorded tower declarations, and records the omitted existing helper
`WeilConjectures.unrestrictedIntegralTensorSection`. The existing recorded module
publicly imports this helper through the former well-definedness module. The
`existing: true` record reuses this published module. The node's statement, source,
dependencies and all other non-Lean fields are unchanged. Its `lean.note` explains
why the old declarations list did not expose the section needed by this consumer.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
