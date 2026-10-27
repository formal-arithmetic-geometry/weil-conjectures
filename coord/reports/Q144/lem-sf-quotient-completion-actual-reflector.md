## Worker report

Q144 states `lem-sf-quotient-completion-actual-reflector` in
`Sheaf.SixFunctors.QuotientCompletionActualReflector`, declaration
`WeilConjectures.IntegralQuotientCompletion.actual_reflector`.
Only this named theorem has a postponed proof. Its docstring gives the source and
all five proof steps of the DAG node. The six auxiliary declarations contain real
data: four local fixed-size standard instances, the transpose of the existing strict
quotient tower, and its localization on the existing resolving class. The repair adds one existing:true definition-node owner, with no new Lean notion,
dependency module, mathematical statement correction, or disputed assertion.

The source was read in `literature/stacks-project/algebraization.tex`, Tags 099B
and 0A0E, together with the current blueprint unit and proof under
`literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/`.
The comparison is in the ordinary derived category, not just on cohomology.

Clause-by-clause translation:

- Prime and coefficient field: `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded coefficient API
  supplies `PbcIntegralRing l E`, `pbcUniformizer l E`, and `pbcIntegralDatum l E`.
  The latter contains the adic hypotheses as data, so no extra unproved adic
  assumption is inserted. The uniformizer is the recorded choice; its ideal is
  the valuation maximal ideal. Positive exponent n is indexed by `n + 1`.
- The scheme is `(T : Scheme.{u})`; the site is exactly `T.ProEt` with
  `ProEt.topology T`. Its object universe is u+1 and morphism universe is u.
  Coefficients use the common ambient lift u+1 of the recorded coefficient
  comparison/intrinsic interface; the ordinary derived category uses u+2.
  No equality of the site's object and morphism universes is imposed.
- `completedIntegralCommRingSheafUnrestricted l E T` is the limit of the actual
  constant finite quotient sheaves. `IntegralOnSlice.Mod l E T none` and
  `IntegralOnSlice.D l E T none` are the recorded module category and its
  ordinary unbounded derived category over this ring.
- `strictTower` is literally `IntegralOnSlice.tower` followed by the existing
  `PrincipalQuotientCompletion.transpose`. `representativeTower` restricts this
  functor to `IntegralOnSlice.Good` and applies `DerivedCategory.Q`.
  `Good` means K-flat and every term flat on the site. The natural comparison
  `lam : qGood ⋙ Q ≅ representativeTower` characterizes Q as the derived strict
  quotient tower, with every transition, on one such representative.
  `qGood` is the recorded resolving localization, so this covers all unbounded
  objects and their morphisms, not just a chosen subcategory of complete inputs.
- C is the composite `Q ⋙ koszulRlim`. Here `koszulRlim` is the published total
  right derived inverse limit of strict towers, not its termwise limit.
  The first conjunction, for every good P, equates eta after `rlim.map lam`
  with `RegularRoosKoszul.augmentedUnit` applied to the actual
  `IntegralOnSlice.augmentation`. The latter sends the generator to 1 tensor x
  in the recorded scalar-extension convention (x tensor 1 after symmetry).
  Thus eta is the actual quotient augmentation, including the derived-limit
  unit. It is not an arbitrarily chosen map to an isomorphic object.
- The first two conjunctions normalize the residue isomorphisms q by their
  values on every `Ideal.Quotient.mk`, and e by every finite quotient projection.
  This is exactly the canonical presentation comparison, not an arbitrary
  ring-sheaf isomorphism. `pbcDerivedRestrict e.inv` carries source-presentation
  modules to B-modules.
- The second inner conjunction specifies Lambda and kappa on every complex C
  over the intrinsic presentation: b identifies Lambda of its transported
  derived object with transport of `intrinsicCompletionComplex ... 1
  (fun _ : Fin 1 ↦ pbcUniformizer l E) C`; its equation identifies kappa with
  the transported `intrinsicCompletionComplexUnit`. Those are the published
  signed fiber and its zero-second-coordinate (u,0) unit. No new Koszul
  completion is defined here. Every derived object has a complex representative,
  and restriction along e is an equivalence, so this specifies the objects and
  units on the entire category. The Hom universal property below also fixes
  the induced action on morphisms uniquely up to the unit-preserving comparison.
- `a : Λ ≅ Q ⋙ koszulRlim` is a natural isomorphism; the next conjunction is
  exactly `∀ H, κ.app H ≫ a.hom.app H = η.app H`. The representative equation
  for eta uses the normalized total-derived-limit comparison. Together with
  the transported intrinsic unit, it fixes the unit-compatible comparison.
- The next conjunction states local completeness inline: it quantifies over every
  actual slice U, every ring section s, and a covering sieve on which s is a
  multiple of `integralCompletionScalarValue`. It requires
  `IsZero (integralCompletionLocalTest ...)`. This is the expansion of the old
  predicate, using the existing local test with a body identical to `localTest`.
  The local test is derived internal Hom from the
  degree-zero section-localization module into the derived slice restriction.
  This tests all local sections, not merely a global uniformizer. Regularity of
  t on B makes locally divisible sections glue uniquely, so these are precisely
  the sections of tB(U) in the node.
- For all H and all locally complete L, the next conjunction is
  `Function.Bijective (fun f ↦ η.app H ≫ f)`, and also the Koszul Hom bijection
  `Function.Bijective (fun g ↦ κ.app H ≫ g)`. The displayed equation for every f
  identifies those maps under a, with the composition order required in Lean.
- The final `∀ H, List.TFAE [...]` lists in order local completeness,
  `IsIso (κ.app H)`, `IntegralOnSlice.IsComplete ... none H`, and
  `IsIso (η.app H)`. The third predicate is the recorded quotient Roos triangle
  definition. All H binders are unrestricted ordinary unbounded derived objects.

Recorded dependencies read and used (module — declaration/interface):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` —
  `Padic.finite_coefficientExtensionRing` and its imported coefficient rings.
- `Sheaf.Paper.AdicCoefficientDatum` —
  `AlgebraicGeometry.Scheme.completedReductionTower`, the adic datum and limit.
- `Mathlib.AlgebraicGeometry.Sites.Proetale` — `AlgebraicGeometry.Scheme.ProEt`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` —
  `WeilConjectures.integralConstantToCompletionOfUniverses` and the completed
  coefficient sheaf/projections it imports.
- `Sheaf.CategoryTheory.RingedSiteModules` — `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` — `DerivedCategory`,
  `DerivedCategory.Q`, and `HasDerivedCategory.standard`.
- `Sheaf.Paper.IntegralReductionTowerCanonical` —
  `WeilConjectures.canonicalIntegralReductionTower`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` —
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` —
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` —
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.ExactProductFunctorStrictLimit` —
  `CategoryTheory.exactProductFunctorStrictLimit`.
- `Sheaf.Paper.IntrinsicCompletion` — the published
  `intrinsicCompletionComplex` and `intrinsicCompletionComplexUnit`, publicly
  retaining the original completed-coefficient fiber and its unit from
  `IntrinsicCompletionCompleted`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` —
  `CategoryTheory.ordinaryModuleDerivedInternalHom`; its public generic
  derived-internal-Hom interface is used by the existing local-test predicate.
- `Sheaf.Paper.DerivedCompleteOnSlices` —
  `WeilConjectures.IntegralOnSlice.IsComplete`.
- `Sheaf.Paper.IntegralCoefficientPresentationComparison` —
  `WeilConjectures.IntegralCoefficientPresentation.comparison` and `.level`.

The signature uses these definition interfaces, whose owning nodes are added to
stmt_deps (no other original non-lean field changes):

- `def-pur-integral-derived-operations`,
  `Sheaf.Paper.IntegralDerivedOperationsOnSlices` —
  `IntegralOnSlice.Mod`, `D`, `Cx`, `Good`, `qGood`, `tower`, `augmentation`.
- `def-sf-integral-local-completion-test`,
  `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` —
  `integralCompletionScalarValue` and `integralCompletionLocalTest`. There is no
  application of the completeness-equivalence theorem or characteristic
  hypothesis on T. The local completeness proposition is inline in all three
  occurrences, rather than adding a theorem dependency for a plain definition.
- `def-pur-principal-quotient-completion-model`,
  `Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel` —
  `PrincipalQuotientCompletion.transpose`.
- `def-sf-koszul-total-derived-limit`,
  `Sheaf.Paper.DerivedCompleteKoszulReconstruction` — `koszulRlim`.

- `def-sf-normalized-strict-tower-augmentation`,
  `Sheaf.SixFunctors.RegularRoosKoszulUnit` — `RegularRoosKoszul.limitComparison`,
  `.constantUnit` and `.augmentedUnit` (new existing:true definition-node owner).
- `def-weil-pbc-bounded-constructible-tower`,
  `Sheaf.Paper.BoundedConstructibleTower` — `pbcModules`, `pbcAdicCompletion`,
  `pbcAdicProjection`, `pbcDerivedRestrict`, and the presentation comparisons.
  Only their definitions are used; H is not bounded or constructible.

Each existing interface has a usable recorded lean record. Traversing both statement and proof
edges from each of these nodes does not reach this item, so the additions create
no dependency cycle. The plain augmentation definitions now have the explicit
new definition-node owner; the conclusion of `lem-sf-regular-roos-koszul-unit`
remains only a proof dependency. All other original proof dependencies are
imported and described in the theorem's proof docstring.

Edge cases checked on the mathematical statement and definitions:

- Zero object: both towers/units give zero, both Hom maps are bijections and all
  four completeness predicates hold.
- Empty T: module and derived categories are trivial; no nonemptiness hypothesis
  is introduced.
- B[1/t] on a nonempty site: reductions and completion vanish, while the original
  localized module is generally not complete. This verifies why H is not assumed
  complete and why eta must be the actual augmentation.
- Finite t-power torsion coefficients: completion recovers the object; the first
  level is exponent one, not exponent zero.
- No boundedness, constructibility, finite Tor-amplitude, invertibility of l on T,
  or completeness of H is inserted. L alone is required locally complete in the
  Hom assertion. Testing all ideal sections is retained even for section zero.

Searches for an exact existing declaration:

- `msearch.py ... leanfinder` with query "The actual quotient augmentation of
  derived inverse limit of reductions is a reflector onto locally derived
  complete sheaves of modules, compatible with intrinsic Koszul completion":
  eight results about condensed adjunctions, sheafification, ordinary adic
  completion, and local cohomology; no exact statement.
- `msearch.py ... leansearch` with the same query: eight ordinary adic-completion
  declarations (`AdicCompletion.module`, `AdicCompletion`, `IsAdicComplete.of_lift`,
  `AdicCompletion.of_apply`, `IsAdicComplete.of_comp_lift`, `AdicCompletion.of`,
  `AdicCompletion.lift`, `AdicCompletion.congr`); no exact statement.
- `msearch.py ... loogle "CategoryTheory.Reflective, AdicCompletion"`: zero hits.
- `msearch.py ... grep "quotientCompletion|koszulCompletion|derivedComplete"`:
  two unrelated uniform-space completion hits.
- `rg` in the prescribed project source directories with
  `quotientCompletion|ActualReflector|actual_reflector|quotient_completion|lem-sf-quotient-completion-actual-reflector|intrinsic.*[Tt]ransport|completedIntrinsicCompletion`
  found the component completion interfaces, but no exact theorem. The exact
  item search in `WeilConjectures` and `dag/lean_names_upstream.json` had no hit.
  The existing regular-unit theorem lacks this completed-coefficient transported
  intrinsic interface and Hom reflection clause, so it is a dependency, not an
  existing match.

Validation: scompile.py compiled the delivered file successfully in both sandbox
and named-library mode against the live published library. No compiler errors or
unexpected warnings. Only the one named theorem has `sorry`; no definition does.

## Second reading by Q144

After the first clean compile, Q144 reread the node and the complete Lean
signature, checking every quantifier, coefficient transport, composition
orientation, the restriction direction e.inv, and every local ideal section.
The dispatcher explicitly forbids starting other agents, so this is an honest
second pass by the same worker; the maintainer's independent delivery review is
still required. No mathematical mismatch was found. During compilation the
worker removed unavailable instance names and made all total-derived-limit
universe arguments explicit; all declarations now compile. No node statement
was changed. The return provided the maintainer's independent mathematical check
of all clauses. In this repair, the inline predicate was checked against both
published bodies, every original hypothesis and conclusion was retained, and
the new definition node was read against all three existing declaration bodies.
The four helper instances are now local; their real data is unchanged.


## Repair of returned head 0160dc5f78b1

1. H2 (theorem-only statement dependencies): removed the two additions
   `lem-pur-integral-principal-cone-local-criterion` and
   `lem-pur-roos-intrinsic-completeness-equivalence`. The existing definition node
   `def-sf-integral-local-completion-test` now supplies the scalar and local test.
   All three local completeness occurrences are written inline, using exactly
   the same covering-sieve divisibility condition. `integralCompletionLocalTest`
   and the former `IntegralPrincipalCone.localTest` have identical bodies,
   including the standard slice instances, restriction and derived internal Hom.
2. H2 (actual augmentation ownership): added
   `def-sf-normalized-strict-tower-augmentation` as existing:true for the three
   published real definitions `limitComparison`, `constantUnit`, `augmentedUnit`,
   and cited it in the item's stmt_deps. No definition is copied and no theorem
   conclusion is promoted to a statement hypothesis.
3. Advisories: cited `def-weil-pbc-bounded-constructible-tower` for the pbc
   coefficient/restriction interfaces, publicly imported its module, and made
   all four priority-5000 helper instances `local instance`.

The retained sandbox was compared with current main: before this repair only
stmt_deps and lean differed in the node, with no source-statement drift. The
returned version was the retained module; the repair changes its imports,
instance attributes and the three definitionally equivalent predicates. The
prescribed delivery wrapper prepares the rebased commit on current main.
Fresh scompile.py validation after these edits passed in sandbox and named-library
modes, with no errors or unexpected warnings.

## New nodes

`def-sf-normalized-strict-tower-augmentation` records existing definitions in
`Sheaf.SixFunctors.RegularRoosKoszulUnit` without delivering a duplicate module.
The node defines the comparison selected with koszulRlim, the localization of the
ordinary constant/limit unit followed by this comparison, and its composite
with the derived image of a strict augmentation. Source: Stacks 0941, 09T5 and
0FND, the actual-unit representative formulas used for 099B/0A0E. LeanSearch and
LeanFinder were queried with "The normalized total derived inverse limit
comparison and the constant tower unit followed by the derived image of a strict
augmentation"; Mathlib grep used `limitComparison|constantUnit|augmentedUnit`.
The first tools gave generic derived/ordinary limit ingredients; grep gave no
hits. Their complete returned output is recorded verbatim in mathlib_searches.
The prescribed project/DAG searches found the exact definitions only as helpers
of the theorem node `lem-sf-regular-roos-koszul-unit`, and blueprint_refs.py search
`augmentedUnit` found zero matches. The existing constant-tower-comparisons node
was also inspected and defines evaluation/exact-functor interchange, not these
limit-unit maps. Thus the new record adds definition ownership only, exactly as
requested by H2.

The first repair dry run identified the newly required `import_flags` field and
that local instances must not appear in the exported `lean.declarations` list.
Added the empty flags list and removed the four local instance names from that
list (the instances remain real local data in the module). Separated grouped
DAG citations into individual brackets. No Lean change was needed for these
record fixes. The signature record is verbatim and all new-node citations match
its stmt_deps exactly.
