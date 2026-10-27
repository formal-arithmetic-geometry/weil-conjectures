## Worker report

Module: `Sheaf.Paper.SystemEnrichedProjectionAdjunction`; namespace
`WeilConjectures.SystemEnrichedProjection`; principal statement
`systemEnrichedProjectionAdjunction`. Stage 2 only: one named theorem has `sorry`;
all definitions have actual data. The original mathematical statement is unchanged.
The three additions to stmt_deps are already landed nodes used for actual support
functors, K-flat tensor normalizations, and the coefficient ring in degree zero.
There are no new nodes or dependency replacements.

The statement is packaged in `Conclusion`, whose fields are propositions about
explicitly defined morphisms. `IsIso` fields give actual isomorphisms via `asIso`;
the displayed inverse equations identify their inverses with `backward`,
`towerBackward`, and its actual derived-limit image, respectively.

Hypotheses, clause by clause:

- The global algebraically closed finite-field datum is `D : FiniteFieldDatum`.
  The coefficient prime is `l` with `[Fact l.Prime]` and `_hl : l ≠ D.p`.
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` are exactly the finite coefficient extension.
  The imported `SystemInternalHom.coefficients l E` is the strict diagram of
  `ULift (Padic.coefficientExtensionRing l E (n+1))` with actual quotient maps.
  The universe lift is the recorded coefficient presentation, not another ring.
- `X` and `Y` have `Over (Spec D.k)` instances. Each structure morphism has
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`. The same three properties
  are required of the base-compatible `f`; `c : Compactification f` supplies
  the actual open immersion and proper morphism.
- `Et l E W` is the existing ordinary unbounded derived category of module
  sheaves on the vertical sequence site. Its rings and transitions are those
  of `Etale.SystemProjection`; there is no cartesianness imposed on test objects.
  Exact evaluation, derived scalar reduction, and transition adjuncts come from
  `RX.etale` and `RY.etale` (the dependency's `SemilinearSections.Data`).
- `RX` and `RY` are the recorded representability presentations. Their existence
  is already the conclusion of the dependency theorem, not a new geometric
  assumption. They carry the existing etale/pro-etale comparisons, actual
  structure images, closed tensors, exact evaluations and point sections.
- `support : Etale.SystemProjection.Support c coefficients` fixes
  `F = support.F` definitionally to exact `j_!` followed by total derived `p_*`.
  `G` and `adj : support.F ⊣ G` are the actual adjunction, including its unit and
  counit. The result works for that supplied adjunction, not one reconstructed
  by choosing some finite adjoints.
- `ProjectionData` supplies the canonical geometric projection presentation.
  Its existence is a CONCLUSION (`Nonempty ProjectionData`), before the universal
  assertion using a presentation. Thus the helper data add no existence
  hypothesis. `PullTensor.model` fixes the comparison on K-flat total complexes,
  and `PullTensor.pure` fixes its ordinary adjunct on every pure tensor.
  `ordinaryPush` is normalized by `sections` using `structureSiteIso` (the actual
  base-change associator); `composition_termwise` is its adjunction mate followed
  by exact localization. `open_transpose` fixes the open comparison by the open
  unit. `ProjectionData.component` is the proper-counit transpose followed by
  the mapped open comparison. `_canonical` identifies every component of `π`
  with this word. Therefore `π` cannot be an arbitrary map with convenient fibers.
  Its being a natural isomorphism renders precisely the assumed invertibility
  of the canonical natural system projection at every test and input.
- `M,N`, `hM,hN,hFM,hGN` express normalization of the four inputs using
  `EtNormalized`, the actual scalar-extension adjunct transition criterion.
  `fM,fN,fFM,fGN` use `EtFinite` and the dependency's actual evaluations. These
  mean bounded constructible finite-Tor at each level, without a uniform bound
  or amplitude across levels.

Conclusions, clause by clause:

- `representingObject` is imported: actual `Ra_*` of system internal Hom.
  `representingEquiv` is the dependency's geometric adjunction followed by its
  closed transposition. `testEquiv` is exactly theta, inverse projection,
  actual adjunction, inverse lambda. `forward` and `backward` evaluate these
  mutually inverse all-test bijections at identities in the system category.
- `Conclusion.system_isomorphism`, `forward_inverse`, `inverse_forward` assert
  invertibility and both morphism equations in the ordinary SYSTEM derived
  category, before any evaluation. `tests` and `inverse_tests` identify the
  represented natural transformations for every unrestricted punctual test.
- `forward_transpose` spells out the actual unit followed by `G.map` of inverse
  projection and theta. `inverse_transpose` spells out projection followed by
  `F.map` of lambda followed by the supplied `adj.counit`. Taking the test to be
  the source identity gives exactly the stated defining counit transpose.
- `naturality` and `inverse_naturality` are the two squares for arbitrary
  `m : M' ⟶ M`, `n : N ⟶ N'`; `representingMap` uses the existing internal-Hom
  bifunctor and actual structure pushforward. These squares in fact need no
  normalization assumptions on the auxiliary pair.
- `finite` is `FiniteCompatibility`. It quantifies over each positive exponent
  `n+1`, every exact point evaluation, and each `FiniteAdjunction` identifying
  the supplied system adjunction counit-compatibly with the actual finite
  compactification functor. The counit equation retains both natural comparison
  isomorphisms, with their directions explicit. The conclusion gives the
  representing-object comparisons, both finite inverse equations, and equality
  of the evaluated inverse with `finiteBackward`. This last map is explicitly
  the finite counit transpose of the published `projectionMapOfCompactification`
  and mapped finite evaluation. `finitePullComp` uses the published geometric
  pullback compositor. In addition, `tX,tY` compare tensor evaluation with the
  finite tensors: the two all-test transpose equations and the finite projection
  equation specify the comparisons compatibly with the actual representing
  bijections. This is more precise than bare unnamed isomorphisms of objects.
  The fixed-coefficient API writes the mapping input before the pulled-back
  test; these tensor comparisons carry the symmetry convention explicitly.
- `degree_zero` is `UnitCompatibility`: the test is the actual coefficient ring
  system in degree zero (`pointUnit`, defined by the existing unit complex).
  Unit-action identifications and the projection-unit equation are asserted
  together with the two transported all-test formulas. The formulas are
  literally `adj.unit.app U ≫ G.map h` and `F.map g ≫ adj.counit.app V`.
- `towerForward` and `towerBackward` conjugate the SYSTEM maps through the
  dependency's canonical `mappingComparison`, with invertibility supplied by
  `Representability.mapping_iso` for the four hypotheses already present.
  They are morphisms between the actual pro-etale mapping systems in the
  ordinary derived category of abelian towers. `tower_isomorphism` and the two
  `tower_*inverse*` fields assert the stated isomorphism and its actual inverse.
  `tower_tests`, `tower_inverse_tests`, and `tower_naturality` retain the test
  and naturality equations through these comparisons/underlying sections.
- `coefficientMappingLimit` is the existing total right derived inverse limit,
  not a cone selected from a homotopy-limit triangle. `limit_isomorphism`,
  `limit_forward_inverse`, `limit_inverse_forward`, `limit_naturality`,
  `limit_tests`, and `limit_inverse_tests` assert the corresponding actual
  functor images, including inverse and projection/test equations in D(Ab).
  The forward and inverse transpose equations above identify those transported
  all-test equations with the projection words.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public inputs:
  `Padic.coefficientExtensionRing`, uniformizer and quotient transition data,
  reused through `SystemInternalHom.coefficients` rather than redefined.
- Mathlib scheme morphism properties and small etale/pro-etale sites:
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `Scheme.smallEtaleTopology`,
  `Scheme.ProEt.topology`; compactifications from
  `WeilConjectures.Compactification.RefinementCategory`.
- `Sheaf.Paper.SystemInternalHomRepresentability`: `Et`, `EtData`, `etHom`,
  `Representability`, `representingObject`, `representingEquiv`, `EtNormalized`,
  `EtFinite`, `mappingComparison`, `PointSections.derived`. This is the controlling
  interface and publicly imports the coefficient-system comparison, normalized
  scalar reductions, internal Hom, constructibility and Tor-amplitude interfaces.
- `Sheaf.Paper.EtaleSystemProjectionData`: `Support`, `Support.F`, `Image`,
  `Image.P`, `Image.R`, `OpenImage.J`, actual ordinary/derived adjunctions,
  `Evaluation.E`, and the normalized sequence-site direct image.
- `Sheaf.Paper.SemilinearSystemModels`:
  `TensorComparisonModel`, `tensorSection`, `Data.tensorModels` (through the
  existing semilinear calculus); no replacement tensor or scalar reduction.
- `WeilConjectures.SixFunctors.Etale.Derived.Hom`:
  `Etale.derivedHom`, `Etale.derivedTensorHomAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`:
  `Etale.derivedUpperStarLowerStarAdjunction`, `Etale.leftDerivedUpperStarComp`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection`:
  `Etale.rightDerivedLowerShriekOfCompactification`,
  `Etale.projectionMapOfCompactification`.
- `def-zl-ringed-derived-closed-symmetric-monoidal-data` (existing definition node),
  module `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `CategoryTheory.ringedTensorUnitComplex`, used by `pointUnit` for the actual
  coefficient ring system in degree zero.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientSequenceGlobalHom`, `coefficientMappingLimit`.
- Mathlib `Iso.homCongr`, `Adjunction.homEquiv`, `conjugateIsoEquiv`,
  `MorphismProperty.Over.pullbackComp`, `NatIso.prod`; the upstream exact-derived
  `Functor.mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`.
- Proof-only imports supply Yoneda full faithfulness, the unit-normalized
  projection-mate theorem, and the independent-coefficient strict-tower limit.
  The stored projection proof dependency currently has no own Lean record;
  its required canonical arrow is constructed here from actual proper/open
  adjunctions, not assumed as an unnamed family of maps or a downstream theorem.

Searches for an existing statement:

1. `msearch.py ... leanfinder "An adjunction and an invertible tensor projection
   give an isomorphism of represented internal Hom coefficient systems"`: eight
   generic representation/condensed internal-Hom results, no matching system theorem.
2. `msearch.py ... loogle "CategoryTheory.Adjunction.homEquiv, CategoryTheory.yoneda"`:
   `Adjunction.representableBy_homEquiv`, no geometric mapping-system result.
3. `msearch.py ... grep
   "internalHomAdjunction|mateEquiv_counit|representableBy_homEquiv" CategoryTheory`:
   fifteen generic adjunction/internal-Hom hits, not the stated theorem.
4. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item and enriched
   adjunction/projection/internal Hom found no exact statement. The existing
   `ClosedAdjunctionEnrichedIsomorphism` concerns a different closed-adjunction
   comparison with a right-adjoint image as target; it is not the punctual
   mapping-system comparison here. It was read rather than copied.
5. Read the recorded dependency declarations and their docstrings; reused the
   newly landed representability and system-projection interfaces. Inspected the
   generalized semilinear tensor model and actual finite projection formula to
   retain canonical normalizations and the independent site/coefficient sizes.

Edge cases checked: zero tests and zero inputs impose no exclusions; identity
adjunction/identity compactification specializes to identity mapping comparison;
empty schemes are not excluded; arbitrary unbounded tests P are allowed; n=0 in
Lean is A_1, and all positive exponents occur; normalization retains equality
indices and all actual quotient maps; bounds may vary with n; etale site objects
have universe u+1 and morphisms u, with coefficients in u+1, without equating
object and morphism universes. No perfectness or uniform amplitude is added.

Sources: the node retains its full seven-step ordinary-system argument and its
source locator at the removed older integral-exceptional-adjoint proof. The
current blueprint's `fix-lem-tensor-adjunction.proof.md` still gives the same
all-test tensor-Hom/projection/adjunction chain and canonical units/counits.
The delivery follows the retained node statement; it does not silently replace
it by a new blueprint unit. No mathematical dispute or statement correction.

## Second reading by Q38

I reopened the node and final module for a separate clause audit (the dispatcher
explicitly forbids starting another agent). The hypotheses are mapped above:
finite-field datum and prime restriction; finite E; separated finite-type base
schemes and f; compactification; actual strict semilinear ordinary derived
categories; actual support adjunction; canonical invertible projection; four
normalization and per-level finite-Tor/constructibility conditions. All occur in
the signature or the recorded interfaces actually used, not merely comments.

The first draft had only an arbitrary natural projection isomorphism parameter.
This was insufficient for the canonical-map clause. It was replaced in the main
statement by equality with `ProjectionData.component`, normalized at the ordinary
pure-tensor, K-flat, section-compositor and open-unit levels. Existence of this
presentation was moved into the conclusion, so a missing construction was not
made an extra mathematical hypothesis. The initial finite comparison clause
was strengthened by the two all-test transposition equations and the explicit
finite projection compatibility, excluding a bare unnamed comparison. Finite
tensor order was reconciled with the upstream M-first convention using those
comparisons; no automatic braiding instance was assumed.

I checked both composition directions in the system and tower equations,
`Iso.homCongr`'s inverse-projection orientation, both naturality squares, both
counit and unit transposes, the counit-compatible finite-adjunction square,
A_1 indexing, and the two H0 formulas. The tower and derived-limit maps use the
canonical recorded comparisons and actual functors. No conclusion is justified
solely from evaluations, and no new assumption of faithful evaluation appears.
Every helper has a source/blueprint docstring; the theorem contains the complete
seven-step retained proof. The only postponed proof belongs to this DAG node.

## Returned delivery repair (2026-10-24)

H2, returned head `5d47b620d8ec`: replaced the added theorem statement dependency
`lem-sf-ringed-derived-closed-symmetric-monoidal` with the landed definition node
`def-zl-ringed-derived-closed-symmetric-monoidal-data`. Its existing Lean record
explicitly owns `CategoryTheory.ringedTensorUnitComplex`, the definition used by
`pointUnit`. The theorem conclusion is not used by this statement. The dependency
line above now records the definition node. The retained Lean module and its
signature are unchanged.

Self-check: compared the packet with the current live node; the only differences
are the Lean record and the three added, landed definition dependencies. Checked
the definition node's declaration list and the full `ringedTensorUnitComplex`
definition against `pointUnit`. The initial retained-packet dry run passed
preflight and compilation (`dc765a309b8`); the corrected packet is validated again
before delivery.
