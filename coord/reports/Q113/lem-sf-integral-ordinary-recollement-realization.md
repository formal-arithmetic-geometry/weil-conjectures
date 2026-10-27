## Worker report

The module states `sfIntegralOrdinaryRecollement_realization`, with `sorry`, and supplies
real helper constructions for its comparison record and the ordinary completed-ring
operations. The two records package conclusions, not hypotheses. The theorem asserts
`Nonempty (SfIntegralOrdinaryRecollement l E i j)`; no comparison, adjunction,
constructibility, completion, or cohomological bound is assumed as input.

Hypotheses and objects:

- `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]` give the prime and finite extension. The imported
  `Padic.coefficientExtensionIntegers`, chosen uniformizer and quotient rings are
  precisely the dependency's coefficient datum. Index `n : ℕ` means exponent `n+1`;
  no exponent zero is substituted for the first quotient.
- `k : Type u`, `[Field k]`, `_hl : IsUnit (l : k)` give the base and invertibility.
- `aX : X ⟶ Spec (.of k)` with `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`
  is separated finite type over k. There is no finite-field or algebraic-closedness
  hypothesis. `i`, `IsClosedImmersion i`, `j`, `IsOpenImmersion j` and `_hU` identify
  the closed subscheme and its complementary open, including empty pieces.
- `scalarReductionSource l E T` is the module category over the actual inverse-limit
  coefficient sheaf on the small pro-etale site, and `scalarReductionDerivedExtension`
  takes values in the actual finite coefficient category. The site object universe is
  u+1 and its morphism universe u; it is not collapsed to an equal-universe site.
  A common universe u for field/scheme/coefficient data is the project's size convention
  (any collection of these data can be placed in one larger universe).

Clauses, in the node's order:

1. Ordinary pullback is `sfOrdinaryModulePull`, Mathlib's left adjoint to the published
   `sfCompletedModuleDirectImage`. Its exact immersion descent is `sfOrdinaryDerivedPull`.
   `SfOrdinaryIntegralComparison.pull` compares this with the existing
   `integralDerivedPullback`; `pull_complete` asserts invertibility on every
   `IsSfDerivedComplete` input, with no constructibility restriction there.
2. `pull_model` fixes the comparison on every flat-term K-flat representative. The
   projection coordinate is transposed through the actual ordinary adjunction and equals
   `sfOrdinaryPullAugmentationLeg`: reduction unit, finite inverse-image unit and the
   published identity-on-sections scalar square. The other Roos coordinate is zero.
   Thus the comparison is the actual augmented strict-tower construction, not an
   arbitrary natural transformation or an isomorphism of its endpoints.
3. `push K hK L` is the ordinary-to-integral direct-image isomorphism for every chosen
   `SfIntegralDirectImage` Roos presentation L. `push_projection` fixes every finite
   projection as ordinary image of the quotient unit followed by the canonical
   `sfDerivedRestrictionComparison`. `push_reduction` says the specified finite adjunct
   is invertible and its conjugate is `sfOrdinaryPushReduction` in the finite category.
4. `pull_reduction` makes the already-defined `integralPullbackFiniteComparison`
   invertible for every good representative and every identification with K. Its target
   `integralPullbackFiniteComplex` computes the finite exact inverse image of K_n, so
   this is the requested `(u_comp^* K)_n ≅ u_n^* K_n` in finite modules.
5. `diagrams` reuses `CompletedCoefficientPushforward.ComparisonData`, rather than
   creating a private substitute. Its inherited `quotientSquare`, `quotientCoherence`,
   `projectionCoherence`, `diagramSquare`, `towerEvaluation`, `limitComparison`,
   `limitNormalization`, and `limitProjection` retain the comparison before evaluation,
   every quotient transition, the universal derived units, and finite projections.
   Its `reconstruction` asserts invertibility of the normalized reconstruction composite
   on complete objects. `diagrams_structure` fixes the actual completed structural map;
   `diagrams_model` and `diagrams_unit` identify its ordinary derived model and universal
   cochain unit with the specified sfCompletedDerivedDirectImage. This uses the published
   coherent strict interface; no inference from equality after evaluation is assumed.
6. `pull_preserves_complete`, `push_constructible`, `pull_constructible` say preservation
   for ordinary and specified completed pullbacks and direct images. The exact predicate
   `sfIntegralConstructible` is completeness plus constructibility of every finite reduction
   and one interval `∃ a b, a ≤ b ∧ ∀ n, support ⊆ Icc a b`. Each image's interval is
   therefore uniform in n. `pull_interval` also retains the input interval for ordinary
   exact inverse image. The isomorphism `push` identifies the same predicate for the
   integral direct image. No finite-Tor category is substituted.
7. `sfOrdinaryClosedKernel` is the actual kernel of the open sheaf adjunction unit,
   followed by closed inverse image, precisely the completed-coefficient transport of
   `ringedClosedKernelShriek`. `sfOrdinaryClosedShriek` is its total right derived functor,
   not an arbitrarily chosen right adjoint. `kernelAdjunction`, `kernel_counit` and
   `ambient_counit` fix the underived support inclusion and its derived counit on every
   K-injective representative. `ambientAdjunction` is the ambient adjunction.
8. `shriek_constructible` gives its restriction to the precise integral subcategory;
   `sfOrdinaryConstructibleShriek` is the literal full-subcategory lift. Its
   `restrictedAdjunction`, `restricted_unit` and `restricted_counit` retain the ambient maps.
9. `supported_triangle` uses `Triangle.mk (ambientAdjunction.counit.app K)
   ((sfOrdinaryDerivedAdjunction ... j).unit.app K) δ ∈ distTriang _` and asserts
   constructibility of the two non-input vertices. Under the normalized pullback and
   direct-image comparisons, these are exactly the specified integral operations and maps.
10. `closed_unit` and `open_unit` assert that the actual counits for i^* i_* and j^* Rj_*
    are invertible. `disjoint` is `IsZero (j^* (i_*P))`. `orthogonal` uses `Subsingleton`
    of the actual Hom group `(i_*P)⟦m⟧ ⟶ Rj_*G` for every integer m.
11. `shriek_linear` concerns the literal restricted functor and the imported constant-section
    R-action. `closed_shift_normalization` pins closed pushforward's shifts to ambient
    derived pushforward, including both full-subcategory inclusions. `shriek_shift_adjunction`
    is `Adjunction.CommShift` for the restricted adjunction. `shriek_exact` preserves
    distinguished triangles with precisely that shift. This is the adjunction-induced
    structure, not an unconstrained shift structure. Additivity follows from the adjunction
    with additive closed pushforward; exactness is stated with its full triangle maps.
12. `conservative` states invertibility of every integral morphism when all its actual
    `scalarReductionDerivedExtension` maps are invertible, for every T (thus X,Z,U).
13. All ambient categories here are completed-ring modules. The diagram interface may
    compare exact restrictions to constant scalars, but no equivalence between the two
    ambient categories is stated.

The five preparatory sorry theorems concern right adjoint existence, additivity of
ordinary inverse image, its exactness for immersions and finite-colimit preservation,
and additivity of the support kernel. They are named subclaims of this node's ordinary
operations and carry source references and complete construction arguments. Every
other helper has real data. The main theorem carries all thirteen proof steps.

Dependency declarations used (module → names):

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` → `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: `None` → `None`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible` → `WeilConjectures.sfIntegralConstructible`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` → `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom` → `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage` → `WeilConjectures.SfIntegralDirectImage`.
- `lem-sf-ringed-closed-kernel-adjoint`: `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint` → `AlgebraicGeometry.Scheme.proEtale_ringed_closed_kernel_adjoint`.
- `def-weil-derived-complete`: `Sheaf.Paper.DerivedCompleteOnSlices` → `WeilConjectures.IntegralOnSlice.IsComplete`.
- `def-weil-integral-derived-reduction`: `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` → `WeilConjectures.scalarReductionDerivedExtension`.
- `def-pur-completed-pushforward-models`: `Sheaf.Paper.CompletedCoefficientPushforwardModels` → `WeilConjectures.CompletedCoefficientPushforward.ComparisonData`.
- `def-derived-cochain-right-unit`: `Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares` → `CategoryTheory.derivedCochainRightUnit`.
- `def-sf-integral-constructible-linear-structure`: `Sheaf.Paper.SfIntegralConstructibleLinear` → `WeilConjectures.sfIntegralConstructibleLinear`.
- `def-sf-scalar-reduction-categories-restriction`: `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` → `WeilConjectures.scalarReductionRestriction`.
- `def-a1-flat-term-kflat-complex`: `Sheaf.Paper.IntegralOperationsWellDefined` → `WeilConjectures.integralOperationsGoodComplex`.
- `def-pur-integral-derived-operations`: `Sheaf.Paper.IntegralDerivedOperationsOnSlices` → `WeilConjectures.IntegralOnSlice.completedTensor`.
- `def-weil-integral-reduction-tower`: `Sheaf.Paper.IntegralReductionTowerCanonical` → `WeilConjectures.canonicalIntegralReductionTower`.

The aggregation node def-weil-scheme-morphism-properties intentionally fixes no new
notion and has no declaration: its individual Mathlib properties are used directly.
The remaining proof dependencies' recorded modules are imported plainly; Mathlib leaves
use their exact derived, shift, adjunction, homology and Noetherian APIs. No dependency
record was repaired or replaced.

Edge cases checked: zero input; zero maps; exponent one (n=0); identity quotient
transitions; empty X, empty Z, empty U; nonreduced closed subschemes; arbitrary base
field including infinite fields; arbitrary cohomological intervals including a=b;
all integer shifts. No extra boundedness of the ambient kernel adjoint is imposed.
The Roos data quantifies over all presentations, rather than assuming a functorial cone.
Uniformity is the shared interval within sfIntegralConstructible, not a separate interval
chosen at each finite level. No disputed statement or source correction was found.

Searches for reuse:

- msearch leanfinder, `Ordinary completed ring sheaf recollement realizes integral derived
  pullback direct image and closed kernel adjoint`: 8 generic module pushforward/adjunction
  hits, including SheafOfModules.PullbackConstruction.adjunction and
  SheafOfModules.pullbackPushforwardAdjunction; no full recollement comparison.
- msearch loogle, `CategoryTheory.Adjunction, CategoryTheory.Functor.IsRightAdjoint`:
  generic adjunction constructors, including Functor.IsRightAdjoint.mk' and module-sheaf
  pullbackPushforwardAdjunction; no matching theorem. These provide the ordinary API.
- msearch grep, `recollement|Recollement`, Mathlib CategoryTheory: 0 hits.
- msearch leansearch, `Derived complete integral sheaves ordinary recollement pullback
  direct image comparison`: eight component module-sheaf pullback/adjunction results;
  no matching theorem.
- rg of lean/WeilConjectures and lean/Sheaf for the item id and
  `sfIntegralOrdinaryRecollement|SfOrdinaryIntegralComparison`: no existing declaration.
- Read the full signatures/docstrings of SfIntegralConstructible, SfDerivedDirectImage,
  DerivedPullbackTensorHom (including its imported IntegralDerivedOperations),
  ProEtaleRingedClosedKernelAdjoint, DerivedCompleteOnSlices,
  DerivedScalarExtensionRestrictionAdjunction, and the coefficient interfaces.
  The original CompactObject example is currently withdrawn and has no declarations;
  the delivered module follows the current module/public-section convention instead.

Validation: all compiler calls use the prescribed scompile.py. The final delivered
module compiles in module mode under its own path and sandbox path with no diagnostics.
Development trace/profiler options were removed. The structure generation options avoid
expensive automatically generated auxiliary declarations without changing the statement.
No local instance, private definition, local notation, hidden let, or auto-bound variable
is used in the delivered statement. All extra statement-dependency ids are already-landed
notion owners, added because the public signature uses their exact declarations.

## Second reading by Q113

A separate manual pass reopened the node and the full delivered module. No separate
agent was started, as the dispatcher explicitly forbids it; independent maintainer
review is the subsequent stage. This pass found and repaired three concrete defects
in the inherited draft: strict coefficient coherence was only described in prose
(now ComparisonData plus the fixed structural map and universal-unit model equation),
linearity/exactness concerned only the ambient shriek (now the literal restricted
functor, restricted adjunction, and its actual unit/counit), and the closed shift was
unconstrained (now closed_shift_normalization pins it to the ambient derived shift).
The pass matched each field with the numbered clause mapping above and checked the
ordinary counit normalization, quotient indices, uniform interval, empty complements,
and the absence of a finite-Tor or finite-field assumption. No node statement changes,
new notions, dependency-module changes or unresolved statement disputes remain.
