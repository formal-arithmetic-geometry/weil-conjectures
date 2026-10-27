## Worker report

The module `Sheaf.Paper.RationalPullbackFibreComparison` states
`WeilConjectures.rationalPullbackFibreComparison`. Every theorem in the delivery has
proof `sorry`; all definitions have actual data. The definitions in the item module
name its formulas and its full proposition, rather than introducing a new independent
mathematical notion. No statement correction or disputed statement is needed.

Hypotheses and clauses, checked against the node:

- The finite-field datum is `D : FiniteFieldDatum`; it includes the prime p, positive
  exponent a, q=p^a, the finite field with q elements, and its fixed algebraic closure k.
  `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give the distinct coefficient prime.
  `Ω`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]` give Qbar.
- `X₀ Y₀ : Over (Spec (.of D.k₀))` and `f₀ : X₀ ⟶ Y₀` give a morphism over k₀.
  Each of the two models has `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`
  on its structure morphism: exactly separated finite type, with no properness,
  smoothness, or condition on f₀ added.
- `D.geometricFiber` is the recorded actual base change. `geometricMap D f₀` is
  the underlying arrow of `(Over.pullback ...).map f₀`, rather than an arbitrary map.
  `z` and `x` are the given maps from Spec k; `h : z ≫ geometricMap D f₀ = x`
  is exactly the required equality. `ModelStatement` supplies the already proved
  `sfWeilPrimeInvertible` structures internally, so invertibility is not a new
  hypothesis in the theorem. Point invertibility uses the published
  `frobeniusPointPrimeInvertible`.
- A finite coefficient subfield is the existing `Index l Ω`. Its coefficient field
  is the existing equivalent small model `Coefficient.{u} l Ω F`. Every finite
  subfield is quantified over, including equal fields. The `Shrink.algEquiv`
  in `commonRepresentative` is the existing point-stage coefficient transport.
- `fibre` is `rationalDerivedPullback` along the point followed by
  `pointRationalFibre`, with target `(DerivedCategory.pointFiniteDimensional E)`.
  `Family` quantifies a natural isomorphism for EVERY coefficient field, on the
  full `sfRationalConstructibleCategory`, from pullback followed by J_z to J_x.
- The first clause of `ComparisonStatement` specifies every component by equality
  to `component`. That definition is `pointRationalFibre.mapIso` of the inverse
  `integralComparisonRationalComposition`, followed by `eqToIso` of the given
  point equality. Thus the existential natural isomorphisms are fully pinned.
- `scalar` is the published rational scalar extension, with the auxiliary
  characteristic proof parameter zero, as in the recorded general stage category.
  `scalarComparison` is precisely inverse `pointRationalFibreScalarIso` (beta)
  followed by `pointRationalFibre.mapIso` of
  `integralComparisonRationalScalar` (a_z). No arbitrary b map is assumed.
- The second clause of `ComparisonStatement` is the displayed scalar square:
  in Lean's left-to-right composition it is `b_z ≫ J_z.map a_f ≫ c_G =
  tensor.map c_F ≫ b_x`. This is an equality of derived morphisms, not merely
  an equality on cohomology groups.
- The third clause imposes `scalarUnit` at BOTH z and x, for every finite stage.
  It compares b followed by J of `sfRationalScalarUnit` with
  `DerivedCategory.fieldScalarUnit`, including multiplication/completeness.
- The fourth clause imposes `scalarTower` at BOTH z and x, for every F≤G≤H.
  It explicitly equates successive b maps followed by J of `sfRationalScalarComp`
  with `pointFibreFdTensorTower` followed by the direct b map. These are the
  recorded completion-conjugated scalar and ordinary module tensor associators.
  The square clause holds at every inclusion, so together with these equations
  it includes compatibility of the square for identities and iterated inclusions.
- The final clause supplies a natural isomorphism on the actual published
  common-stage categories. Its component is specified by HEq to
  `commonRepresentative`, namely the finite-stage c map after the existing Shrink
  coefficient transport and `pointFdQbarStage`. HEq accommodates the published
  functors' propositionally fixed object formulas. A morphism in `PointFdQbar`
  is, by definition, a derived morphism of Ω-modules; its components are therefore
  Ω-linear. The natural isomorphism is on the actual quotient category, ensuring
  independence of representatives, including arrows originally over different fields.
- All object binders range over the full constructible categories. There is no
  Weil structure, lattice, perfectness, Tor-amplitude, or finite-reduction bound.
  The existential C is constrained by all the existing realization coherences
  simultaneously; it is construction data supplied in the conclusion, not an
  additional input hypothesis. Its maps are the published quotient/counit formulas.

Dependency declarations used:

- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStageDerivedPullback` and their prescribed object and map interfaces.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`,
  `pointRationalFibreScalarIso`, `pointQbarFibre`, `pointFibreFdTensorTower`.
  Their full signatures and source docstrings were read, including the small/large
  module transport and the explicit common-stage representative conjugations.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory` and its finite-stage system,
  actual pairs, Hom quotient and normalized transition/associator declarations.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `IntegralComparisonSystem`, `IntegralComparisonRealizationCoherence`,
  `integralComparisonComposition`, `integralComparisonScalar`, and the original
  realization theorem. The dependency module of this delivery imports all of them.
- `Sheaf.Paper.PointSectionsScalarExtension`: the canonical rational sections
  comparison and `pointSectionsScalarExtension`, including all six naturality,
  identity, and tower clauses. These are the comparisons used in the definition
  and normalization of `pointRationalFibreScalarIso`.
- Added existing dependency `def-trf-realized-pullback-comparisons`, module
  `Sheaf.Paper.RealizedPullbackComparisons`: actual
  `integralComparisonRationalComposition` and `integralComparisonRationalScalar`.
  This landed owning node was found during the search, avoiding duplicate maps.
- Added existing dependency `lem-weil-scalar-extension-composition`, module
  `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarUnit` and
  `sfRationalScalarComp`, with their actual completed tensor normalizations.
- Added existing dependency `def-weil-finite-field-fiber`, module
  `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`.
  `sfWeilPrimeInvertible` from `SfWeilSheafComplex` and
  `frobeniusPointPrimeInvertible` from `FrobeniusPointTransport` supply their
  proved residue-field invertibility consequences; no Weil object is used.

Source: opened the current `literature/blueprint/latest/.../
lem-fd-realified-kernel-real.proof.md`, Step 2, including the point over p_1(z)
and its local fibre pullback. Read the item's full five-step proof and all five
original statement dependencies. The dependencies' `blueprint_update` records
announce future condensed replacements; this item explicitly states the existing
raw rational and common-stage assertion, and uses those recorded constructions.

Edge cases: f₀ the identity; z=x and the explicit composition equality; repeated
fields F=G or G=H, including the triple identity; zero complex; empty model (the
point premise then has no witness); non-perfect finite reductions; arrows whose
source and target have different finite stages. No empty-index argument or
characteristic equality is hidden in a universe choice. All universes and variables
are explicit, with `autoImplicit false`. The project point-fibre API uses one
universe for the scheme datum and Ω; this is a common size choice for these sets,
not an equality between pro-etale object and morphism universes, which are retained.

Searches performed with `msearch.py NJ lem-fd-rational-pullback-fibre-comparison`:

- LeanFinder: "Canonical scalar compatible rational derived geometric point fibre
  comparison of pullback constructible ell adic complexes": eight affine-transition
  and scheme-residue-field fibre hits; no exact derived coefficient comparison.
- Loogle: `"stalk", "pullback"`: twelve `TopCat.Presheaf` stalk maps and identities;
  ordinary topological stalks do not give this rational/common-stage statement.
- grep: `stalkPullbackIso|rationalPullbackFibre|pointRationalFibre`: only Mathlib's
  `Topology/Sheaves/Stalks.lean:335`, no match to the full statement.
- LeanSearch: "Canonical derived pullback geometric fibre natural isomorphism with
  coefficient extension coherence": eight categorical descent, sheaf pullback,
  fibered-category, and scheme fibre hits; no exact match.
- `rg` in `lean/WeilConjectures` for rational/fibre/scalar and pullback/fibre found
  ordinary lisse rank, topological stalk and unrelated algebraic fibre statements.
  `grep -rn lem-fd-rational-pullback-fibre-comparison lean/WeilConjectures` found none.
- `rg` in `lean/Sheaf/Paper` found the useful existing rationalized comparison
  definitions in `RealizedPullbackComparisons`, and the point and common-stage
  constructions reused here. `RationalFibreScalarComparison` concerns lisse heart
  fibres and paths, not derived constructible pullback and quotient descent.
- `tools/blueprint_refs.py search 'rational pullback fibre comparison'`: zero
  blueprint nodes match; DAG searches found the existing realized-comparisons
  owning node cited above. No new definition node is introduced.

## Dependency modules

`lem-trf-integral-pullback-comparison-realization` is repaired by
`Sheaf.Paper.SimultaneousIntegralPullbackComparisons`. The original theorem fixes E,
L and iota before `∃ D`, so it cannot furnish a single family coherent across ALL
coefficient inclusions. The node expressly states simultaneous families, arbitrary
finite iterations and tower laws. The added theorem
`integralPullbackComparisonRealization_simultaneous` places `∃ C` before the
coefficient quantifiers and uses exactly the existing
`IntegralComparisonRealizationCoherence`. Its docstring explains the entire
source proof with the same actual quotient diagrams, derived-limit counit,
K-flat/K-injective constructions, eta/lambda/mu, completeness, mixed equation,
and chi-conjugated scalar associator. The module publicly imports the original,
retaining all previous declarations. Only this dependency's `lean` field changes,
with the required explanatory note; no dependency statement or construction changes.

## Second reading by NJ

The dispatcher explicitly prohibits starting other agents. This is a second pass by
the same worker, not a claim of an independent reviewer; the maintainer's independent
review follows delivery. I re-opened the node and compared every binder and each
conclusion against `ComparisonStatement`, `ModelStatement` and the final theorem.
The finite-type and separated assumptions are on both models' structure maps;
f₀ is over k₀; f is its actual base change; the point equality has the correct
composition direction. The component is the INVERSE compositor. The scalar square
has b first and c last on the left, tensor(c) then b on the right, exactly reversing
the printed right-to-left mathematical order. Both point comparisons, rather than
only z, carry the identity and full three-field tower conditions. The common-stage
component includes the recorded Shrink-to-subfield transport. The final natural
isomorphism lives in the quotient category itself, with module-linear components.
The original comparison-system quantifier defect was found and repaired in the
dependency module rather than concealed by a strong hypothesis on C. No mathematical
statement was changed; no theorem was proved. Compilation and preflight results
are recorded below after execution.

Validation: `scompile.py NJ lem-fd-rational-pullback-fibre-comparison` accepted BOTH
modules separately, in dependency order, in the sandbox and under their library names.
The final compiler output contained no errors and no unexpected warnings. The only
elaboration repair needed was replacing the anonymous `.ofHom` in the base-change
map by the explicit `CommRingCat.ofHom`; the mathematical construction is unchanged.
The required `deliver2.py ... --no-push` printed `OK (dry run)` and confirmed that
commit `3d4e4e86666` passes preflight and compiles. All checks used the prescribed
wrappers and their default limits; no global build or direct repository mutation ran.
