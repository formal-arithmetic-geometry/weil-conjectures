## Worker report

The module `Sheaf.Paper.IntegralReductionTowerWellDefined` states
`WeilConjectures.integralReductionTowerWellDefined`. Its proof is `sorry`.
It also supplies the canonical chain maps needed to state the two equations,
together with the canonical localization transports. No proof of either equation
is attempted.

Hypothesis-by-hypothesis correspondence:

- The coefficient prime is `l : ℕ` with `[Fact l.Prime]`. The finite extension is
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]`. `D : FiniteFieldDatum` and `hl : l ≠ D.p`
  express the characteristic convention of the completed-coefficient dependency.
  The chosen valuation-ring uniformizer and quotient rings are those already
  used by `Padic.coefficientExtensionRing` through the coefficient-sheaf module;
  they are not redefined.
- `Y : AlgebraicGeometry.Scheme.{t}` is unrestricted. The actual small pro-etale
  site is `Scheme.ProEt.topology Y`, with object universe `t+1` and morphism
  universe `t`. Coefficients and module sections have universe `max u (t+1)`;
  no equality of site universes is imposed.
- The completed ring, finite ring sheaves, projections and reduction maps are
  `completedIntegralCommRingSheaf`, `integralCoefficientCommRingSheaf`,
  `completedIntegralCommRingProjection`, and `integralCoefficientSheafTransition`.
  Their underlying ring sheaves are the dependency's original ring sheaves.
- `K` is the chosen complex representative, and `P`, `P'` are complexes over
  `completedIntegralModuleSheaves`. The maps `q : P ⟶ K`, `q' : P' ⟶ K`, with
  `hq`, `hq' : CochainComplex.IsKFlatResolution ...`, say exactly that the sources
  are K-flat and their augmentations are quasi-isomorphisms. No flat-term,
  boundedness, surjectivity or direct comparison-map assumption is added.
- `integralTowerFiniteComplex n P` is the recorded ordinary change-of-rings
  functor applied termwise. `integralTowerComplex n P` restricts it termwise to
  completed coefficients. Thus these are exactly `P_n` with each of its scalar
  actions. The index `n : ℕ` denotes the paper's positive exponent `n+1`.
- `integralTowerTensorSection` is a genuine construction: take the pure tensor,
  apply the abelian-sheafification unit, and transport along the defining object
  equality of the recorded ordinary change-of-rings functor. It introduces no
  arbitrary tensor product or coefficient sheaf.
- `integralTowerUnitCondition` specifies every degree and every local section by
  `x ↦ 1 ⊗ x` after sheafification (the extension-of-scalars convention places
  the coefficient first). `integralTowerTransitionCondition` specifies every
  sheafified pure tensor by `s ⊗ x ↦ ρ_n(s) ⊗ x`.
  `integralTowerMaps_existUnique` states the existence and uniqueness implicit
  in the node's phrase "the resulting morphisms of complexes". Its docstring
  gives the full presheaf, balancing, sheafification and differential argument.
  `integralTowerUnit` and `integralTowerTransition` choose from this unique pair.
  This is choice from a theorem determining the maps up to equality; neither
  definition has sorry data or makes a choice from mere unconstrained existence.
- `integralTowerResolutionIso` uses the landed
  `integralDerivedReductionResolutionIso` and the standard homotopy/complex
  quotient comparisons. `integralTowerFiniteComparison` is its inverse for q
  followed by its value for q'. It is exactly the canonical `θ_n`, through the
  common derived reduction of K, rather than an arbitrary finite isomorphism.
- `integralTowerComparison` applies the derived restriction of scalars
  `(completedIntegralRestrictScalars ... n).mapDerivedCategory` to this finite
  comparison. Its endpoints are transported by `mapDerivedCategoryFactors` to
  the actual restricted complexes. The limits/colimits instances come from
  `completedIntegralRestrictScalars_exact`; the additive instance is Mathlib's
  restriction-of-scalars additive instance. This uses the mathlib_match of
  `def-weil-integral-derived-restriction-of-scalars` directly.

Conclusion-by-conclusion correspondence:

1. The first conjunct, for every level n, is `[q]⁻¹ ≫ [γ_n] ≫ Res(θ_n) =
   [q']⁻¹ ≫ [γ'_n]`. The inverse is the inverse of
   `integralTowerAugmentationIso`, the `asIso` of the localized augmentation.
   Lean writes composition in the reverse textual order from the TeX.
2. The second conjunct is `[τ_n] ≫ Res(θ_n) = Res(θ_(n+1)) ≫ [τ'_n]`, with
   the same canonical restricted comparisons as in clause (1).
3. Each comparison is an `Iso`, not just an invertible-looking arrow.
   Clause (2) is exactly the naturality condition for their components on the
   inverse systems (successive arrows generate the natural-number inverse
   diagram); the inverse naturality follows by cancellation. Clause (1) says
   that this isomorphism respects the maps from K. Thus the "So" paragraph is
   encoded by the two equations and the `Iso`-typed components, without a new
   inverse-system definition.

Dependency declarations used:

- `Sheaf.Paper.CompletedIntegralCoefficients`: the completed and finite coefficient
  sheaves, commutative refinements, projections, reduction maps, module category,
  and ordinary restriction functor.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatResolution` and its
  `IsKFlat` constituent, on the same commutative ring sheaf.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses` (and its
  public `TensorProduct` dependency): `SheafOfModules.changeOfRingsPresheaf`.
- `Sheaf.Paper.IntegralDerivedReduction`: `integralReductionExistence`,
  `integralReductionChangeOfRings`, `integralDerivedReduction`, and
  `integralDerivedReductionResolutionIso`. This landed node is added to the
  item's statement dependencies, as the standing rule permits.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`.
- `Sheaf.Paper.RestrictionOfScalarsExact`:
  `completedIntegralRestrictScalars_exact`.
- Proof-plan imports include the recorded K-flat resolution, resolving-class
  derived-functor and saturated quasi-isomorphism modules. Their declarations
  and docstrings were read; the theorem docstring follows all four DAG proof
  steps, including the common homotopy roof and the two tensor squares.

Edge cases checked: level n=0 is exponent one, so the zero-exponent quotient is
never inserted; all positive levels occur. Complexes may be zero or unbounded,
Y may be empty, and the augmentation may be the identity. No nonemptiness or
connectedness assumption enters. The sectionwise map characterization remains
valid on the empty site object, because it uses sheafification rather than a
surjectivity claim on global sections. There is no independent smaller universe
for test objects, and no assumption identifying site object/morphism universes.

Searches: `msearch.py leanfinder` for "canonical K flat resolution comparison
commutes with quotient reduction and tensor unit" returned eight flat-module and
classical adic-completion results, none the augmented tower assertion.
`msearch.py loogle` for `Functor.mapDerivedCategory, NatTrans, IsIso` returned
zero hits (unknown identifier in the remote index). `msearch.py grep` for
`reductionTower|derivedChangeOfRings` in `Algebra/Homology` returned zero hits.
LeanSearch for "canonical comparison K flat resolutions derived tensor quotient
reduction natural unit" was unavailable (Internal Server Error), recorded by
the tool. Direct `rg` of Mathlib's homology, upstream WeilConjectures, the
project's Sheaf files and `dag/lean_names_upstream.json` found no existing
augmented-tower comparison or collision with the new declaration names. A direct
upstream search for the node id found no declaration. Existing derived-reduction
and scalar-restriction constructions were reused instead of copied.

No statement correction and no STATEMENT-DISPUTED flag. The node's inherited
source.document calls 06YL/06YV sites-modules.tex; these sections actually belong
to sites-cohomology.tex, as its proof steps and split_report already note. The
module cites the correct source; no maintainer-owned source field is edited.

## Dependency modules

`def-pc-kflat-complex`: the compile wrapper initially resolved the older live
`KFlat` artifact, whose universe is fixed to the maximum of site object and
morphism universes. Compiling `KFlatResolutionIndependentCoefficients` then failed
with a module-universe mismatch and a missing monoidal-localization instance.
The delivery supplies the currently published generalized `KFlat.lean`
from this group's read-only checkout in its sibling overlay, preserving its
independent coefficient universe and all declarations, and explicitly documents
that size convention in the IsKFlat docstring. Only its node's `lean`
record is updated, with an explicit note. This is the same §1(B) overlay repair
already documented in the dependency record, not a second K-flat notion.
The file compiled in 2.2 seconds. It retains the dependency's full source and
proof docstrings and real monoidal/sheafification constructions.

## Validation

The substantive module and sibling dependency compiled through `scompile.py`.
The first successful pass reported two long-line warnings; both lines were
wrapped before the final compile/dry run. The dry run printed
`OK (dry run): commit d171d3c5d2 passes the preflight and compiles; nothing pushed`.

## Earlier second reading (a previous round; superseded)

Pending independent second reading. This is the author's prescribed `--no-push`
dry run, not a second-reader review. The separate reader must inspect the complete
node, both modules, the canonical-map characterizations, and the clause matching
above before delivering. Nothing has been pushed by this worker.

## Second reading by NC

I reread the node statement, all six statement dependencies, and both delivered modules. The
objects and hypotheses render as follows. The binders `l`, `[Fact l.Prime]`, `E`, `[Field E]`,
`[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`, `Y`, `D`, and `hl : l ≠ D.p` instantiate
the node's fixed prime, finite extension, scheme, and the global finite-field datum required by
the completed coefficient dependency. `completedIntegralCommRingSheaf`,
`integralCoefficientCommRingSheaf`, `completedIntegralCommRingProjection`, and
`integralCoefficientSheafTransition` render the completed sheaf, finite quotients,
projections, and reductions. `P`, `P'`, `K`, `q`, `q'`, and the two
`IsKFlatResolution` hypotheses render the chosen representative and K-flat
quasi-isomorphisms. `integralTowerFiniteComplex` and `integralTowerComplex` render
termwise change of rings and restriction of scalars; `integralTowerUnit` and
`integralTowerTransition` render the maps x ↦ x⊗1 and id⊗ρ, with their formulas fixed by
`integralTowerMaps_existUnique`. `integralTowerComparison` is the restriction of the
canonical K-flat comparison, and `integralTowerAugmentationIso` is the localized
augmentation isomorphism. The first conjunct is exactly compatibility with the maps from
K, and the second is exactly compatibility with every transition; the displayed `Iso`
components encode the final inverse-system isomorphism.

The Lean uses `n : ℕ` as the zero-based index for exponent `n+1`, matching the source's
positive levels (so `n=0` is exponent one); this is an explicit harmless reindexing and does
not add a zero-exponent case. Zero complexes, the empty scheme/site, identity augmentations,
unbounded complexes, and all universe sizes remain admissible. No connectedness,
nonemptiness, boundedness, surjectivity, or characteristic assumption beyond the fixed
finite-field datum and `l ≠ D.p` is introduced.

I searched Mathlib, the upstream WeilConjectures checkout, project `lean/Sheaf`,
and `dag/lean_names_upstream.json` with grep, LeanFinder/Loogle, and msearch.py queries for
K-flat reduction towers, derived change-of-rings comparison, and reduction-tower maps. No
existing declaration states this theorem or its canonical tower notion. The recorded
`integralDerivedReduction` dependency is cited and its canonical resolution isomorphism is
used directly. The K-flat dependency module is the authorized independent-universe repair;
it states the same K-flat and K-flat-resolution notions with the relative smallness
convention, and its node record explains why the old interface was unusable.

No mismatch was found between the node's two clauses and the theorem signature, and no
statement or definition was changed. The only presentational difference is the documented
zero-based index convention. The theorem and sibling K-flat module compile through the
prescribed wrapper; the delivery dry run was run after the report update.
