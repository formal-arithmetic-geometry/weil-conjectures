## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFlatDualizingPolynomialModel` states
`AlgebraicGeometry.exists_properFlatDualizingPolynomialModel`. Its only theorem has
`by sorry`; there are no new definitions or helper theorems. The node statement and
proof are unchanged. The full eight-step node proof, including its uses, is in the
theorem docstring. The source was read directly in the local Stacks source:
`duality.tex`, labels `lemma-existence-relative-dualizing` (0E2X),
`remark-relative-dualizing-complex-bis` (0E4P),
`remark-local-calculation-shriek` (0BV2), and `dualizing.tex`,
`lemma-well-defined` (0BZJ), including its preceding top-forms footnote.
The Noetherian setting of 0BV2 alone is not used to restrict this theorem.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Any schemes X and S and morphism f | `{X S : Scheme.{u}} (f : X ⟶ S)`; neither scheme has a compactness, quasi-separatedness or Noetherian binder |
| Proper | `[IsProper f]` |
| Flat | `[Flat f]` |
| Finite presentation | `[LocallyOfFinitePresentation f]`; properness already implies quasi-compactness and separatedness, hence quasi-separatedness |
| Unbounded D_QCoh | `schemeDerivedQCohCategory X` and `schemeDerivedQCohCategory S`, the recorded full subcategories of the unbounded `DerivedCategory` |
| Rf_* on those categories | Existential `hpres` and the actual `ObjectProperty.lift` of `(schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f`; no arbitrary pushforward functor |
| Right adjoint f^! | Existential `fshriek` and `Nonempty (actualLift ⊣ fshriek)` |
| O_S in D_QCoh | Existential proof `hO : schemeDerivedQCohProperty S (𝟙_ (schemeDerivedCategory S))`; this is a conclusion, never an extra hypothesis |
| Put K_f = f^! O_S | `K : schemeDerivedQCohCategory X` together with `K = fshriek.obj ⟨𝟙_ (schemeDerivedCategory S), hO⟩` |
| Intrinsic coherent relative dualizing pair | Existential diagonal class `ξ` with exactly the recorded domain and pullback codomain, and `IsCoherentRelativeDualizingPair f K.obj ξ` |
| All affine opens V = Spec R and U = Spec B above V | Universal R, B, their ring and algebra structures, `jB`, `jR`, both open-immersion instances, and the equality `jB ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jR` |
| Interpret K restricted to U by affine derived equivalence | `M : DerivedCategory (ModuleCat B)` and `e : (polynomialOpenRestriction jB).obj K.obj ≅ (polynomialAffineTilde B).obj M`; exact native derived tilde is the recorded affine equivalence's forward realization |
| Every chosen polynomial presentation P surjecting onto B | `F : PolynomialDualityPresentationSystem R B (algebraMap R B) M`; its `identification` quantifies over every n and ring map p, its surjectivity and scalar equality, and supplies `M ≅ polynomialDualityModel n p` |
| RHom_P(B, Omega^n)[n] in D(B) | `polynomialDualityModel` is the recorded `derivedCoinduction p` of `polynomialDualityCoefficient R n`; the latter is the degree-zero `polynomialDualityTop` shifted by n; exact derived coinduction commutes with shift |
| Omega^n is the nth exterior power of Kahler differentials | `polynomialDualityTop` uses Mathlib `exteriorPower` of `KaehlerDifferential R (MvPolynomial (Fin n) R)` |
| Natural B action (b h)(b') = h(b'b) | `ModuleCat.derivedCoinduction` derives actual `coextendScalars p`; `coinductionComplexFunctor` computes precisely the degreewise Hom with this action, as its recorded docstring and implementation specify |
| Commutativity with affine-open restriction | One global `atlas : PolynomialDualityChartAtlas f K.obj`, its independent canonical restriction square, and both `IsPolynomialAffineAtlasCompatible atlas ... e F` and `IsPolynomialLocalizedAffineAtlasCompatible atlas ... e F`; these equate affine identifications with that same atlas using evaluation and original derived units |
| Polynomial refinement and adjoining t mapped to a | The presentation system's `refinement` equation uses `polynomialDualityRefinement R n g`, with g any chosen lift; it equates its transition to the two-evaluation-counit `polynomialDualityRefinementMap` |
| Ordered dual(t-a) tensor d(t-a) goes to 1 | `IsPolynomialDualityContraction` fixes the inverse coefficient map to the shifted boundary of the actual short exact equation sequence; the quotient sends the new ordered volume to the old one |
| Repeated refinements, exterior and cohomological signs | Iteration of those boundary-normalized maps and the `coordinate` field, whose `IsPolynomialDualityCoordinateComparison` is fixed on all wedges of universal derivatives; shift and exterior maps are the standard native ones |
| Composition cocycle | `F.comparison p q` is `(F.identification p).symm ≪≫ F.identification q`; intermediate identifications cancel. Global restriction squares share K and the native restriction composition, and compatibility identifies the concrete arrows with these transitions |
| Same intrinsic object for all models | Every atlas and every affine e uses this one `K.obj`, with its displayed equality to the value of fshriek |
| No Noetherian, CM, lci or dimension condition; no concentration or invertibility assertion | None occurs in the hypotheses or conclusion; K is a general derived object and no line-bundle or single-degree predicate is asserted |

The `HasDerivedCategory` binders only specify localization universes for ringed-space
module categories and over-open module categories, following the existing atlas and
pair interfaces. They impose no geometric hypothesis and no equality of site object
and morphism universes. Every universe and variable is explicitly bound;
`autoImplicit false` is set. Module-valued polynomial models use their existing
standard derived categories, rather than creating a second model carrier.

Dependency declarations read and used (including their signatures and docstrings):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme` — `AlgebraicGeometry.Scheme`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper` — `AlgebraicGeometry.IsProper`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat` — `AlgebraicGeometry.Flat`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` — `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-pc-derived-category`: `WeilConjectures.AlgebraicGeometry.DerivedCategory` — `AlgebraicGeometry.schemeDerivedCategory`.
- `def-pc-derived-direct-image`: `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage` — `AlgebraicGeometry.schemeDerivedDirectImage`.
- `def-trf-coherent-relative-dualizing-pair`: `Sheaf.AlgebraicGeometry.RelativeDualizingPair` — `AlgebraicGeometry.IsCoherentRelativeDualizingPair`.
- `lem-pc-affine-qcoh-derived-equivalence`: `WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence` — `AlgebraicGeometry.exists_affineQCohDerivedEquivalence`.
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic` — `KaehlerDifferential`.
- `def-weil-pbc-exterior-algebra`: `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic` — `ExteriorAlgebra`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` — `CategoryTheory.ordinaryModuleDerivedInternalHom`.
- `def-trf-derived-coinduction`: `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction` — `ModuleCat.derivedCoinduction`.
- `def-pc-scheme-derived-tensor-structure`: `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure` — `AlgebraicGeometry.schemeDerivedTensorMonoidal`.
- `def-trf-polynomial-duality-presentation-data`: `Sheaf.AlgebraicGeometry.PolynomialDualityPresentationData` — `AlgebraicGeometry.PolynomialDualityPresentationSystem`.
- `def-trf-polynomial-duality-restriction-primitives`: `Sheaf.AlgebraicGeometry.PolynomialDualityRestrictionPrimitives` — `AlgebraicGeometry.polynomialCoinductionRestriction`.
- `def-trf-polynomial-duality-restriction-atlas`: `Sheaf.AlgebraicGeometry.PolynomialDualityRestrictionAtlas` — `AlgebraicGeometry.PolynomialDualityChartAtlas`.
- `def-trf-polynomial-duality-affine-realization`: `Sheaf.AlgebraicGeometry.PolynomialDualityAffineRealization` — `AlgebraicGeometry.IsPolynomialDerivedImageComparison`.
- `def-trf-polynomial-duality-affine-compatibility`: `Sheaf.AlgebraicGeometry.PolynomialDualityAffineCompatibility` — `AlgebraicGeometry.IsPolynomialLocalizedAffineAtlasCompatible`.

The five polynomial definition nodes at the end of `stmt_deps` are already landed
nodes, added under the standing rule allowing statement dependencies to gain landed
notions. They supply exactly the presentation, restriction, affine realization and
compatibility structures needed to state the original compatibility clauses. No node
is newly created or restated, and no dependency record is repaired.

Proof dependency imports are plain `import`; statement dependencies use `public
import`. All recorded proof modules are imported. The following proof nodes currently
have neither a Lean record nor a Mathlib match, so cannot supply an import yet:
`lem-sfb-proper-flat-space-derived-duality`,
`lem-sfb-derived-etale-zariski-equivalence`,
`lem-sfb-proper-flat-adjoint-tensor-formula`,
`lem-sfb-proper-adjoint-diagonal-pair`, and
`lem-trf-affine-algebra-class-evaluation-comparison`.
They are proof prerequisites only; no missing statement notion depends on them.
Mathlib proof leaves are imported by their recorded files (Flat,
FinitePresentation, FiniteType). No import cycle was introduced.

Edge cases checked before writing and against the completed statement:

- Empty X and empty affine source chart: B is the zero ring, which is allowed by
  `[CommRing B]`; D(B) is zero and all comparison maps are unique. There is no
  `[Nontrivial B]` or nonempty-space binder.
- Empty base: no excluded point or chart; all quantifiers and derived categories
  still make sense.
- n = 0: `Fin 0` is allowed; the exterior coefficient is wedge^0 = P with
  shift zero. The empty ordered volume is the unit. No positive-n binder exists.
- Identity morphisms: allowed; their zero-variable presentation realizes O_S.
- Arbitrary non-Noetherian base rings: no finiteness of ideals other than the
  geometric finite-presentation assumption appears in any binder.
- Non-Gorenstein flat proper families: K need not be a line or concentrated.
- Non-quasi-compact bases and non-quasi-separated schemes: neither is excluded;
  properness is a property of f. Atlas and chart quantifiers use no finite cover.
- Principal ambient h = 0 or h = 1: the existing localized compatibility predicate
  explicitly covers both, with the h=0 zero ring allowed.
- Coordinate permutations and different lifts of the additional image: the
  system quantifies over each lift and all polynomial automorphisms; its transition
  equations share the fixed identifications, retaining sign and lift independence.
- Chart ring universes: R and B are Type u with Scheme.{u}; their polynomial
  rings and localizations remain Type u. This covers all affine charts of those
  schemes and does not introduce a smaller independent testing universe.

Searches for an existing statement:

1. `msearch.py ... leanfinder "Proper flat duality normalized polynomial models over
   arbitrary schemes right adjoint derived direct image"`: eight hits, including
   `Scheme.Modules.instIsRightAdjointPushforward`, Gamma/Spec adjunctions and affine
   space normalization declarations. None states this derived right adjoint or the
   polynomial models.
2. `msearch.py ... loogle "AlgebraicGeometry.IsProper, Adjunction"`: zero hits;
   the service reported unknown identifier `Adjunction`.
3. `msearch.py ... grep "polynomial.*[Dd]ual|[Dd]ualizing" AlgebraicGeometry`:
   zero Mathlib hits.
4. `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for polynomial
   duality/model names found the Q42 presentation and atlas definitions and
   `exists_relativeDualityPolynomialChart`. Read in full: that theorem assumes
   `IsLocallyNoetherian S` and does not supply the global proper right adjoint, so
   it is a proof dependency, not an existing match. The definitions are reused.
5. `rg` for this node id in `lean/WeilConjectures`: no declaration.
6. `rg` for `exists_properFlatDualizingPolynomialModel` in both project roots and
   `dag/lean_names_upstream.json`: no existing name.

No STATEMENT-DISPUTED issue or source-based statement correction was needed.

Validation: prescribed `scompile.py Q72
lem-sfb-proper-flat-dualizing-polynomial-model <module>` passed for both its sandbox
probe and its actual library module name, with no compiler errors or warnings.
Only this statement is postponed; nothing was proved at stage 2.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
