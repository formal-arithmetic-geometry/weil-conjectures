## Worker report

The module `Sheaf.AlgebraicGeometry.ZariskiNaiveCotangentAffineComparison` states
Stacks Tag 0D0I for the morphism of affine schemes induced by an arbitrary ring map.
There is one postponed theorem, `zariski_naive_cotangent_affine_comparison`; its
proof docstring gives all five DAG steps. All definitions contain real data.

Hypothesis and clause correspondence:

- The only mathematical input is `φ : R ⟶ B`, with `R B : CommRingCat.{u}`.
  No nontriviality, finite generation, Noetherianity or flatness assumptions occur.
  Arbitrary rings can be placed in a common universe; no independent test-object
  universe introduces a vacuous condition.
- `Spec B`, `Spec R` and `Spec.map φ` are exactly U, V and f.
- `presentation φ` has ring `MvPolynomial B R`, coefficient map `MvPolynomial.C`
  and augmentation `MvPolynomial.eval₂Hom φ.hom id`, sending X b to b.
  Surjectivity is witnessed by X b. Thus the kernel is exactly the displayed J.
- The imported `Algebra.CotangentResolution.Naive.complex (presentation φ)`
  uses the actual Mathlib conormal quotient and tensor-differential module, with
  the differential `Extension.cotangentComplex`. `kernelClass`, `tensorGenerator`,
  `conormalIso`, `differentialsIso` expose these coordinates. Its degrees are -1,0,
  zero elsewhere. No alternate ring-complex definition is supplied.
- `associatedComplex φ` applies `tilde.functor B` termwise via
  `mapHomologicalComplex (.up ℤ)`. This is precisely the stated associated complex.
- `sheafPresentation φ` is `SheafPolynomialCotangent.canonical` for the existing
  `Scheme.Modules.tensorPullbackRingMap (Spec.map φ)`. Its source is the actual
  `TopCat.Sheaf.inverseImageRing` and its target is `(Spec B).sheaf`.
- `K : SheafPolynomialCotangent.Model (sheafPresentation φ)` is a representative
  of the dependency's K_B. It includes the exact locally defined conormal quotient,
  the actual differential term, support outside -1,0, and the differential formula.
  Quantifying over this representative makes no choice of undetermined data and
  works with the models of the dependency's `Comparison` equally. It is not an
  extra geometric assumption or a substitute arbitrary complex.
- `Comparison.map : associatedComplex φ ⟶ K.complex` is the map of complexes.
  `coefficientSection` is the inverse-image adjunction unit from R, restricted to
  each W. `functionSection` is b as a regular function on W. `polynomialSection`
  maps coefficients and variables by these maps, then uses the sheafification unit.
- `Comparison.conormal_formula` says every kernel polynomial maps to its class in
  K. The existential j is only a kernel membership witness for that exact polynomial,
  not an arbitrarily selected section: its underlying element is explicitly fixed.
  `Comparison.differential_formula` maps every tensor b tensor dh to the corresponding
  local function times the universal differential. These are exactly the adjoint
  construction in the DAG proof, and determine the two components canonically.
- `Comparison.quasiIso` asserts quasi-isomorphism of this very chain map.
  `Comparison.derived` is an isomorphism of its images under the existing
  `SheafPolynomialCotangent.localization (Spec B).sheaf`; `derived_hom` identifies
  its hom with the localization of `map`, so it is not an unrelated isomorphism.
  This localization is Mathlib `DerivedCategory.Q` with the standard localization
  instance, not a new category or new abelian instance.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: Scheme, Scheme.Hom, Spec, Spec.map.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: MvPolynomial, C, X,
  eval₂Hom, eval₂_X; the ring-map version of aeval gives the same polynomial evaluation.
- `Mathlib.RingTheory.Kaehler.Basic`: KaehlerDifferential, D and its universal
  property, through the existing ring and sheaf cotangent interfaces.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and associated scalar-extension API:
  the actual tensor product through `Naive.differentials` and the sheaf differential term.
- `Sheaf.CategoryTheory.SheafPolynomialCotangentComparison`: canonical, Model,
  polynomials, polynomialSheaf, kernelIdeal, tensorD, localization. The dependency
  theorem supplies models; its already exposed Model encodes exactly K_B.
  The existing definition node `def-sfb-sheaf-polynomial-cotangent-presentation` is
  also cited for canonical, polynomials, polynomialSheaf, kernelIdeal and tensorD;
  Model and localization retain the original comparison-node dependency.
- `Mathlib.Topology.Sheaves.Functors`: inverse-image adjunction; the equivalent
  explicit construction is `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  as used in upstream inverseImageRing and tensorPullbackRingMap.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: tilde.functor, tilde.toOpen,
  tilde.adjunction (the latter in the construction proof), ΓSpecIso.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: DerivedCategory.Q and
  QuasiIso, via the dependency's localization wrapper.
- Added existing definition dependency `def-trf-naive-cotangent-comparison-data`:
  `Sheaf.RingTheory.NaiveCotangentComparison`, Presentation, complex, kernelClass,
  tensorGenerator, conormalIso and differentialsIso. This is the already established
  two-term ring model. Its declaration ownership is the existing definition node;
  the existence theorem `lem-trf-lci-naive-cotangent-model` is not a statement dependency.
- Added existing statement dependency `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, publicly exposing
  upstream `AlgebraicGeometry.Scheme.Modules.tensorPullbackRingMap`. This uses only
  its canonical structural ring map, not a second definition of inverse image.

All already stated proof inputs are imported: AffineScheme and Tilde for affine and
module stalk localization; InverseImageStalk; Kaehler.Polynomial; LocalizedModule.Exact;
Etale.Kaehler for H1 and differential localization and the cotangent exact sequence;
ModuleStalkExact. The two proof-only nodes `lem-sfb-naive-cotangent-localize-base` and
`lem-sfb-naive-cotangent-stalk-comparison` have no recorded Lean declarations or
Mathlib matches on this base, so no fictional module imports are added for them.
They are proof prerequisites, not missing objects needed to type this statement.

Edge cases checked against the definitions and source: B zero (empty Spec B), R=B
and φ=id (the standard polynomial complex remains its standard presentation),
nonflat Z→Z/2, infinitely many polynomial generators, arbitrary characteristics,
W=empty and W=top. Quotient local surjectivity is the dependency's sheaf condition;
no sectionwise surjectivity of the sheaf conormal quotient is assumed. The only
explicit surjectivity proof is the valid ring evaluation with the X b witness.

Searches (2026-10-24):

- msearch.py leanfinder, query “The Zariski naive cotangent complex of Spec B over
  Spec R is quasi-isomorphic to the tilde of the standard ring naive cotangent complex”:
  eight results, including Algebra.H1Cotangent, Extension.cotangentComplex_mk and
  localized cotangent maps; none states this sheaf comparison.
- msearch.py loogle, query “Algebra.Extension.cotangentComplex, AlgebraicGeometry.tilde”:
  zero hits.
- msearch.py grep, query “naiveCotangent|cotangentComplex|NaiveCotangent” in
  AlgebraicGeometry: zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf with those terms and the item id:
  found the existing ring Naive complex, generic sheaf-polynomial comparison and
  affine étale consumer, but no theorem with this Zariski comparison statement.
  The affine étale consumer's docstring refers to this missing item as its prerequisite.
- Checked dag/lean_names_upstream.json for the item and proposed module/name:
  no collision. Read the source of every recorded statement dependency; no dependency
  record repair or new definition node is needed.

Source read locally: literature/stacks-project/more-morphisms.tex,
section-netherlander, definition-netherlander and lemma-NL-affine (Tag 0D0I), including
its proof from sections, the tilde universal property, stalks and both localizations.
The statement is unchanged. No STATEMENT-DISPUTED issue was found.

## Second reading by Q74

Performed a separate in-thread rereading of the node and completed module. No other
agent was started, as the dispatcher brief explicitly prohibits starting agents;
the maintainer's independent delivery review remains separate.

Checked the arbitrary ring-map binder against the absence of finiteness hypotheses;
the exact polynomial presentation against P_0, α_0 and J; the reused ring complex
against both terms, its differential and degrees; termwise tilde against the module
adjunction; the canonical sheaf presentation against f⁻¹ O_V→O_U; and both generator
formulas against the sectionwise construction of η. Checked that quasiIso applies
to η and that derived_hom identifies the displayed derived isomorphism with Q(η).
The Model binder is a choice of coordinates for the dependency's K_B, not an
assumption that such a model has additional properties.

The compile-directed corrections were the restriction proof `le_top : W ≤ ⊤`
and the explicit coercion of a kernel element to `(presentation φ).ring`. The
completed signatures have no diagnostic commands, hidden lets, file-local notation,
new category structures, extra finiteness assumptions or arbitrary comparison map.

## Returned delivery repair (2026-10-25)

H2 on immutable head `3f5d67dcfad3`: replaced the added statement dependency
`lem-trf-lci-naive-cotangent-model` with its definition owner
`def-trf-naive-cotangent-comparison-data`, as requested. Read the current owner node
and its recorded declarations in `Sheaf.RingTheory.NaiveCotangentComparison`: the
statement uses Presentation, complex, kernelClass, tensorGenerator, conormalIso and
differentialsIso, all registered there. It does not use the existence theorem.
Also followed the advisory by citing the landed definition node
`def-sfb-sheaf-polynomial-cotangent-presentation` for the polynomial presentation
constructions; Model and localization continue to use the original comparison node.
Updated the dependency mapping above. The Lean file and its theorem signature are
unchanged from the returned delivery; no mathematical statement was altered.
Compared the retained node against current main and retained current-main metadata
while applying only stmt_deps and lean. The delivery wrapper rebases the repaired
files onto current main in its private worktree.

Reread the corrected dependency list against the actual source declarations: the
ring-complex definitions now point to their definition node, the sheaf presentation
points to its definition node, and the structural inverse-image map remains attributed
to def-pc-module-pullback. This addresses the numbered return without modifying Lean.
