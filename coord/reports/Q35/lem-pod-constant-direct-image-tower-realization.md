## Worker report

The module `Sheaf.Paper.ConstantDirectImageTowerRealization` states
`WeilConjectures.constantDirectImageTowerRealization`, with only `sorry` as its proof.
Its helpers are actual functor compositions, an instance obtained from Mathlib's existing
finite-colimit preservation, and the actual scalar-unit/finite-comparison composite.
No data are defined by `sorry` or by an unconstrained existence choice.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The global p,a,q,k₀,k datum is `D : FiniteFieldDatum.{u}`; its fields explicitly include
  primality, positive exponent, cardinality and the specified algebraic closure.
* The coefficient prime and finite extension are `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`
  and `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The integer ring, chosen uniformizer and quotient at exponent n+1 are exactly
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and
  `coefficientExtensionRing l E (n + 1)`. No second coefficient ring is introduced.
* Y and f are `(Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]` and
  `Y ↘ Spec (.of D.k)`. `LocallyOfFiniteType` and `QuasiCompact` together mean finite
  type. `IsSeparated` is an explicit section binder. The site remains Mathlib's
  `ProEt`, with object universe u+1 and morphism universe u.
* F_n[0], completed coefficients in degree zero, and their projection-induced reduction
  maps are the existing `finiteConstantCoefficientObject`,
  `integralCohomologyCoefficient`/`integralConstantCoefficientObject`, and
  `constantCoefficientReductionMap`. `connectedFiniteTowerIso` uses the latter actual
  morphism and its canonical invertibility, not an arbitrary endpoint isomorphism.
* B_n is `sfDirectImageTerm ... (integralCohomologyCoefficient ...).obj n`.
  Its transition is exactly `sfDirectImageTransition`. B with the specified Roos
  triangle is `connectedIntegralImage`; this is the very choice used by `integralImage`
  in the ordinary cohomology definition. All these helpers lack a connectedness premise.
* C and C_n are the images under `constantTowerAbSections`. This is the existing exact
  `pointFibreIntegralAmbient`, followed by the exact localization of the ordinary
  forgetful functor to `AddCommGrpCat.{u+1}`. Thus the displayed triangle is in D(Ab).
  `[HasDerivedCategory.{w} AddCommGrpCat.{u+1}]` chooses any localization presentation,
  not a mathematical condition on the field, scheme, or coefficient ring.
* The existential e is the product comparison. Its first equation specifies each of
  its coordinates as the image of the actual product projection. The next conjunct
  is `IsDerivedLimitTriangle` of the image of the actual transition, with first arrow
  Γ(projection) followed by e.hom and last arrow e.inv followed by Γ(boundary) and
  the canonical shift comparison. The following conjunct retains Γ(p_n) explicitly.
* `constantTowerFiniteProjection` is Γ(η_B), then Γ(Res ρ_n), then the existing
  finite-tower identification. The next conjunct identifies this composite with the
  image of the specified Roos projection followed by the same identification.
  Its degree-zero clause applies the canonical exact restriction/homology comparison
  and asserts the result equals the existing map `P D l hl E Y n` on every element.
* The Q conjunct uses `connectedFiniteH0SectionsIso` on both ends and asserts that Q
  is `(integralCoefficientSheafTransition ... n).hom.app` at the object used to
  evaluate f_* at the final point. This is exactly the sectionwise quotient
  F_(n+1)(Y) → F_n(Y). The natural augmentation identifies this evaluation with Y
  sections. As Q is already defined by H⁰ of `sfDirectImageTransition` conjugated by
  `connectedFiniteTowerH0Iso`, the formula also states the required augmentation
  description of that actual transition, not a newly chosen Q.
* The final conjunct is `Q n (P (n+1) x) = P n x` for every n and integral H⁰ class.
  The internal index n : ℕ denotes the source's positive exponent n+1, including
  exponent one; its successor denotes n+2. No zero or first positive level is lost.
* There is no ConnectedSpace, Nonempty, higher-cohomology finiteness, flatness of a
  quotient over another quotient, or properness hypothesis.

Dependency declarations read and used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public dependency
  `CoefficientExtension`: the integer ring, uniformizer, ideals, quotient rings,
  transitions, and `Padic.finite_coefficientExtensionRing`.
* Morphism properties use Mathlib `Scheme.Over`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, as prescribed by the convention-only morphism-properties node.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its public dependencies:
  completed coefficients, their limit projections, and `integralCoefficientSheafTransition`.
* `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`, `sfDirectImageTerm`,
  `sfDirectImageTransition`, `sfDirectImageReductionComparison`.
* `Sheaf.Paper.ConstantCoefficientScalarNormalization` publicly retains
  `ConstantCoefficientObjectsConstructible`: `constantCoefficientReductionMap` and
  `integralConstantCoefficient_constructible`.
* `Sheaf.Paper.PointProEtaleSectionsExactOfUniverses`:
  `AlgebraicGeometry.ProEtale.pointModuleSectionsOfUniverses` and
  `point_proEtale_sections_exact_of_universes`; the original same-size evaluation
  and its exactness are retained by its public import. `pointFibreIntegralAmbient`
  is the existing exact localization, with the ordinary integral action.
* `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle`, `IsDerivedLimit`.
* `Sheaf.Paper.PointReductionUnits`: `pointUnitIntegralSheafUnit`,
  `pointUnitIntegralRestriction`, `pointUnitIntegralSectionsRestrictionIso` and its
  exact localization. `connectedSectionsRestrictionIso` transports that same
  identity-on-sections square to ordinary cohomology's small-Hom localization.
* `Sheaf.Paper.CommonStageCompactWeilCohomology` publicly retains
  `OrdinaryCompactCohomology`: `finiteOrdinarySections`, `finiteOrdinaryCohomology`,
  `integralImage`, `integralOrdinaryCohomology`, coefficient objects.
  The additional public import exposes the already existing P/Q helpers
  in `Sheaf.Paper.ConnectedConstantH0`, without invoking its connectedness theorem.
* Proof imports include `site_rgamma_derivedLimit`, strict scalar-unit normalization,
  scalar adjunction, K-injective existence, ringed-topos composition, the generic
  right-derived H⁰ unit calculation, and `constantTowerTransition`. The corresponding
  Mathlib injective-resolution, K-injective, and triangulated-composition modules
  are imported for their recorded proof nodes. The finite-sheaf H⁰ augmentation node
  has no recorded declaration yet; it is not imported and is not assumed. The current
  statement uses the already constructed canonical augmentation isomorphism, and
  its eventual proof can use that node when available.

Edge cases checked against the signatures and constructions: empty Y, disconnected
Y with independent sections on each component, exponent one, and the successor
quotient that is not flat over its predecessor. All remain in the binders. The
augmentation comparison never replaces all sections on a disconnected scheme by
constant sections. Zero maps and zero sections are permitted. The boundary includes
its shift comparison and the same 1-s sign convention as `IsDerivedLimitTriangle`.

Searches actually run:

* `msearch.py ... leanfinder`, query “Applying exact point sections to completed constant
  coefficient direct image derived limit Roos triangle with projections and degree zero
  quotient transitions”: 8 unrelated homological-triangle hits, no exact theorem.
* `msearch.py ... loogle`, query `CategoryTheory.IsDerivedLimitTriangle,
  CategoryTheory.Limits.Pi.π`: unknown project identifier IsDerivedLimitTriangle,
  zero hits; this service result is not evidence that project declarations are absent.
* `msearch.py ... grep`, query `IsDerivedLimitTriangle|sfDirectImageTransition`:
  zero Mathlib hits.
* `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  the item ID found no existing statement; `rg` for direct-image transitions and
  constant towers located `SfDerivedDirectImage` and the existing cohomology helpers.
* Searches of the prospective helper and main declaration names in Mathlib,
  WeilConjectures and Sheaf found no collision.

Source reading: Stacks `sites-cohomology.tex`, lemma-RGamma-commutes-with-Rlim,
Tag 0D6K, and `derived.tex`, lemma-left-exact-higher-derived, Tag 05TD; current
`literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-finite/
prop-cohomological-finiteness.proof.md`, final constant-sheaf paragraph.
The theorem docstring records all seven node proof steps. No statement correction
or disputed mathematical claim is needed.

No dependency module was needed. The ordinary-cohomology dependency is imported through its public
module and its existing declarations are used; the additional P/Q helper declarations are already
public in `Sheaf.Paper.ConnectedConstantH0` and are imported directly by the item module.
Because connected-h0 uses this item in its proof, its future proof import of this module must
be omitted to avoid an import cycle, as required by stages/2-statements.md §3.7. Only the
existing definitions introducing P and Q are used here, never the connected-h0 theorem.

## Second reading by Q35

A second pass by the same dispatcher worker, not an independent agent (the dispatch
brief expressly forbids starting agents), compared the node text with the final
signature and opened the definitions of P, Q, connectedIntegralImage,
connectedFiniteTowerIso and connectedFiniteH0SectionsIso. The maintainer's independent
review remains required. This pass found that a first draft only expressed projection
compatibility and omitted the D(Ab) triangle and quotient-on-sections clause. Both
were added. The product comparison was fixed to start at Γ(∏ B_n), not Γ(B), and its
coordinate equations now specify the actual projections. A finite-reduction composite
was added explicitly so the P assertion includes the adjunct/unit normalization.
The actual quotient map is now evaluated after the canonical augmentation on each
side of Q. It has no premise identifying all sections with constants. The separated
hypothesis is retained through the explicitly bound section variable. The n+1 indexing was checked
at n=0 and n=1. All seven node clauses are present. The only additional binder is an
arbitrary D(Ab) localization presentation; no new geometric or finiteness assumption
is imposed. The only node change is its new lean record. Existing helper data are reused.
