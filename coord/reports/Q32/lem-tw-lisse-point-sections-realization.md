## Worker report

The new module `Sheaf.Paper.LissePointSectionsRealization` states
`WeilConjectures.LisseRealization.lisse_point_sections_realization` and
`lisse_point_sections_scalar_compatibility`, both with `sorry` proofs. The two
structures in their conclusions retain the actual comparison maps and their
normalizing equations. `pointIntegralUnit` and `pointRationalUnit` are transparent
specializations of the existing single functor and coefficient units. No new
coefficient sheaf, module category, tensor, pullback, rationalization, or point
fibre is defined. There are no definitions with postponed data or new axioms.

The mathematical statement is unchanged. The only change outside `lean` is adding
the already landed node `def-real-lisse-field-normalization` to `stmt_deps`, as
permitted by brief-stage2 §5 for a recorded notion used by the statement. Its
`FieldNormalized` fixes the very completion/scalar map required by the last
clause. No new node or dependency repair is needed.

### Hypotheses and objects

- The finite-field datum is `D : FiniteFieldDatum.{u}`, whose geometric field is
  the algebraic closure `D.k`. `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p`
  retain exactly the coefficient-prime assumptions.
- `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` encode the finite coefficient extension. The
  integer ring and chosen uniformizer are the recorded
  `Padic.coefficientExtensionIntegers` and `coefficientExtensionUniformizer`.
  The statement is invariant under choosing an embedding in an algebraic closure;
  all finite field embeddings are included by `i : E →ₐ[ℚ_[l]] F` below.
- `X : LisseRealization.Base D l hl` contains the scheme, its structure map over
  `Spec D.k`, and local finite type plus quasi-compactness of that map. It has
  no separation assumption. `x : (point D l hl).scheme ⟶ X.scheme` is an
  arbitrary scheme map, without a requirement of k-linearity.
- The site is exactly `Scheme.ProEt` and its topology. Completed coefficients are
  `completedIntegralCoefficientSheafUnrestricted`; localized coefficients are
  `rationalCoefficientSheaf`, identified with sheafified localization by the
  existing `At.localization` and its unit equation.
- `sfIntegralConstructibleCategory` is the integral category. `Raw` is its raw
  scalar localization, with unchanged objects and tensor Hom groups.
  `At.J`, `At.integral`, and `At.fractions` are exactly the specified J, F, and
  formula on rational arrows. `Lisse` is the recorded intersection of the
  rational standard heart and local finite-free triviality. Local models and
  varying ranks, including zero, are unchanged.
- The parameters `a`, `t`, and `r` are the normalized realizations and the
  specified tensor/pullback comparisons already introduced in the node. These
  are not extra flatness, completeness, finiteness, or point-comparison
  hypotheses. The conclusion constructs the point comparison on top of them.
  They use the previously recorded comparison interfaces, rather than replacing
  a canonical operation by a free map.

### Every conclusion clause

1. The point `s` is the existing `point D l hl = Spec D.k`.
   `PointSectionsRealization.integral_constants` and `.rational_constants`
   assert bijectivity of the actual constant-section ring homomorphisms, so their
   inverses are evaluation on the one-point space. This records B(s)=R, A(s)=E
   with their prescribed identifications, not arbitrary ring isomorphisms.
2. `.normalized : PointNormalized ...` contains `.ordinary`, a natural
   isomorphism from integral sections followed by ordinary localization to
   ordinary scalar extension followed by sections. Its `.sections` equation is
   precisely `c ⊗ z ↦ c(1 ⊗ z)` through `pbcTensorSection`.
   The coefficient tensor is written E tensor_R Gamma; the node's displayed
   Gamma tensor_R E has the same canonical map under tensor symmetry.
3. `.normalized.derived` is a natural isomorphism of functors on the *unbounded*
   ambient integral derived category. Its `.derived_normalized` equation uses
   every representative complex, the actual scalar counit, the exact-sections
   factorization, and `NatIso.mapHomologicalComplex ordinary`. This asserts the
   termwise comparison, with naturality on all derived morphisms. Restriction to
   integral constructible objects gives every lambda_C in the node.
4. `.integral_hom` and `.rational_hom` give the unit-Hom/sections identifications.
   Their `_natural` fields state naturality on all derived arrows, and their
   `_one` fields normalize evaluation of the identity to the actual section 1.
   By Yoneda this fixes the identifications, instead of choosing unrelated group
   equivalences. `.hom_scalar` quantifies `q : ℤ` and evaluates at C[q]. It says
   the H^0 map of lambda_{C[q]} carries `c tensor integral_hom(f)` to
   `rational_hom(c • F(f))`, inserting the specified derived unit comparison.
   Exact sections and shifts identify this with H^q(lambda_C), including negative
   degrees. The homology/scalar-tensor comparison is the recorded exact-functor
   comparison, not an extra map.
5. `.comparison` is an actual isomorphism in D(E), after the canonical carrier
   lift of the recorded small fibre. Its target is the single in degree zero
   of sections of `ordinaryPull x (H^0 J_X K)`, i.e.
   A_s tensor_{x^{-1} A_X} x^{-1}(H^0 J_X K). The derived source is the recorded
   `pointRationalFibre`, not a newly chosen fibre functor.
6. `.comparison_normalized` is the formula nu, then lambda, inverse integral
   realization, the specified `RealizationPullComparison.comparison`, its
   homology-normalized single identification and ordinary-pull single comparison,
   followed by exact sections of a single. `nu` is literally
   `pointRationalNormalization`. The chosen single identification is required to
   induce the identity on H^0; full faithfulness on degree-zero objects removes
   any freedom in that choice.
7. `.degree_zero` identifies H^0 of this *same derived isomorphism* with the
   `PointNormalized.square` comparison followed by ordinary pullback comparison.
   `.point.degree_zero` records that the original small fibre is in degree zero;
   `.finite` asserts finite dimension of the target. The derived isomorphism
   gives the same claim on the source. `.naturality` is the square for all raw
   rational arrows, with no integral-arrow restriction.
8. `.tensor_sections` and `.tensor_sections_normalized` fix evaluation of ordinary
   sheaf tensor on every pure section: pure(x,y) maps to x tensor y.
   `.unit_sections_normalized` sends the constant c to up(c), in particular
   1 to up(1). `.fibre_tensor`, `.tensor_square`, `.fibre_unit` and `.unit_square`
   retain the actual tensor and unit comparison diagrams with the point map.
   Naturality of the fibre tensor follows from these squares and the natural
   point isomorphism. `.pull_tensor` is the existing `PullTensor` interface for
   every x, with both its pure pulled-back-generator formula and its actual
   compatibility equation with the tensor comparisons t and pullback comparisons r.
   Combining it with the point tensor square and `.degree_zero` gives the tensor
   square for the displayed comparison at x. The specified normalized pullback
   sends local basis vectors to themselves. On units and their finite sums this
   gives e_i tensor e_j to e_i tensor e_j, with the empty sum included.
9. `lisse_point_sections_scalar_compatibility` uses arbitrary finite coefficient
   fields E,F and embeddings i, with their recorded `FieldChange` and
   `FieldNormalized` comparison. It constructs `PointSectionsScalarCompatibility`.
   Its `.ordinary` and `.sections` fix the point sections/scalar comparison on
   every `c : F`, not just integral c. `.derived_normalized` fixes its termwise
   descent with the same ordinary comparison and the actual universal counit.
10. The scalar structure's `.square` is the *derived* commuting diagram using
    `pointRationalSectionsScalarExtensionIso` (the recorded phi), lambda_E,
    lambda_F, and `FieldNormalized.derived`. The sole raw-object transport is
    `eqToHom` of the recorded scalar functor's object formula. `HEq` expresses
    the endpoints with that already specified object identification; it is an
    equality of the complete composite arrows, not only homology.
    `.pullback` supplies `Mixed` for every x and normalized coefficient change
    at X: its balanced-section formula and actual pullback/scalar compatibility
    equation are retained. Together with `.square` and
    `.comparison_normalized` this gives the scalar square of the displayed
    point comparison for every x. Conjugating by the recorded size-descent
    normalization gives exactly the recorded fibre scalar comparison, whose
    definition uses this same phi. Identity and tower specializations use phi's
    already recorded unit/tower equations and the scalar associators. No equality
    of uniformizers is used.

### Dependency declarations read and used

- `Sheaf.Paper.LissePointNormalization`: `LisseRealization.PointNormalized`,
  including ordinary, sections, exact counit, derived representative and square fields.
- `Sheaf.Paper.RationalLocallyFree`: `IsRationalLisse`,
  `rationalLisseHeartProperty` (through the existing `Lisse` alias).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and the localization convention.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, the recorded completion and its
  constant cone. The completion is used through the recorded integral-module
  and realization interfaces, not redefined.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeartProperty`, `sfRationalHeart`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`,
  `pointRationalNormalization`, `pointRationalFibreScalarIso`. The latter is
  characterized by phi and the size-descent counit; this is why the derived
  scalar square descends to the recorded fibre square.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the public coefficient constructions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`, and its
  uniquely fixed object formula.
- `def-weil-scheme-morphism-properties` is a convention collector; as its record
  requests, the existing finite-type and quasi-compact classes are used in `Base`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` is the transparent
  Mathlib `SheafOfModules` category used by the imported module interfaces.
- `Sheaf.Paper.LisseTensorPullbackRealization`: `RealizationTensorComparison`,
  `RealizationPullComparison`, their normalized tensor/unit and pullback maps.
- `Sheaf.Paper.PointProEtaleSectionsExactOfUniverses`:
  `point_proEtale_sections_exact_of_universes`. The actual specialized exact
  sections and factors are the existing `pointCompletedSections`,
  `pointCompletedDerivedSections`, and `sections` composites.
- `Sheaf.Paper.PointSectionsScalarExtension`: `pointSectionsScalarExtension`,
  `pointRationalSectionsScalarExtensionIso`, `pointModuleRationalization`,
  `pointModuleDerivedRationalization`, `pointCoefficientFieldDerivedTensor`.
- Added recorded dependency `Sheaf.Paper.LisseFieldNormalization`:
  `LisseRealization.FieldNormalized`, whose `.chi_normalized`, universal counit,
  and `.derived_normalized` fix the scalar map of this item.

Statement dependencies are public imports, including through the already recorded
public import closures. Stated proof dependencies are plain imports:
`PointRingedEvaluationModel`, `DerivedInternalHomSectionsModel`,
`CoefficientComplexRationalization`, `ContinuousCoefficientImmersionRestriction`,
and `PointSectionsFiniteness`. The two proof-only nodes
`lem-tw-lisse-localization-restriction` and
`lem-tw-lisse-scalar-comparison-coherence` currently have no Lean record; their
future proof imports are not invented. Their roles and proof arguments are in the
new theorem docstrings. The required normalized realization operations are already
provided by the recorded statement dependencies.

### Sources and edge cases

Read Bhatt--Scholze 6.8.12--6.8.15 from the supplied PDF, including 6.8.13's
warning that a global lisse integral lattice need not exist. The formal statement
therefore uses the existing local-lattice lisse predicate and raw objects; it never
assumes a globally lisse lattice. Read the current blueprint's
`lem-tw-dual-negation.proof.md`, first sentence, which is the ancestor use.

Checked zero objects and rank zero: no nonempty basis or positive-rank hypothesis
occurs. Tensor sections is fixed on every pure tensor; the zero object has the
unique zero map. Ranks vary over the existing lisse covering. The empty scheme is
allowed by Base; a map from s to it has no inhabitant, so the x clauses are
correctly vacuous. Nonseparated finite-type schemes and non-k-linear maps are
allowed. `q : ℤ` retains negative, zero and positive degrees. Fraction coefficients
are arbitrary elements of E/F, including zero. Finite extension may be the identity,
and may be ramified; the diagrams use the normalized completed coefficient map,
not a relation of chosen uniformizers.

Universes are explicit and `autoImplicit` and `relaxedAutoImplicit` are disabled.
The existing site has object universe u+1 and morphism universe u; module carriers
have size u+1. The recorded small fibre is lifted by `ModuleCat.uliftFunctor`
and identified by `pointRationalNormalization`. The tensor of large carriers is
written `ModuleCat.of E (M tensor[E] N)` directly, and the coefficient unit is
`ModuleCat.of E (ULift E)`; this avoids the equal-universe restriction of Mathlib's
module monoidal instance. These are the ordinary tensor and the same scalar
module, with no imposed universe equality or changed site.

No statement dispute or mathematical correction was found.

### Searches and validation

The prescribed `msearch.py` searches were run for this item; its sandbox
`searches.jsonl` records their exact queries/results:

- LeanFinder: "At an algebraically closed pro-etale point exact sections commute
  with scalar localization and normalize lisse fibres preserving tensor units and
  coefficient extensions". Eight hits on algebraic etale localization and scheme
  normalization, none on the specified point comparison.
- Loogle: `SheafOfModules.unitHomEquiv`. Six hits, the ordinary unit/sections
  equivalence and its naturality/evaluation lemmas. Read its full definition and
  signatures in Mathlib; it does not assert the derived/rational lisse comparison.
- Mathlib grep: `sections.*locali[sz]|unitHomEquiv` in
  `Algebra/Category/ModuleCat`. Sixteen hits on free module sheaves, pullback and
  ordinary sections, not this statement.
- LeanSearch: "Sections of lisse adic sheaves at a geometric point commute with
  rationalization and tensor products". Eight hits on tensor scalars, associated
  sheaf sections, sheafification/pullback and condensed monoidal modules; no exact
  statement.
- `rg` in `lean/WeilConjectures` for this node id and the proposed theorem/structure
  names: no existing declaration. Broader point/sections/localization searches
  give ordinary algebraic geometry and point-fibre infrastructure, not this lemma.
- `rg` in `lean/Sheaf/Paper` found the recorded `PointNormalized`, the tensor and
  pullback realization interfaces, and the final assembly
  `LisseRationalRealization`. The latter asserts the downstream complete family;
  it is not the statement of this isolated point comparison. Those existing
  interfaces are used rather than copied. No new independent notion is introduced.

Compilation uses only `scompile.py Q32 lem-tw-lisse-point-sections-realization`
with this module. The final per-file compile is recorded in the delivery output.
The `deliver2.py --no-push` preflight and final delivery are performed after this
report and node record are complete. All probes are removed. Both theorem proofs
are `sorry`, as required in stage 2. All helper definitions have real data.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
