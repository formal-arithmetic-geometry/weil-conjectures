## Worker report

Module: `Sheaf.Paper.ExactSectionsReductionUnit`. Main declaration:
`SheafOfModules.PrincipalReduction.Setup.exactSectionsReductionUnit`.
This states the node unchanged, with a single `sorry`. All helper definitions contain
actual data. No new nodes, dependency repairs, or statement corrections are needed.
The existing `PrincipalReduction.Setup`, its scalar maps, its universal derived tensor
models, and its canonical comparison are reused without modification.

Sources read: Stacks `sites-cohomology.tex`, `lemma-derived-base-change` (06YY) and
`lemma-adjoint` (07A6), and `derived.tex`,
`lemma-pre-derived-adjoint-functors-general` (0FND), together with the node's complete
seven-step extracted argument. The main theorem docstring carries those seven steps,
including the identification of the point-site extension with mixed tensor through
uniqueness of the counit-compatible left derived functor.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Small site with final object U | `C`, `Category.{v} C`, `J`, `EssentiallySmall.{r} C`, and `D.U`, `D.terminal` in the recorded `PrincipalReduction.Setup` |
| Exact sections on abelian sheaves | `D.sectionsExact : exactFunctor _ _ ((sheafSections J AddCommGrpCat).obj (op D.U))` |
| Commutative ring R and regular element t | `{R : Type r} [CommRing R]`, `D.t`, and `ht : Function.Injective (fun x : R ↦ D.t * x)` |
| A = R/(t) with specified quotient | `D.A`, `D.commRing`, `D.quotientMap`, `D.quotient_surjective`, `D.quotient_kernel`; this is the same specified principal quotient presentation used by the dependency |
| Ring sheaves O, O' and quotient morphism | `D.O`, `D.S`, `D.φ`; all are commutative ring sheaves on J |
| Compatible coefficient maps | `D.ρ`, `D.quotientSectionsMap`, `D.quotient_sections_comm` |
| Exact coefficient sequence and O' = O/tO | `D.zero`, `D.shortExact`, whose first map is `sectionMultiplication D.O D.U D.terminal (D.ρ D.t)` and second map is the underlying additive map of `D.φ`; the cokernel presents the quotient, including the specified quotient map |
| Module sheaves and derived categories | Existing `ringedSiteModules`, `DerivedCategory`, and four separate `HasDerivedCategory` instances |
| Exact coefficient restriction | `D.reductionRestriction` is an abbreviation of Mathlib `SheafOfModules.restrictScalars`; the two exactness instances project the existing ordinary coefficient-adjunction theorem |
| G, G', T, L with the specified scalar actions | Existing `D.G`, `D.G'`, `D.T`, `D.L`; no replacement functors are introduced |

The site-object, site-morphism and coefficient universes remain separate (`u`, `v`, `r`).
The four localization morphism universes (`wO`, `wS`, `wR`, `wA`) also remain separate.
The sheafification and sheaf-composition instances express the usual small-site module
category infrastructure, not additional geometric hypotheses.

Clause-by-clause correspondence:

1. `∃ a : D.extension.E ⊣ D.reductionRestriction` includes the ordinary normalization
   at every object `V` of the opposite site: after the prescribed presentation equality,
   its unit is the sheafification-unit image of `1 ⊗ x`. It is therefore the actual
   scalar-extension adjunction rather than an unspecified choice of adjunction.
2. `∃ b : D.T ⊣ D.reductionRestriction.mapDerivedCategory` includes the derived unit
   formula on every flat-term K-flat sheaf complex. After applying restriction to
   `D.extension.ε.app P` and the exact-functor factorization, `b.unit` is the localized
   ordinary unit. This is precisely the normalized sheaf adjunction in the dependency.
3. `∃ d : D.L ⊣ (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory` includes
   the corresponding ordinary-module unit normalization using the actual mixed-tensor
   counit `D.c Q` and Mathlib `ModuleCat.extendRestrictScalarsAdj`. The quantified Q
   is K-flat with flat terms; no such assumption is imposed on sections of P.
4. `∃ α : D.G ⋙ D.L ≅ D.T ⋙ D.G'` supplies isomorphisms for every derived N,
   natural for every derived morphism. The first conjunct is the node's unit equation,
   in Lean's left-to-right composition order.
5. `sectionsReductionRestrictionIso` is constructed by the identity on section groups.
   Its linearity is exactly `D.quotient_sections_comm`. The derived square
   `derivedSectionsReductionRestrictionIso` is obtained with existing
   `Functor.mapDerivedCategoryNatIso` and `Functor.mapDerivedCategoryCompIso`. Its
   component at `D.T.obj N` gives the precise target identification in the unit equation.
   It is not an assumed or arbitrary comparison map.
6. The next conjunct quantifies over every morphism f from LGN to G'TN: if its
   restricted composite with `d.unit` equals sections of `b.unit`, then `f = α.hom.app N`.
   This is uniqueness as the scalar-extension adjunct, without restricting f to an iso.
7. For every flat-term K-flat P, `α.hom.app (DerivedCategory.Q.obj P) = D.alpha P hP hf`.
   The existing definition `D.alpha` is literally `D.c (Gamma P)` followed by
   `DerivedCategory.Q.map (D.theta P hf).hom`, with the recorded localization and
   K-flat-model identifications. Thus normalization is the specified theta_P c_Gamma P.
8. For every ordinary flat-term K-flat resolution `q : Q ⟶ Gamma P`,
   `reductionRepresentative` is the actual chain map `extendScalars(q) ≫ theta_P`.
   Its degree-i formula at `1 ⊗ x` is `D.quotientSection (P.X i) (q.f i x)`.
   Since `D.quotientMap` is surjective with kernel tR, `1 ⊗ x` is the quotient class
   of x, so this is exactly x-bar ↦ q(x) modulo t. The A-linearity determines the
   map on every tensor, hence on the whole quotient.
9. `reductionRepresentativeAdjunct` applies the ordinary complex extension/restriction
   adjunction to that same chain map. Its formula is x ↦ q(x) modulo t. A further
   equality using `d.homEquiv` identifies its localization with the *derived* adjunct
   of `D.c Q ≫ Q_A(reductionRepresentative)`, so the formula is tied to the actual
   derived adjunction, not merely to a separate chain map.
10. The representative identity identifies `D.c Q ≫ Q_A(reductionRepresentative)`
    with the intrinsic component `α_P`, after precisely the canonical identifications
    supplied by q and the sheaf K-flat counit. It holds for **every** q, so changing
    q changes neither the represented intrinsic map nor its adjunct. The final
    conjunct says `D.resolvedComparison p hP hf = α.hom.app (Q M)` for **every** sheaf
    resolution p; this gives independence of the sheaf resolution as well. There is
    no K-flatness or term-flatness hypothesis on `Gamma P` anywhere.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, exactly
  Mathlib's `SheafOfModules`, including its inherited abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, read with its normalization
  and full signature. The statement here spells out its normalized adjunctions for
  the already recorded cochain models, retaining separate localization universes.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.DerivedReductionResolutionIndependence`:
  `SheafOfModules.PrincipalReduction.Setup`, its fields, `sections`, `quotientSections`,
  `G`, `G'`, `extension`, `quotientComplex`, `T`, `L`, `c`, `quotientSection`,
  `existsUnique_theta`, `theta`, `modelIso`, `alpha`, `resolvedComparison`,
  and `resolution_independence`. Their actual definitions and signatures were read.
- The proof-only dependencies are imported: `KFlatResolutionIndependentCoefficients`,
  `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`, `Mathlib.RingTheory.Flat.Basic`,
  `MixedTensorPointwiseLeftDerived`, `DerivedTensorSecondFactorFunctor`,
  `PrincipalQuotientQuasiIso`, and `DerivedChangeOfRingsCochainModel`.
- Supporting existing APIs: `SheafRingCoefficientOrdinaryAdjunction` for the exactness
  witnesses; Mathlib ordinary extension/restriction and complex adjunctions; upstream
  `DerivedBaseChange` for `ModuleCat.extendScalars_additive`; upstream derived exact-functor
  functoriality for the canonical restriction square.

Edge cases checked mathematically before stating:

- The point site, R = Z, t = 2, N = Z/2 in degree zero: derived reduction has its
  nonzero Tor term; nothing replaces it by underived tensor on N.
- R = Z × Z and t = (2,3): multiplication is injective but R is not a domain. The
  theorem accepts this case, unlike the existing domain-only principal comparison.
- t a unit: A and the quotient ring sheaf are zero and the unique comparison and units
  remain meaningful. No nontriviality or t ≠ 0 hypothesis is added.
- The zero ring, t = 0, and zero complexes are allowed. In a nonzero ring t = 0 fails
  exactly the regularity hypothesis. Arbitrarily unbounded complexes are included.
- The empty site cannot have a final object, exactly as in the node; no extra
  nonemptiness hypothesis is used. No object/morphism universe equality is imposed.

Searches actually run:

- `msearch.py`, LeanFinder: “Exact global sections commute with derived scalar extension
  by a principal quotient and preserve the scalar extension adjunction unit”. Eight
  hits, chiefly cotangent exact sequences and `Functor.mapExactFunctor_smul`; no match.
- `msearch.py`, Loogle: `"mapDerivedCategory", "unit"`. No hits.
- `msearch.py`, grep: `sections.*[Qq]uotient|[Rr]eduction.*[Uu]nit`. Five unrelated hits
  (roots of unity, submonoid units, elliptic reduction); no matching statement.
- `msearch.py`, LeanSearch: “Exact global sections of sheaves of modules commute with
  derived principal quotient and the comparison is adjoint to the scalar extension unit”.
  Eight hits, including `ModuleCat.extendRestrictScalarsAdj`, sheaf pullback adjunction,
  global sections, and module sheafification adjunction; no exact-sections derived
  principal-quotient unit theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the
  item id, `exactSectionsReduction`, `exact_sections_reduction`, and `PrincipalReduction`.
  Found the recorded resolution-independence module and the domain-only
  `PrincipalReductionComparison`/`PrincipalReductionFlatComparison` and point-site
  specializations. Read their declarations: none gives this general regular-element
  comparison with its unit, uniqueness and representative formulas.
- `rg` of Mathlib and both project source trees for the proposed public helper names
  and `exactSectionsReductionUnit`: no clashes. Inspected the actual scalar restriction,
  exact-functor, adjunction, K-flat, flatness, tensor and quotient APIs before using them.

No `STATEMENT-DISPUTED` flag: the statement agrees with the source-derived argument and
its tested edge cases. Only the item's `lean` record is changed. All variables and
universes are explicitly bound; there are no local notations or private definitions.

Validation is through the prescribed `scompile.py` and `deliver2.py` wrappers only.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
