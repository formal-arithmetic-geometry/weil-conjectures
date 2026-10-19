## Worker report

Repair of returned head b7669291e300. The initial required saved-packet dry run
passed at 6a63280838, but rereading confirmed that the returned mathematical
faults remained. The repaired main module is
`Sheaf.AlgebraicGeometry.TorsionStalkProEtaleResolutionMap`.

The theorem now asserts four substantive clauses:

1. `torsionStalkPointSectionsBeta Ω Λ a F = torsionStalkResolutionGlobalSections ...`.
   The left side applies derived point sections to precisely
   `Functor.rightDerivedFunctorPlusBaseChange
   (lowerStarComparisonUpperStarBaseChange a (ModuleCat Λ))`, with the canonical
   source and target Leray maps. Its source point identification is
   `boundedBelowComparisonGlobalSections (Spec Ω) Λ` at `Ra_et,* F`.
   This is defined by the comparison derived adjunction unit and the comparison
   Leray map. At the geometric point, exact sections and the constant presentation
   of comparison-sections identify it with the original comparison unit evaluated
   at P, termwise. There is no new exactness assumption or chosen endpoint iso.
   The right side localizes the published `comparisonResolutionSections` evaluated
   at `op (Scheme.Etale.mk (𝟙 Z))`. By the definition of that map it is exactly
   Γ(Z_et,I) -> Γ(Z_proet,A_Z I) -> Γ(Z_proet,J), with first arrow the comparison
   unit (inverse-image sections) and second arrow Γ(j).
2. This normalized resolution morphism equals
   `(boundedBelowComparisonGlobalSections Z Λ).app F`, the specific canonical
   cohomology comparison, not merely an invertible map with those endpoints.
3. For every `φ : F ⟶ F'`, the square using etale RΓ(φ), the point-section mate
   at F', the displayed resolution morphism at F, and pro-etale RΓ(A_Z φ) commutes.
   This is naturality in the derived object, not site-object naturality.
4. For every second pair I', J', representative eF' and quasi-isomorphism j',
   the two normalized resolution morphisms agree. All four endpoints are actual
   derived global sections. This is independence of both resolutions under
   their canonical derived identifications.

Hypothesis-by-hypothesis: `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]` give the
algebraically closed field; P is `Spec (.of Ω)`. `Λ : Type (u+1)` and
`[CommRing Λ]` give arbitrary discrete commutative coefficients at the established
project size convention. `Z`, `a`, `[IsProper a]` give the proper scheme morphism.
`F : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat Λ))` gives D+.
`I`, `hI`, `hIinj` give a bounded-below termwise injective etale complex.
`eF : ι.obj F ≅ Q.obj I` means that I represents F; an isomorphism allows every
representative, including ones not definitionally equal to F. `J`, `hJ`, `hJinj`
give the corresponding pro-etale injective complex. `j` has domain the actual
termwise comparison inverse image of I; `hj : QuasiIso j` is its resolution map.
No finiteness, torsion, affine, nonempty or common-bound assumption is added.

Canonical normalization: `torsionStalkEtaleResolutionIso` and its pro-etale
counterpart use the existing `rightDerivedFunctorObjQIso` (the inverse derived
unit on a K-injective complex) and the terminal-evaluation isomorphism
`Sheaf.ΓNatIsoSheafSections`. K-injectivity follows from the actual boundedness
and injectivity hypotheses via `CochainComplex.isKInjective_of_injective`.
`torsionStalkResolutionTargetIso` additionally composes exact comparison-pullback
localization compatibility, eF, and `asIso (Q.map j)`. Thus no arbitrary map,
Nonempty choice, or assumed equality is used to force the conclusion.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`:
  `AlgebraicGeometry.ProEtale.comparisonSectionComplexes`,
  `comparisonResolutionSections`, `boundedBelowComparisonGlobalSections`.
  Its published `comparisonResolutionUnit` supplies the actual comparison unit.
- `WeilConjectures.SixFunctors.ProEtale.Comparison` (transitively imported):
  the fixed mate `Functor.rightDerivedFunctorPlusBaseChange` of
  `AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange` (the hom
  of the recorded `rightDerivedLowerStarComparisonPlusIso`). Current server
  source of the recorded extracted comparison module was also read with
  `scompile.py --source`; the mate definition agrees exactly.
- `WeilConjectures.SixFunctors.Etale.Derived.GlobalSections`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections`:
  `AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso` and
  `AlgebraicGeometry.Scheme.ProEt.isTerminalMkId`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `CategoryTheory.Functor.rightDerivedFunctorObjQIso`.
- Mathlib `CategoryTheory.Functor.mapDerivedCategoryFactors`,
  `CochainComplex.isKInjective_of_injective`, `DerivedCategory.Q`,
  `Sheaf.ΓNatIsoSheafSections`, `NatIso.mapHomologicalComplex`;
  recorded K-injective dependency `CochainComplex.IsKInjective.Qh_map_bijective`
  and `DerivedCategory.Plus.Qh_map_bijective_of_isKInjective` support the proof plan.

Edge cases checked: empty Z; identity a; zero or infinite Λ; zero complexes;
arbitrary integer lower bounds, different bounds for I and J; arbitrary
isomorphic representatives of F, including automorphisms of a representative.
The target isomorphism transports Q(j) together with eF, so changing either
representative is accounted for in the independence clause. The source's
properness is retained although the map constructions exist more generally.

Searches (2026-10-17):

- `msearch.py ... leanfinder "Sections of the fixed derived etale proetale direct
  image comparison at an algebraically closed point equal the injective resolution
  global cohomology comparison"`: eight hits, headed by
  `AlgebraicGeometry.Scheme.Γevaluation_naturality`; no matching theorem.
- `msearch.py ... loogle '"rightDerivedFunctorPlusBaseChange"'`: zero hits.
- `msearch.py ... grep 'rightDerivedFunctorPlusBaseChange|proetale'
  Algebra/Homology/DerivedCategory`: zero hits.
- `rg` for `comparisonResolutionSections` in `lean/Sheaf` found the existing
  definition in BoundedBelowProEtaleComparison; it is reused. `rg` for
  `rightDerivedFunctorObjQIso` in upstream found the canonical construction in
  RightDerivedFunctor/KInjective, which is reused. Searches for the new helper
  names and the node id in upstream found no declaration of this full statement.

Validation: `scompile.py Q129 lem-pbc-torsion-stalk-proetale-resolution-map`
compiled both delivered modules individually in dependency order, with no errors
or non-sorry warnings. The dependency import diff was independently checked
against the current server source and changes only imports and one wrapped line.

No natural-language statement correction or new node is needed: the original
node already requests precisely these equalities, naturality and independence.
All new helper definitions contain real data. The sole theorem of the main
module has `sorry`, with the complete seven-step mathematical proof in its
docstring. The old three copied definitions and both automatic conjuncts are removed.

## Dependency modules

`sk-prop-sf-comparison`: dependency module
`Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison` is retained with its
published declarations and statements. Its old direct imports of retired
ProEtale modules collided with the current FiniteCoefficient framework, giving
"environment already contains" for `rightDerivedLowerShriekOfCompactification`
and `upperStarIsoLowerStarInv`. The seven affected imports now use the published
FiniteCoefficient module paths. This is an import-only §1(B) repair, recorded in
lean.note. It neither copies the comparison helpers into the main module nor
changes their mathematical definitions or any dependency theorem statement.

## Second reading by Q129

I reopened the node, the source proof (3), the returned diagnosis and the revised
Lean file. The saved report's assertion of agreement was wrong: invertibility
of an iso and naturality on site objects did not identify beta with the displayed
map. Those clauses and the three duplicate definitions are gone.

The first equality now contains beta itself inside the defined point-section
composite. The resolution side contains Q of the exact published cochain map,
not another transformation with the same endpoints. Its source iso uses eF and
the inverse derived section unit on I; its target iso uses exact pullback
compatibility, eF, Q(j), and the inverse section unit on J. The second equality
names the published canonical global comparison. I checked the last two clauses
quantify arbitrary derived morphisms and arbitrary second I', J', eF', j'.
In particular neither is the naturality field of comparisonResolutionSections.
All original hypotheses are represented, including properness and arbitrary
coefficients. I replaced the earlier equality-only representative with an
isomorphism to include every resolution representing F. There is no additional
assumption that A_Z I is injective or acyclic. The proof docstring follows the
restriction mate, derived units at I and J, exact point sections, derived
comparison unit, and K-injective Hom-bijection in the node's seven proof steps.
