## Worker report

The module states `AlgebraicGeometry.Etale.properOpenInterchangeCoherence`, with one
postponed theorem and no new definitions. Source: Stacks Project, more-etale.tex,
Tags 0F7B, 0F7C, 0F7D and 0F7F, read in the local literature source.
The complete eight-step DAG proof is included in the theorem docstring.

Hypothesis and clause correspondence:

- Finite commutative coefficients: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  Schemes are arbitrary `Scheme.{u}` and sheaves use `ModuleCat.{u + 1} Λ`.
- A square is given by `k`, `i`, `r`, `p`, `[IsOpenImmersion k]`,
  `[IsOpenImmersion i]`, `[IsProper r]`, `[IsProper p]`, and
  `h : k ≫ p = r ≫ i`. No Cartesian or quasi-compact-open hypothesis is imposed.
- `γ` is one family of natural isomorphisms
  `rightDerivedLowerStarPlus r ⋙ openImmersionLowerShriek i .mapDerivedCategoryPlus ≅
   openImmersionLowerShriek k .mapDerivedCategoryPlus ⋙ rightDerivedLowerStarPlus p`.
  Thus its naturality and invertibility are part of its type.
- The auxiliary ordinary family `δ` is the canonical proper/open sheaf identification.
  The first conjunct pins it down by equality after the ordinary inclusions
  `openImmersionLowerShriekToLowerStar` into the same `lowerStar (k ≫ p)`;
  `lowerStarComp r i (k ≫ p) h` provides the specified commutativity transport.
  This characterizes the identification on underlying sections, rather than choosing
  an unspecified isomorphism of the sheaf functors.
- The second conjunct is the universal derived-unit form of the stated resolution
  normalization. It applies `NatTrans.mapHomotopyCategoryPlus δ.hom` degreewise,
  then the actual `p_*` right-derived unit; the factors are the canonical
  `mapDerivedCategoryPlusFactorsh` for the exact open extensions. On a bounded-below
  injective representative J the r-unit is invertible, so solving the equation gives
  exactly `i_!r_*J ≅ p_*k_!J → p_*I` for a K-injective replacement `k_!J → I`.
  Naturality extends this computation to any K-injective representative of the same
  D⁺ object (including ones not termwise bounded below). Conversely the specified
  resolution calculation gives this unit equation by an injective replacement of J
  and naturality of the units. Thus this is an equivalent characterization, not an
  assumption that `k_!` preserves injectives or a different choice of comparison.
- The third conjunct specializes `γ j₁ j₂ (𝟙 X) p` and inserts
  `lowerStarIdDerivedPlus.inv`; it equates that map with the recorded
  `properOpenComparison Λ p j₁ j₂ h K`.
- The fourth conjunct is the vertical pasting equation. Both direct-image composition
  transports are `Functor.rightDerivedFunctorPlusCompIso'` applied to the actual
  `lowerStarComp`. The `h` argument merely supplies the consequence of h₁ and h₂
  for the outer square; it imposes no additional geometric condition.
- The fifth conjunct is horizontal pasting, with precisely
  `extensionZeroCompDerivedPlusIso` for the bottom and top composite opens.
- The sixth conjunct handles identity vertical maps using `lowerStarIdDerivedPlus`.
  The seventh handles identity horizontal maps using the localized
  `Adjunction.leftAdjointIdIso` of the actual open-extension adjunction and
  `upperStarId`.
- The final conjunct is the base-change equation. `sp`, `sr`, `si`, `sk` give the
  four Cartesian faces of an arbitrary pullback cube, and `h₁` is the commutativity
  of the pulled-back square. Every such cube is canonically isomorphic to the
  fibre-product base change in the node. Conversely the four faces identify its
  objects with those fibre products. All morphisms `b` are allowed.
  The beta terms are exactly `extensionZeroBaseChangeDerivedPlusIso` for si and sk;
  the exchange terms are `derivedBaseChangeMapPlus (ModuleCat Λ)` for sp and sr,
  the same module exchange used in `exchange_forget_coefficients`.
  Properness and openness of the pulled-back edges are explicitly supplied as
  instances; these always exist by base-change stability, with no extra restriction.

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.lowerStar`.
- `def-weil-pbc-extension-by-zero`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-kinjective-resolutions`: `Sheaf.AlgebraicGeometry.KInjectiveResolutions`, `CochainComplex.IsKInjectiveResolution`.
- `def-weil-pbc-proper-open-comparison`: `Sheaf.AlgebraicGeometry.ProperOpenComparison`, `AlgebraicGeometry.Etale.properOpenComparison`.
- `cor-cbc-derived-extension-zero-base-change`: `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`, `AlgebraicGeometry.Etale.derivedExtensionZeroBaseChange`.
- `lem-weil-pbc-exchange-forget-coefficients`: `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`, `AlgebraicGeometry.Etale.exchange_forget_coefficients`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `lem-weil-pbc-direct-image-preserves-injectives`: `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`, `AlgebraicGeometry.Etale.preservesInjectiveObjects_lowerStar` (repaired existing record; see below).

The first record's torsion predicate is not a category definition; its module supplies
and documents the existing `DerivedCategory.Plus` and constant-coefficient category
encoding used here. The K-injective-resolution record supplies
`CochainComplex.IsKInjectiveResolution` (QuasiIso and IsKInjective); the equivalent
universal-unit normalization avoids binding a particular chosen resolution.
The proper-support theorem is imported for the canonical ordinary identification,
and the acyclicity theorem and all recorded proof-dependency modules are imported
for the stage-3 proof plan. No private replacement of a dependency is introduced.

Edge cases checked: empty schemes and opens, zero complexes, the zero coefficient
ring, identity maps in either direction, non-Cartesian commutative squares, opens
without a quasi-compactness hypothesis, arbitrary base morphisms, and all scheme
universes. The equations remain well-typed in these cases. No nonempty, positive-degree,
nonzero-ring, Noetherian, Cartesian-original-square or characteristic restriction
is added. Explicit universes and all variables are bound.

Searches:

- `msearch.py leanfinder`, query “Proper pushforward and open extension by zero
  interchange for noncartesian squares with composition and base change coherence”:
  eight hits for ordinary pushforward composition (exponentiable maps and scheme
  modules); none gives this statement.
- `msearch.py loogle`, query `"openImmersionLowerShriek", "lowerStar"`: no hits.
- `msearch.py grep`, query `properOpenInterchange|proper_open_interchange|proper.*interchange`:
  no hits.
- `rg` in upstream `WeilConjectures/SixFunctors` and side `lean/Sheaf/AlgebraicGeometry`,
  query `properOpen|properSupport|interchange`: found
  `openImmersionLowerShriekLowerStarExchange`, read in full. That declaration assumes
  a Cartesian square and works on unbounded categories; its invertibility theorem
  does not state the non-Cartesian coherence package here. The proper-open refinement
  construction is the recorded dependency, not this general result.
- `rg` for the item id in upstream WeilConjectures: no hits.
- DAG inspection of `lem-weil-pbc-etale-open-proper-interchange`: it is a downstream
  Cartesian, quasi-compact-open specialization explicitly depending on this node,
  not an available duplicate or a prerequisite.

No statement correction, new nodes, or statement dispute. One stale dependency record is repaired below.
Validation: final module compiles cleanly through scompile.py (15.8 s sandbox,
16.7 s library), with no errors or warnings. Delivery dry run is the final check.

## Dependency modules

`lem-weil-pbc-direct-image-preserves-injectives` receives an existing-declaration
repair only; no dependency module is delivered. Its old declaration
`AlgebraicGeometry.Etale.preservesInjectiveObjects_lowerStar_of_abelian` is absent
from both pinned and current server sources (`scompile.py --source`). The existing
global instance is `AlgebraicGeometry.Etale.preservesInjectiveObjects_lowerStar` in
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`, read in full.
Its coefficient category A has `Category.{u+1}`, `Abelian`,
`IsGrothendieckAbelian.{u+1}` and `HasSmallSiteSheafify`; its only geometric data
are schemes X,Y and any f : X ⟶ Y. The conclusion is exactly
`(lowerStar A f).PreservesInjectiveObjects`. Specialize A to
`ModuleCat.{u+1} Λ` for the node's module clause and `AddCommGrpCat.{u+1}` for its
abelian clause. All coefficient assumptions are existing instances, and there are
no properness, finiteness or additional size restrictions. This existing instance
is defined by `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
applied to the existing exact `upperStarLowerStarAdjunction`.

The main statement publicly imports that smaller instance module so its canonical
derived compositors elaborate. The main node adds this already recorded node to
stmt_deps because preservation of injectives is needed to type those compositors.
The dependency's node changes only in lean; no proof or statement is changed.


## Second reading by NN

Independent second reading, 2026-10-15. I opened the node, delivered Lean, all
statement-dependency nodes and their declaration sources, and more-etale.tex at
lemma-shriek-proper-and-open (0F7B), lemma-shriek-proper-and-open-compose (0F7C),
lemma-shriek-proper-and-open-compose-horizontal (0F7D), and
lemma-shriek-proper-and-open-base-change (0F7F). The enclosing section imposes no
standing Noetherian, quasi-compact-open, Cartesian-square or characteristic
hypothesis. The source's separated locally quasi-finite maps and torsion-ring
case specialize to the open immersions and finite commutative ring in this node.

Node checklist and Lean correspondence:

1. Finite commutative coefficients: `Λ : Type (u + 1)`, `[CommRing Λ]`,
   `[Finite Λ]`. Exact. The category is the recorded constant-coefficient
   `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and its
   `DerivedCategory.Plus`. I opened DerivedCategories and Mathlib's
   DerivedCategory/TStructure: Plus means bounded below in cohomology, as required.
2. Four schemes and the displayed arrows: `{A B C D : Scheme.{u}}`,
   `k : A ⟶ B`, `i : C ⟶ D`, `r : A ⟶ C`, `p : B ⟶ D`. Exact endpoints.
3. Open horizontal maps, proper vertical maps and commutativity:
   `[IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]`
   and `h : k ≫ p = r ≫ i`. Exact. I read the actual Mathlib definitions.
   No Cartesian condition is imposed on the original square.
4. One canonical natural isomorphism for all squares and all K: the single
   existential family `γ` has type `Rr_* ⋙ i_! ≅ k_! ⋙ Rp_*`, using
   `rightDerivedLowerStarPlus` and `mapDerivedCategoryPlus` of the recorded
   functors. Exact. Naturality and invertibility are built into `≅`, and all
   following equations concern this same family, not independently chosen maps.
5. Canonical ordinary comparison: `δ` and the first conjunct identify its map
   after the inclusions `openImmersionLowerShriekToLowerStar` into the same
   `lowerStar (k ≫ p)`, with `lowerStarComp ... r i (k ≫ p) h` transporting
   commutativity. Exact. I read both comparison constructions: this is equality
   of the same sections, as in 0F7B, so it excludes arbitrary abstract isomorphisms.
6. K-injective representative normalization: the second conjunct says
   `i_!(η_r,J) ≫ γ(Qh J) = factors_i ≫ Qh(δ_J) ≫ η_p,k!J ≫ Rp_*(factors_k⁻¹)`.
   Exact equivalent formulation. The units are Mathlib's actual
   `rightDerivedFunctorPlusUnit`, and the factors are its canonical exact-functor
   localization comparisons. For bounded-below injective J, η_r is invertible;
   η_p is computed by p_* of a resolution k_!J → I. Solving the equation gives
   exactly i_!r_*J → p_*k_!J → p_*I. Conversely, naturality along an injective
   replacement proves this unit equation for every bounded-below homotopy object.
   I checked HomotopyCategory/Plus: its representatives are termwise bounded
   below. The statement still determines the requested calculation for every
   K-injective representative of a D⁺ object, even one not termwise bounded
   below: it is homotopy equivalent to a bounded-below injective representative,
   by full faithfulness of localization into K-injectives. Additive functors
   preserve that homotopy equivalence and the resolution homotopies. No claim
   that k_! preserves injectives, or arbitrary comparison map, is introduced.
7. Refinement case α_u: the third conjunct precomposes `γ j₁ j₂ (𝟙 X) p`
   by i_! of `lowerStarIdDerivedPlus.inv` and equates it with
   `properOpenComparison Λ p j₁ j₂ h K`. Exact. I opened ProperOpenComparison:
   its definition is j₂! of θ inverse followed by the descended counit, and θ
   uses the required restriction, base-change and clopen component comparisons.
8. Vertical composition: the fourth conjunct uses the left compositor hom,
   outer γ, then the right compositor inverse, equating them with γ₂ at Rr₁_*K
   followed by Rp₂_*γ₁. Exact direction and order. Both compositors are
   `rightDerivedFunctorPlusCompIso'` applied to `lowerStarComp`. The binder h
   for the outer square follows from h₁,h₂ and adds no geometric hypothesis.
9. Horizontal composition: the fifth conjunct uses
   `extensionZeroCompDerivedPlusIso Λ i j`, outer γ and the inverse compositor
   for k,l; the other side is j_!γ₁ followed by γ₂ at k_!K. Exact. I opened the
   dependency: its compositor is the localization of the actual ordinary
   `openImmersionLowerShriekComp`.
10. Identity vertical maps: `γ k k (𝟙 A) (𝟙 B)` and the two
    `lowerStarIdDerivedPlus` maps in the sixth conjunct give exactly the
    identity comparison after the canonical identity transports.
11. Identity horizontal maps: `γ (𝟙 A) (𝟙 C) r r` in the seventh conjunct
    uses the localized `Adjunction.leftAdjointIdIso` of the actual open
    adjunction and `upperStarId`. Exactly the identity on derived direct image.
12. Arbitrary base change: the final conjunct binds a,b,c,d and the pulled-back
    edges. `sp`, `si`, `sr`, `sk` give the four Cartesian faces, h₁ gives the
    pulled-back square, and b is unrestricted. These faces encode exactly a
    fibre-product base-change cube, up to its unique projection-compatible
    isomorphism; pasting gives its outer A₁-to-D₁ pullback face. The equation
    is b*γ then Ex_p then Rp₁_*β_k equals β_i then i₁!Ex_r then γ₁ at d*K.
    Exact order and endpoints. β is precisely the recorded
    `extensionZeroBaseChangeDerivedPlusIso`; Ex is precisely the
    `derivedBaseChangeMapPlus (ModuleCat Λ)` used in ExchangeForgetCoefficients,
    whose signature I opened. The supplied open/proper instances on the
    pulled-back edges always exist by stability under base change.

Dependency repair checked independently: the existing instance
`AlgebraicGeometry.Etale.preservesInjectiveObjects_lowerStar` in
SixFunctors/BaseChange/DerivedPasting/Vertical has an arbitrary morphism f and
Grothendieck abelian coefficient category A with small-site sheafification. Its
conclusion is exactly `(lowerStar A f).PreservesInjectiveObjects`, via the exact
inverse-image adjunction. Specialization to ModuleCat Λ and AddCommGrpCat gives
both clauses of lem-weil-pbc-direct-image-preserves-injectives; all coefficient
assumptions are existing instances. The repaired record points to this actual
instance. There are no new definition nodes or dependency modules to audit.

Edge cases: empty schemes and empty opens, zero sheaves and complexes, the zero
ring, and identities in both directions are admitted. There is no nonempty index,
positive degree, nonzero ring, characteristic-invertibility, Noetherian or
quasi-compact-open assumption. Degree zero is covered. The universe u is explicit
and unrestricted; the coefficient universe is the existing site convention.
Every finite coefficient ring can be placed in that universe, so no finite ring
is excluded. All variables are explicitly bound.

Independent searches, with queries different from the worker's:

- msearch.py LeanFinder: "Canonical interchange between proper pushforward and
  extension by zero of an open immersion, coherent under composition and
  pullback" gave eight ordinary restriction/open-immersion composition hits;
  none states the node.
- msearch.py Loogle: `"openImmersionLowerShriekToLowerStar"` gave no hits.
- msearch.py LeanSearch: "Extension by zero along open immersions commutes with
  proper direct image in bounded below derived categories, with composition and
  base change compatibility" returned Internal Server Error. Recorded as
  unavailable; other searches provide the duplicate check.
- msearch.py grep:
  `proper.{0,40}open.{0,40}(exchange|interchange)|shriek.{0,40}proper|properOpenInterchange`
  gave no Mathlib hits.
- Direct rg in upstream WeilConjectures, Mathlib CategoryTheory and project
  lean/Sheaf/AlgebraicGeometry for `properOpen`, `interchange` and
  `LowerShriekLowerStarExchange` located the upstream exchange. I opened its
  full definition and invertibility theorem: they require `IsPullback`, use
  unbounded categories and do not supply this non-Cartesian coherence package.
  ProperOpenComparisonComposition supplies only the refinement specialization.
  Neither is a duplicate. Searches of the upstream name table and all
  upstream/project sources for this declaration and node id found no occurrence.

Findings and changes: no mathematical or interface mismatch. The Lean module and
both node copies remain unchanged; this independent review was appended to the
report. The module has one named theorem whose whole proof is sorry, no new data
definitions, no private copies and no hollow hypotheses. The docstring carries
all eight node proof steps, source and blueprint tag; every Lean line has at most
100 characters. The node's lean.statement is the verbatim source signature and
matches the project's signature reader after its whitespace normalization.

Validation: scompile.py compiled this sole delivered module separately as sandbox
and library (16.3 s and 16.7 s), with no errors or warnings. deliver2.py checks the
existing-declaration probes and delivery preflight as part of the final dry run.
