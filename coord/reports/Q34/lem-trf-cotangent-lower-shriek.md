## Worker report

Module: `Sheaf.RingTheory.CotangentLowerShriek`.
Main declaration: `Algebra.CotangentSites.lowerShriekData_nonempty`.
This states existence of the complete specified projection/counit/comparison system;
its only postponed theorem is this declaration, with proof `sorry`. The auxiliary
records expand its conclusion. No definition selects data from this theorem or
from the bar-system existence theorem. No statement correction or dependency repair.

The node's own polynomial-presentation categories and canonical maps had no existing
implementation. The helper declarations here implement those constructions in the
owning node's module, as allowed by the human's missing-helper instruction. They do
not introduce an independent mathematical prerequisite or duplicate a DAG notion.

Clause-by-clause translation (all names below are in `Algebra.CotangentSites`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary commutative rings and maps `A → B → C` | `{A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)`; no flatness, finiteness, nonzero or characteristic assumptions. |
| Common size convention and small representatives | Rings and variable sets are in `u`; `AsSmall.{0}` produces genuinely small categories in `u+1` with lifted homs. Coefficient modules are in `u+1`, and the recorded bar instances supply derived localizations in `u+2`. This is the common larger-universe convention; no site object/hom universes are forcibly equated. `AsSmall.equiv` identifies these representatives with the original categories, so no literal skeleton choice affects the assertion. |
| A polynomial algebra, allowing any set of variables | `IsPolynomial f := ∃ (S : Type u) (e : CommRingCat.of (MvPolynomial S A) ≅ P), CommRingCat.ofHom MvPolynomial.C ≫ e.hom = f`. The coefficient equation makes the ring isomorphism an algebra isomorphism. Coordinates are not part of an object or a morphism. |
| Objects and all augmentation-preserving algebra maps of `C_(T/S)` | `Presentations f` is the full subcategory of `Over (Under.mk f)` where the source structural map is polynomial; `Site f` takes its opposite and `AsSmall`. The under-category fixes the base map, the over-category fixes the augmentation, and fullness retains every allowed map. |
| Objects and all commuting pairs of maps of `E` | `Pairs f g` is the full subcategory of `Over (triangle f g)` in `Arrow (Under A)`, with polynomial conditions on `A → P` and `P → Q`. Thus all three squares of a morphism and both augmentation conditions are imposed by the ambient category. `PairSite f g` reverses arrows and makes it small. |
| Identity-cover topology and sheaves = presheaves | Every sheaf type is on `⊥`; `ringSheaf` and `setInverse` use Mathlib's `sheafBotEquivalence`. Module presheaves are `Eᵒᵖ ⥤ ModuleCat R`, as in the recorded bar theorem. |
| Three target categories in the specified order | `target f g` has values `Arrow.mk f`, `Arrow.mk (f ≫ g)`, `Arrow.mk g`, at `0,1,2 : Fin 3`. |
| `u₁(P,Q) = P`, including its base, augmentation and morphisms | `Projections.projection 0`, the natural ring isomorphism `first`, and `firstBase`/`firstAugmentation`. Naturality of `first` fixes the map on all morphisms; full faithfulness of the diagram category fixes the functor up to the displayed canonical identification. |
| `u₂(P,Q) = Q` as an `A`-algebra | `projection 1`, `second`, `secondBase` and `secondAugmentation`. Its codomain consists of polynomial `A`-algebras, so polynomiality of `Q/A` is part of the existence conclusion. |
| `u₃(P,Q) = Q ⊗_P B`, including induced maps | `projection 2`, natural inclusions `tensorQ` and `tensorB`, and `tensorSquare : IsPushout ...` in commutative rings. This is exactly the algebra tensor product, not an arbitrary ring with two maps. `tensorBase` fixes the `B`-algebra structure, and `tensorAugmentation` fixes the map to `C`; the pushout universal property fixes the maps on morphisms. Its target is a polynomial `B`-algebra presentation. |
| Structural presheaves and augmentations | `presentationRing`, `presentationBase`, `presentationAugmentation`; on pairs these are `pairP`, `pairQ`, `pairPQ`, `pairPB`, `pairQC`. Pulling back the third ring is the specified pushout ring. `liftRing` is the literal ring universe transport by `ULift`, with maps `h.hom.ulift`. |
| Geometric inverse image precomposition and direct image its right adjoint | `RingedRestriction.morphism : RingedToposMorphism ...`; `inverse` identifies its inverse image with `setInverse`, which is precomposition through `sheafBotEquivalence`. The existing `RingedToposMorphism.adj` supplies the required geometric adjunction and left exactness, together with the induced module direct image. |
| Identity variable structural map `g⁻¹O = O_i` | `Projections.structural`, using `RingedRestriction.structural`, equates the structural map to the inverse-image identification itself. No scalar-extension comparison is substituted for it. |
| Exact inverse image on modules with pulled-back variable rings | `structuralLeftExact` and `structuralRightExact` assert finite-limit/finite-colimit preservation for the existing literal restriction `PresheafOfModules.pushforward₀`. On the identity topology these are the module-sheaf restriction functors. |
| Additional constant coefficient map `B → C` | The original `g : B ⟶ C`, independent of the quantified coefficient `R`; the variable augmentations are `pairPB` and `pairQC`, and `tensorAugmentation`/the ambient augmentation square fix compatibility with `g`. |
| For every commutative coefficient ring `R`, identity-structural-map `g_i^R` | `LowerShriekData.shriek` quantifies over every `(R : Type (u+1)) [CommRing R]`; each `DerivedRestriction.geometric` is `RingedRestriction` of the constant ring presheaf. |
| Constant point inverse images and `π = π_i g_i` | `(bar.models E R).point` is the recorded `CategoryColimitPoint`, with constant inverse image and identity structural map; its derived adjunction is in `CategoryColimitBarModel.adjunction`. Precomposition of a constant presheaf is the constant presheaf, so these inverse images compose as specified (up to the category encoding's canonical unitors). |
| Sheaves of left modules | Mathlib `ModuleCat`, `PresheafOfModules`, and the dependency's `RingedToposMorphism`/`ringedSiteModules`; no alternative module category. |
| `g_!` is left Kan extension along `u_i^op` | `DerivedRestriction.left` and `adjunction : left ⊣ moduleInverse v R`. A left adjoint to precomposition is precisely this left Kan extension, characterized uniquely up to its adjunction-compatible isomorphism. Its data are existentially asserted, never chosen from a mere existence theorem. |
| Unbounded total left derived functor with canonical counit | `derived`, `comparison`, `universal`, `derivedAdjunction` and `normalization`. The universal property is Mathlib's `IsLeftDerivedFunctor` on all integer cochain complexes. `normalization` fixes the adjunction by its ordinary-complex Hom bijection. |
| All three derived counits are isomorphisms for every degree-zero `K` | `DerivedRestriction.counit` is `IsIso (derivedAdjunction.counit.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj K)))`, for every module presheaf `K`. The right side of the adjunction is the exact descended restriction functor. |
| Canonical derived-colimit comparison is an isomorphism | `LowerShriekData.comparison` is a natural transformation between the two derived-colimit functors on degree-zero presheaves; `comparisonIso` asserts each component is an isomorphism in `DerivedCategory (ModuleCat R)`. |
| Its representative is exactly `(chain,x) ↦ (u_i chain,x)` | `represented` equates the derived component to the bar-model comparison, `DerivedCategory.Q.map (reindex ...)`, and the inverse target model. `reindex` uses the dependency's `CategoryColimitBarSystem.map` with its fixed `formula` and `canonical` laws, with identity scalar restriction removed by `restrictScalarsId`. Thus the element and every vertex are exactly as stated. |
| Naturality in `K` | `comparison` is a `NatTrans`; the counit is the natural transformation in the recorded derived adjunction. |
| Abelian presheaves, `R = ℤ` | Integer-module presheaves are the standard abelian-presheaf encoding. If a ring lies in a smaller universe, use its canonical `ULift` transport in `u+1`; this preserves all elements, maps and formulas. In particular the coefficient case `ULift ℤ` is included without assuming characteristic or nontriviality. |
| Comparisons use constant coefficients, not the variable structural rings | `DerivedRestriction` and `LowerShriekData.comparison` use the independently quantified `R`; `Projections.structural` uses `presentationRing ... ⋙ liftRing`. These are distinct fields and distinct functor categories. |

Dependency declarations read and used:

- `def-weil-size-convention`: its convention-only `lean` record has no declaration;
  the explicit universe levels above implement it.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: its full signature and docstring
  were read. The identity topology here uses the associated existing Mathlib site
  and `sheafBotEquivalence`; no second site/sheaf definition is introduced.
- `Sheaf.CategoryTheory.RingedToposMorphism`,
  `CategoryTheory.RingedToposMorphism`: used literally in `RingedRestriction`,
  including its finite-limit geometric adjunction and specified module direct image.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the general-site `SheafOfModules` category used by that ringed-topos interface;
  constant coefficients are its presheaf realization, as in the bar dependency.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`: the exact existing derived category and localization.
- `Sheaf.CategoryTheory.DerivedColimitBar`,
  `CategoryTheory.CategoryColimitBarSystem`, `CategoryColimitBarModel`,
  `CategoryColimitPoint`, `categoryBarModuleDerived`, `categoryBarPresheafDerived`
  and `categoryColimitBarSystem_exists`: the full module was read, including the
  `formula`, `canonical` and model-normalization fields. The theorem accepts any
  such specified bar system; the dependency already asserts its existence, so this
  parameter adds no mathematical hypothesis on the rings, sites, or presheaves.
- Proof-only import:
  `Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek`,
  `CategoryTheory.continuousCocontinuous_exists_derivedShriek` and its data record
  were read. The two other proof nodes,
  `lem-trf-derived-shriek-comma-homology` and
  `lem-trf-cotangent-lower-shriek-polynomial-top`, currently have no Lean record;
  their complete node statements were read, and no nonexistent module is imported.
  They are proof dependencies only; this delivery does not restate them.

Source checks: read `literature/stacks-project/cotangent.tex`, section-triangle,
equation-three-maps and lemma-triangle-compute-lower-shriek (08QR/08QW).
The main theorem docstring carries all eight DAG proof steps, including the
explicit sections and bar contractions, the tensor-comma identification, the
polynomial-target augmentation, and the canonical-map identification. It retains
the DAG's repaired case `i=2`, rather than the source's invalid arbitrary lift.

Edge cases checked before writing:

- Empty variable set: `S : Type u` has no `Nonempty` or finiteness assumption, so
  the polynomial algebra with zero variables and both section constructions occur.
- Zero rings: `CommRingCat` permits the zero ring; no `Nontrivial` binder occurs.
  The polynomial condition and tensor pushout still have their usual meanings.
- Zero coefficient ring or zero presheaf: the quantified `CommRing R` and `K`
  permit both, and the claims reduce to isomorphisms of zero objects.
- No augmentation-surjectivity assumption: the over-category includes arbitrary
  augmented polynomial algebras, exactly as the node requires.
- No polynomiality or flatness assumption on `C/B`: the third comma argument uses
  the polynomial target object of its site, not polynomiality of the original `C`.
- The counit is stated for degree-zero presheaves, not strengthened to arbitrary
  unbounded `K`; the derived functor itself is unbounded.
- The comparisons are derived-category isomorphisms of the specified maps, not
  merely isomorphisms of individual homology groups.

Searches made on this task:

- `msearch.py ... leanfinder "derived lower shriek counits of polynomial presentation
  sites for composable commutative ring maps"`: eight hits, including generic
  `Adjunction.derived_counit` and sheaf pushforward counits; none gives these sites
  or asserts the three counits are invertible.
- `msearch.py ... loogle '"totalLeftDerivedCounit"'`: two generic total-derived
  functor declarations, not this polynomial-site statement.
- `msearch.py ... grep 'PolynomialPresentation|[Cc]otangent.*[Ss]hriek|[Ll]owerShriek'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "polynomial presentation categories cotangent complex
  derived lower shriek counit isomorphism"`: eight generic restriction/sheaf or
  derived counit hits; no matching statement or polynomial-presentation categories.
- Mathlib `rg 'structure.*Polynomial|def IsPolynomial|class IsPolynomial|abbrev
  IsPolynomial'` in RingTheory: polynomial laws/other unrelated results, no predicate
  for an arbitrary ring map being a polynomial algebra. Existing `MvPolynomial`
  and categorical full/over/under categories are used to express it.
- `rg` in both live `lean/WeilConjectures` and `lean/Sheaf` for polynomial presentation,
  cotangent sites and this node id: no implementation of the four sites or three
  projections. `CotangentTransitivityTriangle` only mentions the node in its proof
  docstring; `CotangentResolutionCoherence` implements a different standard
  simplicial resolution. The node-id grep in `lean/WeilConjectures` had no hits.

## Second reading by Q34

A separate clause-by-clause pass reread the node and the complete generated module.
The dispatcher explicitly forbids starting other agents, so this is a second pass
by the sole worker, not a claim of independent authorship.

The ambient `Over (Under.mk f)` and `Over (triangle f g)` definitions were checked
against every morphism square in the node. The `IsPolynomial` equation was checked
to require preservation of coefficients, not just a ring isomorphism. The tensor
square was checked in commutative rings and together with `tensorBase` and
`tensorAugmentation`, so it determines both the algebra and its augmentation,
including all induced morphisms. The first and second projections retain both
base and augmentation conditions through natural isomorphisms.

This pass found that the first draft explicitly asserted constant-coefficient
exactness but omitted exactness for modules over the variable pulled-back rings.
Added `Projections.structuralLeftExact` and `structuralRightExact` for the canonical
Mathlib restriction functor. It also checked that the bar representative removes
identity scalar restriction on both its coefficient and target-complex sides;
`represented` fixes the actual derived arrow using the existing model isomorphisms.
The normalized adjunction counit is evaluated on the zero-degree single complex.
No other mismatch found; no node statement changed and no hypothesis was added
on the commutative rings, their maps, or the module presheaf.

Validation is by the prescribed `scompile.py` and `deliver2.py` wrappers; the final
compile and dry-run results are recorded below after they complete.

Final validation (2026-10-22 UTC): `scompile.py` compiled both the sandbox module
and its actual library module name cleanly (33.9 s and 34.8 s respectively for
the variable-exactness revision). The final module, with all direct dependency
imports, also compiled in `deliver2.py --no-push`; preflight returned
`OK (dry run): commit 4d306fcbb5e passes the preflight and compiles; nothing pushed`.
Only the node's `lean` field differs from the base; all 28 top-level declarations
are recorded. Additional source checking read sites-cohomology.tex's category-over-
point, morphism-of-categories, lower-shriek-properties, and comma-computation texts
(Tags 08PF, 08PH, 08PC and 08PK).
