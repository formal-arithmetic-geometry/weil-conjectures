## Worker report

The delivery states `lem-weil-stratum-ambient-hom` in
`Sheaf.Paper.StratumAmbientHom`, with one theorem for each of the two sites:
`AlgebraicGeometry.Etale.nonempty_stratumAmbientHomIso` and
`AlgebraicGeometry.ProEtale.nonempty_stratumAmbientHomIso`.
Both are `sorry` statements. Definitions and structural instances have real data.
The blueprint source at order 2069 was read, including its proof, through the server
literature copy. The node already supplies the Noetherian hypothesis needed on the
pro-etale side; no statement correction is made.

Hypotheses and clauses, individually:

- Finite commutative coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`
  in the etale presentation, and `(A : Type u) [CommRing A] [Finite A]` in the
  intrinsic pro-etale presentation, following the respective recorded site conventions.
  The latter uses the recorded `ULift` in `proEtaleConstantRing`, not an extra coefficient.
- Schemes and immersion: `{S U X : Scheme.{u}}`, `(i : S ⟶ U) [IsClosedImmersion i]`,
  `(j : U ⟶ X) [IsOpenImmersion j]`. The immersion is the composite `i ≫ j`.
  Quantification over all such `i,j,U` renders either allowed factorization. No
  separate chosen immersion or equality hypothesis is required.
- Site choice: the two declarations respectively use `Etale.DerivedCategoryModule`
  and `Scheme.proEtaleDerivedCategory`. These are the recorded ordinary derived
  categories; there is no bounded, constructible, or completed subcategory.
- Pro-etale Noetherianity: `[IsNoetherian X]` appears only in the pro-etale theorem.
  This class includes local Noetherianity and quasi-compactness. It is not replaced
  by an assumption that schemes have finite type over a field.
- Constant-ring modules: etale uses the upstream fixed-scalar ModuleCat-valued
  sheaf presentation, already used by `def-weil-pbc-derived-categories`; pro-etale
  uses exactly the intrinsic `proEtaleRingModules T (proEtaleConstantRing T A)`
  underlying `proEtaleDerivedCategory`, retaining the small site's separate universes.
- `Rs_! = j_! Ri_*`: on the etale side this is
  `(Etale.lowerStar (ModuleCat A) i).rightDerivedFunctor ⋙
  (Etale.openImmersionLowerShriek (ModuleCat A) j).mapDerivedCategory`.
  On the pro-etale side it is
  `(sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
  (sfIntrinsicExtensionByZero j A).mapDerivedCategory`.
  The latter is the recorded extension-by-zero definition unchanged, with its
  exactness and additivity instances imported from the published
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact` module.
- `Rs^! = Ri^! j^{-1}`: etale composes the exact open
  `(Etale.upperStar (ModuleCat A) j).mapDerivedCategory` with the right adjoint
  `.rightDerivedFunctor.rightAdjoint` of closed direct image, using the recorded
  ambient adjoint instance. Pro-etale composes the exact canonical constant-module
  open pullback with `(sfIntrinsicClosedUpperShriek i v A).rightDerivedFunctor`.
  Here `v` is the explicit canonical open immersion with range complementary to
  `Set.range i`; the dependency theorem identifies exactly this functor as the
  ambient right adjoint, with no hypotheses on its values.
- Ordinary `Rs_*`: the final functor is `.rightDerivedFunctor` of direct image along
  `i ≫ j`, not a shriek, restricted, or completed direct image. The published
  total-derived implementation uses K-injective resolutions.
- Internal Hom: etale uses the recorded upstream `Etale.derivedHom`, the right
  adjoint to the derived tensor product; pro-etale uses the dependency's
  `derivedInternalHomOfUniverses.{u + 1, u, u}` on the actual constant ring sheaf.
- All `P,M` and naturality: `Nonempty (F ≅ G)` is a natural isomorphism of functors
  with source `D(S,A)ᵒᵖ × D(X,A)`. The left functor is the product of `(Rs_!).op`
  with the identity followed by uncurried derived Hom. The right functor is the
  product of the identity with `Rs^!`, followed by uncurried derived Hom and
  `Rs_*`. Thus every object and every morphism is covered, contravariantly in `P`
  and covariantly in `M`; an objectwise existence statement would have been weaker.
- No boundedness, constructibility, Tor-amplitude, preservation, or biduality
  assumption occurs in either declaration. There are no predicate arguments on
  `P` or `M` at all. Both full natural-language proof plans are in the docstrings.

The canonical pro-etale helper abbreviations introduce no alternative operations:
they specialize the published `proEtaleRingModulePullback`,
`proEtaleRingModuleDirectImage`, and uniquely tensor-unit-normalized
`proEtaleRingModuleAdjunction` to the recorded constant rings. The isomorphism
`sfConstantCoefficientIso` is `asIso` of the actual
`proEtaleCoefficientInverseImageMap`; its invertibility is the recorded constant
coefficient theorem, with the finite coefficient temporarily equipped with the
discrete topology. No topological hypothesis is imposed on the statement, and no
map, inverse image, or adjunction is selected from a bare existence assertion.

Dependency declarations read and used (statement dependencies):

- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlat`, `CochainComplex.IsKFlatIndependentCoefficients`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `def-weil-pbc-proetale-site`: `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-pbc-extension-by-zero`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `def-weil-extension-by-zero`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`, `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`.
- `lem-weil-extension-by-zero-exact`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`, `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero_exact` and its three published instances `sfIntrinsicExtensionByZero_additive`, `sfIntrinsicExtensionByZero_preservesFiniteLimits`, `sfIntrinsicExtensionByZero_preservesFiniteColimits`.
- `lem-exc-closed-ambient`: `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`, `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `lem-exc-proetale-closed-support`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient`, `AlgebraicGeometry.Scheme.sfIntrinsicClosedAmbientAdjunction`.
- `lem-weil-pbc-site-derived-tensor-descent`: `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`, `SheafOfModules.site_derived_tensor_descent`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, `CategoryTheory.derivedInternalHomOfUniverses`.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.lowerStar`.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`.
- `prop-pur-kinjective-resolutions-exist`: `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`, `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `lem-weil-pbc-kinjective-total-derived`: `Sheaf.CategoryTheory.KInjectiveTotalDerived`, `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
- `def-exc-proetale-sections-with-support`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport`, `AlgebraicGeometry.Scheme.sfIntrinsicClosedUpperShriek`.

Proof dependencies with usable modules are imported privately. In particular the
K-flat resolution, tensor descent, K-injective Hom complex, Hom/tensor totalization,
RHom/global sections, ringed open-closed localization, extension by zero, canonical
tensor pullback and ringed slice tensor statements remain available to stage 3.
The legacy `WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriekProjection`
module cannot coexist with the recorded finite-coefficient pro-etale modules: the
import probe and server confirmation report duplicate `lowerStarComp` declarations.
Following the launcher's explicit duplicate-import repair instruction, it is omitted;
the imported `RingedSliceExtensionTensor`, K-flat resolution and tensor descent
modules provide the proof route described in the node. The same conflict prevents
importing the legacy closed-immersion fully-faithful module into the new intrinsic
closed-support module; the compatible ringed open-closed theorem is imported instead.
Unstated proof prerequisites are not hypotheses or assumed results in these statements.

Edge cases checked before writing: the zero coefficient ring is admitted (no
`Nontrivial A`); empty schemes and empty or full closed strata are admitted; identity
closed/open immersions give the expected tensor-Hom/direct-image identities; neither
immersion need be proper, nonempty, strict, or a nonidentity map; arbitrary unbounded
complexes, including zero and complexes unbounded in either direction, remain objects
of the quantified categories. Non-Noetherian etale targets remain allowed. On the
pro-etale side Noetherianity is only that of `X`; the open `U` and its complement
inherit the required properties rather than becoming extra assumptions. All universes
and variables are explicit and auto-implicit variables are disabled.

Searches: LeanFinder query “Derived internal Hom from extension by zero along a
locally closed immersion equals derived direct image of internal Hom into exceptional
inverse image” returned generic scheme module restriction/pushforward adjunctions,
not the assertion. Loogle query `MonoidalClosed, Functor.rightAdjoint, Adjunction`
returned no result (unknown `MonoidalClosed`). Mathlib grep `internalHom|ihom` in
`CategoryTheory/Monoidal` returned generic internal-Hom declarations, not the stratum
identity. `rg` searches for internal Hom, shriek and stratum declarations in upstream
`WeilConjectures` and project `lean/Sheaf`, and a literal item-id search in upstream,
found the component operations but no existing theorem with this bifunctor statement.
Dependency source modules were inspected locally and through `scompile.py --source`
when missing from the old upstream checkout. The item search output is retained in
`searches.jsonl`. Searches for support find the existing DAG definition, so no new
independent notion node is introduced.

No STATEMENT-DISPUTED flag or source-statement fault was found. Only the item's `lean`
and the addition of the already recorded support-definition and intrinsic exactness
nodes to `stmt_deps` change; the other two node copies change only in `lean`.

## Dependency modules

The recorded extension-by-zero definition and its exactness interface are both
usable in the published library. This delivery imports
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact` and reuses its
instances directly. It supplies no replacement extension-by-zero module or node record.
The corresponding landed node `lem-weil-extension-by-zero-exact` is added to the
item's statement dependencies because these instances elaborate its derived functor.

`def-exc-proetale-sections-with-support`: its record gives legacy fixed-scalar names
without a module or primary declaration, and that legacy module duplicates declarations
from the required finite-coefficient framework. The intrinsic module constructs
`sfIntrinsicSectionsWithSupport` as the kernel of the actual adjunction unit, with
`kernel.map` on morphisms and functor laws from uniqueness; then
`sfIntrinsicClosedUpperShriek` is exactly this kernel followed by closed inverse image.
The canonical coefficient map and specialized operations are helpers of this same
construction, and are all listed in the node's declarations. Finite commutative rings,
all module sheaves, and maps of kernels followed by pullback render every clause of
the dependency statement. The formula is defined even without closed/open hypotheses;
it specializes to the stated situation and asserts no adjunction or constructibility.

`lem-exc-proetale-closed-support`: this genuine prerequisite has no Lean record, so the
human's 2026-10-16 “unstated dependencies are yours to state” instruction requires its
statement in this delivery. Its theorem quantifies a finite commutative ring,
Noetherian `T`, a closed `i`, open `j`, and `IsCompl` of their ranges. The direct-image
functor is left exact by its published construction; `PreservesFiniteColimits` records
its exactness so its right derived functor is the termwise functor in the node. The
`Nonempty` adjunction has exactly this left side and the total right derived functor
of `sfIntrinsicClosedUpperShriek` as right side. It is on the entire unbounded
categories and asserts no boundedness or constructibility. The four-step proof in
its docstring follows the node: quasi-compact complementary open and ringed
localization; unique kernel factorization and the sheaf adjunction; preservation of
K-injectives; termwise adjunction and the two K-injective Hom comparisons. Its own
statement does not require its unstated proof lemmas to be proved at stage 2.

## Repair of return L (immutable head f810d2b7af9b)

The returned delivery repeated three declarations already owned by the published
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact` module:
`AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero_additive`,
`AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero_preservesFiniteLimits`, and
`AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero_preservesFiniteColimits`.
I inspected the complete live sources of both intrinsic extension-by-zero modules
using `scompile.py --source`. Their signatures concern exactly the same functor,
finite ring, and open immersion. The exactness module derives all three instances
from the recorded `sfIntrinsicExtensionByZero_exact` theorem.

Removed the sandbox replacement `ProEtaleIntrinsicExtensionByZero.lean` and its
`def-weil-extension-by-zero` node copy, so neither definition nor any of these
instances is redeclared. The main module now publicly imports the existing
`ProEtaleIntrinsicExtensionByZeroExact` module. The already landed node
`lem-weil-extension-by-zero-exact` is cited in `stmt_deps`. The two theorem signatures,
all definition data, and all mathematical node statements are unchanged.

The delivered files are now the main module, the intrinsic closed-support definition,
and the intrinsic closed-ambient theorem, with their three matching node records.
The original independent reading below predates this repair; its remarks on added
extension-by-zero instances and four delivered modules describe the returned version.
The next reader should check this import reuse and the removal of the redundant files.

Validation for the repair uses `scompile.py Q29 lem-weil-stratum-ambient-hom`
on all three delivered files, then
`deliver2.py Q29 lem-weil-stratum-ambient-hom --no-push`, which repeats the separate
file checks and runs the current server preflight. The dry-run output is retained in
`scratchpad/repair-dry-run.log`. Static checks confirm verbatim node signatures,
100-character Lean lines, and no declarations of the three colliding instance names
anywhere in the delivered modules. A source DAG traversal found no path from the
added exactness dependency back to the item (318 dependency nodes visited).

## Earlier second reading (a previous round; superseded)

I independently read the item node, its source at blueprint order 2069 and the enclosing
unit, the four delivered modules, and the statement-dependency records and declarations.
I also read the source nodes at orders 1858 and 1859, the canonical module-adjunction
normalization, the intrinsic coefficient realization, and Stacks `proetale.tex`
(09BM, closed exactness; 09AH, localization) and `sites-cohomology.tex`
(08FJ, open adjunction; 0GL1, projection formula; 08J9, internal Hom).
The source supplies ambient ordinary derived categories and naturality; the enclosing
unit explains the Noetherian scope retained by the node on the pro-etale side.
The node already records this scope explicitly; no statement correction is needed.

Here is my object/hypothesis/conclusion checklist against the node, in its order.

| Node item | Lean rendering and verdict |
| --- | --- |
| A finite commutative ring | Both theorems bind `A`, `[CommRing A]`, `[Finite A]`. Pass; neither assumes `Nontrivial A`. |
| An immersion with a chosen closed-then-open factorization | `{S U X : Scheme.{u}}`, `i : S ⟶ U` with `[IsClosedImmersion i]`, then `j : U ⟶ X` with `[IsOpenImmersion j]`. The immersion is `i ≫ j`. Pass; no extra chosen map or equality is needed. |
| Either finite-coefficient small site | Separate `Etale.nonempty_stratumAmbientHomIso` and `ProEtale.nonempty_stratumAmbientHomIso`. Pass; they assert both choices, rather than just one. |
| Noetherian X only for pro-etale | `[IsNoetherian X]` only in the second theorem. Mathlib's class extends `IsLocallyNoetherian X` and `CompactSpace X`. Pass; no field, characteristic, finite type, or separatedness hypothesis is added. |
| Ordinary unbounded D(T,A) | Étale uses `Etale.DerivedCategoryModule A T`, the recorded `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat A))`; pro-etale uses precisely `proEtaleDerivedCategory T A`. Pass; neither category restricts its objects. |
| The actual constant coefficient ring | Étale uses the recorded fixed-scalar presentation. Pro-etale uses `proEtaleConstantRing T A`, which sheafifies the constant commutative ring `ULift A`, exactly as in `proEtaleDerivedCategory`. Pass. |
| Rs! = j! Ri* | The left product functor uses `lowerStar i |>.rightDerivedFunctor` then `openImmersionLowerShriek j |>.mapDerivedCategory`, or the corresponding intrinsic constant-module functors. Pass; the order is closed direct image followed by open extension. |
| Rs^! = Ri^! j inverse | The right product functor first applies exact open pullback, then the ambient closed right adjoint. Étale uses `.rightAdjoint` from the recorded ambient-adjoint instance. Pro-etale uses the right derived functor of `sfIntrinsicClosedUpperShriek i v A`. Pass. |
| The complementary open used to specify closed i^! | The explicit `Scheme.Opens.ι` has open set `(Set.range i)ᶜ`, whose openness follows from `IsClosedImmersion.isClosedEmbedding`. Pass; it is the canonical complement in U, not an additional hypothesis or arbitrary choice. |
| Ordinary Rs* computed on K-injectives | The last functor is the total `.rightDerivedFunctor` of ordinary direct image along `i ≫ j`. Pass; it is not extension by zero or a restricted direct image. |
| Internal Hom on X and on S | `Functor.uncurry.obj (Etale.derivedHom ... T)` and `derivedInternalHomOfUniverses (ProEt.topology T) (proEtaleConstantRing T A)` use exactly the two recorded presentations. I opened their definitions: the first is the internal Hom of derived tensor, the second localizes the Hom complex with K-injective replacement. Pass. |
| RHom_X(Rs! P,M) is isomorphic to Rs* RHom_S(P,Rs^! M) | The two sides of the functor isomorphism are exactly these composites. Pass; the RHS Hom is on S before applying Rs*. |
| All P,M, contravariant/covariant naturality | `Nonempty (F ≅ G)` quantifies an actual natural isomorphism over `D(S,A)ᵒᵖ × D(X,A)`. The left first-variable functor is `(Rs!).op`; the right first-variable functor is identity; the second variables are identity and `Rs^!`, respectively. Pass; this covers every object and morphism. |
| No bounds, constructibility, Tor, preservation, or biduality assumptions | There is no predicate on either derived object and no such instance binder. Pass. |
| Either allowed factorization | Both theorems quantify every intermediate U and every closed i and open j. Pass; no restriction selects a particular factorization. |

I checked the dependency declarations themselves, not just their names. The closed/open
immersion classes and small topologies are Mathlib's. `DerivedCategories` documents and
imports the unbounded fixed-scalar category, even though its primary new declaration
is the unrelated torsion predicate; that predicate is not imposed here. The generalized
internal Hom and K-injective resolution interfaces retain independent site universes.
The other recorded K-flat, tensor-descent, and total-derived statements supply proof
interfaces and introduce no hidden assumptions in the item signature.

All three dependency modules were also read against their nodes:

- `def-weil-extension-by-zero`: the original two definitions and their data are unchanged.
  The realization is the equivalence of the canonical associated-module-sheaf functor,
  whose scalar map is the constant sheafification unit. Conjugating the published open
  extension by this equivalence gives precisely the node's sheafified extension and
  maps. The three added instances only expose its additivity and exactness. They are
  structural constructions from existing instances, not newly postponed theorems.
- `def-exc-proetale-sections-with-support`: `sfIntrinsicSectionsWithSupport.obj` is
  literally `kernel ((sfConstantModuleAdjunction j A).unit.app N)`; `.map` is
  `kernel.map` with the naturality square. `sfIntrinsicClosedUpperShriek` composes this
  kernel functor with closed inverse image. Pass on both objects and morphisms.
  Its more general definition for arbitrary maps does not assert any extra property.
  `sfConstantCoefficientIso` is `asIso` of the recorded constant-section map, using
  its published invertibility theorem. The pullback/direct-image abbreviations merely
  specialize the published ringed functors to that map. The adjunction comes from the
  published unique tensor-unit normalization, so the kernel uses the canonical unit.
  The existing `proEtaleConstantModulePullback` is objectwise, not an available functor
  with this interface; no second independent inverse-image construction was introduced.
- `lem-exc-proetale-closed-support`: its binder `IsCompl (Set.range i) (Set.range j)`
  says exactly that the open immersion is the closed immersion's complement. The
  categories are the full intrinsic unbounded categories, with finite commutative A
  and Noetherian T. The exactness conjunct supplies the termwise interpretation of
  closed derived direct image, as explicitly established by the node's proof and
  Stacks 09BM. The adjunction is to the right derived functor of the specified kernel
  construction just reviewed. It is existence of an adjunction between specified
  functors, not an unspecified right-adjoint functor. Pass.

There are no new DAG nodes. The support-definition node already exists and is added to
the item's statement dependencies because its canonical construction occurs in the
signature. The dependency records explain their missing or unusable old interfaces.
No definition has `sorry` as data; the realization and canonical adjunction choices are
determined up to the precise isomorphism/equality used by their recorded interfaces.
The only postponed statements here are the two item theorems and the closed ambient
adjunction theorem, each with its matching node and full source-based proof docstring.

Edge cases: zero rings and zero complexes are allowed; empty schemes, empty strata,
and full closed strata are allowed; identity closed/open immersions are allowed.
The theorem has no degree or index-set parameter, so there is no hidden positive-degree
or nonempty-index restriction. All characteristics are allowed. No nonempty, proper,
smooth, regular, or constructible condition is assumed. Both directions of unbounded
complexes remain included. Scheme universes are arbitrary. The étale coefficient
universe is u+1; the pro-etale coefficient A has universe u and is lifted by the recorded
constant-ring convention. The pro-etale internal Hom is instantiated at object universe
u+1, morphism universe u, coefficient maximum u+1, without equating those universes.
No undeclared variables or universes remain (`autoImplicit false`).

Independent searches used different wording from the first reader:

- LeanFinder: “Natural isomorphism between internal Hom of an extension by zero and
  pushforward of internal Hom with exceptional inverse image for an immersion”. Eight
  hits concern scheme-module restriction equivalences/adjunctions, not this assertion.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.MonoidalClosed`. Twelve hits concern
  transport of monoidal closure, internal-Hom adjunctions, and Cartesian Frobenius
  comparisons; none supplies the site-specific ambient immersion identity.
- LeanSearch: “Internal Hom and exceptional inverse image for a locally closed immersion
  of schemes”. The service returned Internal Server Error; recorded as unavailable.
- `rg` on Mathlib's monoidal category sources, upstream `WeilConjectures`, and project
  `lean/Sheaf` used `stratumAmbientHom`, Hom/shriek combinations, and
  internalHom/derivedHom with projection. The hits supply component operations and
  restricted scheme-module statements, not this bifunctor identity. A second search for
  the canonical-support/helper names found no competing construction. The existing
  intrinsic extension definition was opened and preserved verbatim.

No hypothesis, object, quantifier, or conclusion mismatch was found. I repaired only
broken `\\operatorname` commands split across lines in the two proof docstrings and
replaced empty “Dependencies: .” annotations with “No additional dependencies.”
All four node `lean.statement` values were checked to occur verbatim in their files;
all delivered Lean lines satisfy the 100-character limit. No mathematical signature,
definition data, source statement, or unit statement changed during this reading.

Validation by the second reader: the required `scompile.py` invocation passed all four
sibling modules separately, including the main module's combined dependency imports,
with no errors or warnings. The final delivery dry run checks the docstring-edited
files again and runs the current server preflight before the delivery is pushed.

## Second reading by Q29

I read the three delivered node records and modules independently, including the
repair of return L. The checklist below is against the node's current mathematical
statement, not merely the earlier report. I opened the blueprint source at order
2069 and its enclosing preservation unit, and the dependency sources at orders
1858 and 1859. The preservation unit concerns finite-type schemes over a field;
the node explicitly retains its Noetherian consequence only on the pro-etale side.
I also checked Stacks proetale.tex, labels
`lemma-closed-immersion-complement-retrocompact-exact` (09BM) and
`lemma-ses-associated-to-open` (09AH), and sites-cohomology.tex, labels
`lemma-adjoint-lower-shriek-restrict` (08FJ), `lemma-j-shriek-and-tensor` (0GL1),
and `lemma-internal-hom` (08J9). These give the source hypotheses needed by the
unbounded argument; no coefficient characteristic or constructibility assumption
is needed for this ambient identity.

The object, hypothesis, and conclusion checklist, in node order:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| A finite commutative ring A | Both declarations bind `A`, `[CommRing A]`, `[Finite A]`. | Exact; no field, nonzero, or characteristic hypothesis. |
| Schemes S and X, and a chosen intermediate U | `{S U X : Scheme.{u}}`. | Exact; arbitrary schemes in the chosen scheme universe. |
| Immersion s factored closed then open | `i : S ⟶ U`, `[IsClosedImmersion i]`, `j : U ⟶ X`, `[IsOpenImmersion j]`, with `s = i ≫ j`. | Exact; s is determined by the factorization, so a redundant extra s binder is unnecessary. |
| Either small site | Separate `Etale.nonempty_stratumAmbientHomIso` and `ProEtale.nonempty_stratumAmbientHomIso`. | Both choices are asserted. |
| Noetherian X only for pro-etale | `[IsNoetherian X]` occurs only in the second declaration. | Exact; Mathlib's class extends local Noetherianity and compactness. No finite-type or separatedness assumption is added. |
| Ordinary unbounded categories of constant-coefficient modules | `Etale.DerivedCategoryModule A T`; `proEtaleDerivedCategory T A`. | Exact; I opened both category definitions and the constant-ring definition. Neither is a bounded or completed category. |
| The coefficient size convention | Étale has `A : Type (u + 1)` and `ModuleCat.{u + 1}`; intrinsic pro-etale has `A : Type u` and the recorded constant ring of `ULift.{u + 1,u} A`, with modules in u+1. | Matches these published presentations. A finite ring can be represented in the smaller universe; the intrinsic category and extension-by-zero dependency already use this convention. Site object size u+1 and morphism size u remain distinct. |
| Rs! is j! Ri* | First product factor is `(lowerStar i).rightDerivedFunctor ⋙ (openImmersionLowerShriek j).mapDerivedCategory`, or its intrinsic `sfConstantModuleDirectImage`/`sfIntrinsicExtensionByZero` version. | Exact, including the order. |
| j! is actual exact extension by zero | Published `openImmersionLowerShriek` on étale sheaves and `sfIntrinsicExtensionByZero` on pro-etale modules. | Exact; the latter transports the published finite-scalar extension along the canonical realization equivalences. Its exactness instances are imported, not redeclared. |
| Rs^! is Ri^! j inverse | Second product factor is exact open `upperStar` followed by the right adjoint to closed derived direct image, or exact `sfConstantModulePullback j A` followed by `(sfIntrinsicClosedUpperShriek i v A).rightDerivedFunctor`. | Exact, with open restriction first. The actual complement v is constructed from `(Set.range i)ᶜ`, not supplied as an additional condition. |
| Ri^! is the ambient closed adjoint | Étale uses the `IsLeftAdjoint` instance from `EtaleClosedAmbientAdjoint`; pro-etale uses the delivered closed-support adjunction on all unbounded objects. | Exact; no Brown adjoint with unspecified source/target or assumption on its values. |
| Rs* is ordinary derived direct image | Final functor is direct image along `i ≫ j`, followed by `.rightDerivedFunctor`. | Exact; not shriek and not a constructible restriction. The imported implementation uses K-injectives. |
| Internal Hom on X and S | `Functor.uncurry.obj (Etale.derivedHom ... T)` or `derivedInternalHomOfUniverses.{u+1,u,u} (ProEt.topology T) (proEtaleConstantRing T A)`. | Exact; the former is internal Hom for derived tensor, the latter localizes the canonical K-injective Hom-complex construction. |
| Every P and M | Functor isomorphism with domain `D(S,A)ᵒᵖ × D(X,A)`. | Exact; the two products feed precisely P and M into the two sides of the node's formula. |
| RHom_X(Rs!P,M) ≅ Rs* RHom_S(P,Rs^!M) | The left composite extends its first argument before Hom on X; the right restricts its second argument before Hom on S and pushes its result to X. | Every clause and variance agrees. |
| Naturality contravariantly in P and covariantly in M | `Nonempty (F ≅ G)` for the two bifunctors. | Exact; this is existence of one natural isomorphism, not only objectwise existence. |
| No amplitude, boundedness, constructibility, preservation, or biduality input | No object-property binders occur. | Exact on the entire ambient categories. |
| Either permitted factorization | Universal i, j, U with just their immersion classes. | Exact; no particular factorization or independence theorem is assumed. |

Dependency-module reading:

* `def-exc-proetale-sections-with-support`: the actual map is the unit of
  `sfConstantModuleAdjunction j A`. The object is its kernel; a morphism is
  `kernel.map` with the square supplied by unit naturality. The closed functor
  composes with the canonical closed module pullback. This gives the source's
  object and morphism clauses. Functor laws and additive instances contain real
  structural proofs, with no postponed data or independent theorem proved here.
  The coefficient isomorphism is `asIso` of the already constructed canonical
  coefficient map, using its published invertibility theorem. The adjunction is
  specialized from the uniquely tensor-unit-normalized published adjunction.
  It is not selected from an undetermined `Nonempty` assertion.
* `lem-exc-proetale-closed-support`: the binders are finite commutative A,
  Noetherian T, closed i, open j, and `IsCompl` of their ranges. The conclusion
  is exactness of the actual closed direct image together with its derived
  adjunction to the specified support functor. Exactness is explicitly used in
  the source and identifies `.rightDerivedFunctor` with termwise closed image.
  There are no object restrictions. Its docstring carries all four DAG proof
  steps, including the open-unit restriction calculation and the two
  homotopy-to-derived Hom identifications. Pass.

I read the current dependency declarations in `EtaleClosedAmbientAdjoint`,
`DerivedCategories`, `ProEtaleDerivedCategory`, `ProEtaleInverseImage`,
`ProEtaleOperations`, `ProEtaleOperationsCanonicalAdjunction`,
`ProEtaleIntrinsicExtensionByZero`, `ProEtaleIntrinsicExtensionByZeroExact`,
`ProEtaleFiniteModuleIntrinsicComparison`, `DerivedInternalHomOfUniverses`,
`RingedSiteModules`, `KFlat`, `SiteDerivedTensorDescent`, and
`KInjectiveTotalDerived`, as well as upstream étale lower/upper star, open
extension by zero, and derived Hom. The Noetherian, immersion, and small-site
Mathlib declarations have the expected binders. K-injective existence is in the
recorded independent-universe interface. The two complete ten-step proof plans
in the main file reproduce the node's proof rather than assuming the desired
identity or any preservation theorem.

One change since the worker's report matters for the dependency notes: the
current DAG now records N0's `ProEtale.finiteSupportedSections` and
`finiteClosedUpperShriek` in `Sheaf.AlgebraicGeometry.ProEtaleSupportedSections`,
and Q42's existing upstream `derivedLowerStarClosedUpperShriekAdjunction`.
I opened these declarations. They act on fixed-scalar ModuleCat-valued sheaves,
whereas the published intrinsic extension-by-zero and derived-category
interfaces used here act on SheafOfModules over the constant ring sheaf.
The fixed-scalar support functor cannot be applied to those intrinsic objects;
the upstream adjunction additionally imports the conflicting legacy star
modules documented by the previous compile probes. Thus the same intrinsic
§1(B) interfaces remain necessary. I corrected both delivered `lean.note`
fields: neither now claims that the current dependency has no module or no
Lean declaration. The published category presentation can change without
invalidating the retained intrinsic presentation: the canonical realization
module explicitly relates the two. No current recorded notion is silently
substituted by a different category with no comparison.

Independent searches used other wording than the first worker:

* LeanFinder: “internal sheaf Hom of extraordinary direct image for a locally
  closed subscheme is the direct image of internal Hom with exceptional pullback”.
  Eight results were generic scheme-module pullback/pushforward and open
  restriction adjunctions, not this ambient derived bifunctor isomorphism.
* Loogle: `Functor.uncurry, Adjunction`. No hit; the service did not recognize
  `Functor.uncurry`.
* LeanSearch: “For a locally closed immersion internal derived Hom of extension
  by zero is direct image of internal derived Hom into exceptional inverse image”.
  Eight results concerned locally closed ranges, immersion images and open
  immersion maps. None stated the node.
* Direct `rg` in Mathlib's monoidal-closed declarations, upstream six-functor
  modules and the project's `lean/Sheaf`, using `internalHom`, `derivedHom`,
  Hom/shriek combinations, `stratumAmbientHomIso` and supported-section terms.
  I opened the generic internal Hom and both upstream site derived-Hom
  declarations. No existing stratum identity was found. The searches did find
  the newer fixed-scalar support interface described above; its objects differ
  from the intrinsic interface required by this module. No independent notion
  is absent, and no new definition node is added.

Edge cases: zero coefficient rings and zero complexes remain allowed, because
there is no `Nontrivial` or nonvanishing input. Empty schemes, empty/full closed
strata, empty opens and identity immersions remain allowed; the canonical
complement construction works for the empty and full range. There is no index
set or degree parameter excluding an empty set or degree zero. Complexes are
indexed by all integers and can be unbounded in both directions. All finite
coefficient characteristics are allowed, including the characteristic of any
base field. No additional relation between site object and morphism universes
is imposed. The étale theorem allows non-Noetherian X. The pro-etale theorem
assumes Noetherianity only on X; openness supplies the needed condition on U
and its complementary open. All variables are explicitly bound with
`autoImplicit false`.

The repair of return L is present: only three Lean files remain, and none
redeclares the three extension-by-zero exactness instances. Every definition
has actual data; only the two main statements and the closed-ambient statement
are `sorry`. Source/blueprint docstrings, complete proof plans, public versus
proof imports, namespaces and 100-character lines pass inspection. All three
recorded primary signatures occur verbatim in their files. There is no
`statement_change`, no mathematical statement correction, and no new node to
audit. The only changes in this second reading are this report and the two
stale dependency explanations; the Lean source and mathematical statements are
retained unchanged. Compilation and dry-run results are recorded below.

Validation: `scompile.py Q29 lem-weil-stratum-ambient-hom` on all three delivered
modules completed successfully, compiling each separately against the private
overlay. It reported no errors or warnings. The declaration reader confirms
all three primary signatures, and direct checks found no line over 100
characters, no duplicate delivered declaration, and no unbound variable.

The required `deliver2.py Q29 lem-weil-stratum-ambient-hom --no-push`
completed with `OK (dry run)`: all modules compile and the current server
preflight passes. The wrapper preserved the current maintainer review metadata
on both dependency records rather than copying their older sandbox metadata.
