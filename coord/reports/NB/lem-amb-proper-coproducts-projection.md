## Worker report

Item: `lem-amb-proper-coproducts-projection`, group NB, stage 2, 2026-10-15.

The new module `Sheaf.AlgebraicGeometry.ProperProjectionFormula` states
`AlgebraicGeometry.Etale.isIso_proper_projection_formula_reordered`. Its single proof is
`sorry`. It states invertibility of the specified composite, not existence of an unrelated
isomorphism. The original node's statement and all dependency/proof lists are unchanged.

Hypothesis and clause audit:

| Node text | Lean rendering |
| --- | --- |
| A finite commutative ring | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| Schemes V,T and morphism r | `{V T : Scheme.{u}} (r : V ⟶ T)` |
| Proper r, of finite type | `[IsProper r]`; Mathlib properness includes locally finite type and universally closed, hence quasi-compact, thus finite type |
| V Noetherian | `[IsLocallyNoetherian V] [CompactSpace V]` |
| T Noetherian | `[IsLocallyNoetherian T] [CompactSpace T]` |
| Ordinary unbounded small-etale module derived categories | `DerivedCategoryModule A V` and `DerivedCategoryModule A T`, the exact upstream abbreviation used by the recorded derived-category node |
| Every L and K | Unrestricted binders `(L : DerivedCategoryModule A V) (K : DerivedCategoryModule A T)` |
| Exact termwise inverse image r inverse | `(upperStar (ModuleCat A) r).leftDerivedFunctor`, canonically identified with `(upperStar (ModuleCat A) r).mapDerivedCategory` by `leftDerivedUpperStarIsoMapDerivedCategory` |
| Its derived right adjoint | `(lowerStar (ModuleCat A) r).rightDerivedFunctor`, paired with this pullback by `derivedUpperStarLowerStarAdjunction` |
| Ordinary uncompleted derived tensor | Every tensor is the recorded upstream `derivedTensor`, as encoded in the two ends of `rightDerivedLowerStarProjectionMap` and in `derivedTensorSymmetry` |
| First arrow, K tensor RrL to RrL tensor K | `((derivedTensorSymmetry (ModuleCat A) T).hom.app K).app ((lowerStar (ModuleCat A) r).rightDerivedFunctor.obj L)` |
| Middle adjoint-of-counit PF(L,K) | `((rightDerivedLowerStarProjectionMap (ModuleCat A) r).app L).app K` |
| Last arrow, Rr of symmetry on V | `(lowerStar (ModuleCat A) r).rightDerivedFunctor.map (((derivedTensorSymmetry (ModuleCat A) V).hom.app L).app ((upperStar (ModuleCat A) r).leftDerivedFunctor.obj K))` |
| Exactly the displayed three-arrow composite | These expressions are composed in the displayed order by `≫` |
| The canonical signed symmetry | The dependency repair constructs the actual `DerivedMonoidal.braiding`, using the signed homotopy-category braiding. It does not choose an arbitrary natural isomorphism from `Nonempty` |
| Isomorphism in D(T_et,A) | `IsIso` of that composite |
| No boundedness, constructibility, Tor amplitude, completion, or invertibility of order | No such binder or predicate occurs |

The coefficient size is the recorded six-functor convention: the small-etale site of
`Scheme.{u}` has objects in `Type (u+1)` and morphisms in `Type u`, and module coefficients
are in `ModuleCat.{u+1} A` with `A : Type (u+1)`. No site object/morphism universes are
identified. This is exactly the category from `def-weil-pbc-derived-categories`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper` (and its
  `UniversallyClosed` and `LocallyOfFiniteType` components).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, without a Hausdorff condition.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: recorded category conventions;
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` is the underlying abbreviation.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`, the K-flat-derived bifunctor.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`; read its full signature and docstring.
  The upstream six-functor exact pullback realizes this in the module-valued-sheaf encoding;
  `leftDerivedUpperStarIsoMapDerivedCategory` identifies its derived and termwise versions.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `rightDerivedLowerStarProjectionMap`, `rightDerivedLowerStarProjectionMap_app_app`,
  `homEquiv_symm_rightDerivedLowerStarProjectionMap`. These fix the actual counit mate.
- `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`:
  `nonempty_iso_derivedTensor_flip`; this is the old symmetry record, repaired below.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat` provides the module
  coefficient instance, with no additional assumptions on r, K, or L.

The proof docstring follows all three proof steps: finiteness gives torsion and exact inverse
image; Stacks 0F0G gives the middle isomorphism; the canonical symmetries and their inverses
finish the composite. The existing finite-coefficient specialization
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite` is imported from
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula` for stage 3. The general
`lem-kun-0f0g` has no recorded declaration or module, so there is no import for that proof-only
node; it is not needed to state this item. No dependency wait is introduced.

Edge cases checked before writing: the zero coefficient ring is allowed (`CommRing`, not
`Nontrivial`), as are the empty schemes, zero complexes, the identity morphism, and complexes
unbounded in both directions. Characteristic dividing the order of A is allowed on the schemes.
Properness already implies the explicit finite-type phrase. None of these cases requires a
new hypothesis; no uniform cohomological-dimension bound is used in the signature.

Searches made with `msearch.py NB lem-amb-proper-coproducts-projection`:

- LeanFinder: "For a proper morphism of schemes and a finite commutative coefficient ring,
  the unbounded derived tensor projection map on small etale sheaves is an isomorphism".
  Eight hits about light condensed projectivity, formal etaleness and Kahler differentials;
  no matching Mathlib declaration.
- Loogle: `"IsIso", "projection"`: zero hits.
- Grep: `projectionFormula|projection_formula|rightDerivedLowerStarProjectionMap`: zero hits.
- LeanSearch: "Unbounded derived projection formula for proper direct image of etale sheaves
  with finite commutative coefficient ring": unavailable, Internal Server Error; no verdict.
- Repository `rg` for `lem-amb-proper-coproducts-projection` finds
  `WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula.lean:239`. The theorem there
  asserts invertibility of the original-order projection bifunctor for all proper schemes,
  without the Noetherian hypotheses. It is not this node's explicit reversed-factor composite;
  `lem-etale-proper-projection-formula-finite` already records that exact theorem.
- `rg` in `dag/lean_names_upstream.json` for the new names and the finite projection
  theorem name returned no entries in that catalog. Direct source inspection above located
  the actual upstream theorem.
- `rg` in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` for the theorem and
  helper names `isIso_proper_projection_formula_reordered|derivedTensorSymmetry` found no
  declaration collision. Searches of the same trees for projection-map names and symmetry
  constructions located the actual canonical upstream K-flat braiding and its comparison
  lemmas. No existing declaration states this precise reversed composite with this signature.

Sources opened: the complete imported blueprint node; local Stacks
`etale-cohomology.tex`, `lemma-projection-formula-proper-mod-n` (0F0G); local
`sites-cohomology.tex`, `definition-derived-tor` and the following signed-symmetry paragraph
(06YU); the full recorded dependency declarations and their docstrings; upstream
`CategoryTheory/Monoidal/DerivedBraided.lean`,
`CategoryTheory/Monoidal/Instances/DerivedCategory.lean`, and
`Algebra/Homology/HomotopyCategory/Braided.lean` for the actual descended signed swap.

No statement correction and no STATEMENT-DISPUTED finding.

## Dependency modules

`lem-kun-tensor-sym`: new module `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`,
recording `AlgebraicGeometry.Etale.derivedTensorSymmetry`.

The old `nonempty_iso_derivedTensor_flip` forgets the map it constructs. Extracting an arbitrary
isomorphism from its `Nonempty` conclusion would not identify the map in this item's composite.
The repair supplies the actual canonical natural isomorphism, with full data:
the helper `CategoryTheory.DerivedMonoidal.canonicalBraidingNatIso`, which uses
two applications of `NatIso.ofComponents` to the concrete upstream
`DerivedMonoidal.braiding DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ))`.
The two naturality witnesses are the already proved upstream
`DerivedMonoidal.braiding_naturality_right` and `braiding_naturality_left`, with
`NatTrans.ext` for the outer curried functor. No new theorem is proved in this definition.
The helper is generic in the localization and its categories; the etale definition specializes
it to the recorded tensor product. Both declarations are listed in `lean.declarations`.
The homotopy-category braiding is the image of the Koszul cochain-complex braiding;
`DerivedMonoidal.braiding_hom_μ` is its K-flat representative characterization. The helper
is generic in the coefficient category so specialization to `ModuleCat A` does not require
Lean to compare two large monoidal-instance terms, as explained in upstream TensorStructure.
Its natural-isomorphism type gives naturality in both arguments, and its components are
isomorphisms by construction. Its data contains no `sorry` and makes no arbitrary
`Nonempty` choice. Only this dependency node's `lean` field is changed.

## Validation

The prescribed `scompile.py` wrapper passed with exit code 0 and no warnings for both
delivered modules, each compiled separately in dependency order. The canonical symmetry
module passed its preliminary, sandbox and library checks (57.2 s, 57.6 s, 57.8 s), and
the projection-formula theorem passed its sandbox and library checks (2.5 s, 2.7 s), all
within the fixed 60-second limit. The theorem has exactly one `sorry`; the two helper
definitions have complete data. Node deltas and literal-signature checks confirm that
only the two authorized `lean` fields changed, and all Lean lines have at most 100 characters.
The preflight signature convention starts at `def` and omits the preceding `noncomputable`
modifier; the dependency record follows that convention. The canonical symmetry module
imports the recorded derived-category module and the existing tensor module directly.
The independent second reader supplies the second-reading section and delivers; this
worker uses only `deliver2.py --no-push`.

## Second reading by NB

Independent second reading, 2026-10-15. I opened the item and dependency node JSON,
both delivered Lean modules, the recorded dependency declarations, the blueprint source,
Stacks `etale-cohomology.tex` lemma-projection-formula-proper-mod-n (0F0G), and
`sites-cohomology.tex` definition-derived-tor and its following symmetry paragraph (06YU).
The Stacks lemma assumes properness and torsion coefficients, with arbitrary objects of the
unbounded derived categories. It has no global Noetherian, boundedness, or invertibility
assumption. The item's additional Noetherian hypotheses are in its reviewed statement and
are retained. The item's node has no `statement_change`; none is needed.

My object, hypothesis, and conclusion checklist, independently matched to the Lean:

| Node item | Lean rendering and verdict |
| --- | --- |
| Finite commutative coefficient ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`: exact; no nonzero-ring or field assumption. |
| Schemes V and T, with r : V → T | `{V T : Scheme.{u}} (r : V ⟶ T)`: exact. |
| Proper, finite-type morphism | `[IsProper r]`: exact. I read Mathlib's class, extending separatedness, universal closedness, and locally finite type. `UniversallyClosed.lean:167` supplies quasi-compactness, giving finite type. No extra finite-type binder is needed. |
| V Noetherian | `[IsLocallyNoetherian V] [CompactSpace V]`: exactly locally Noetherian plus quasi-compact as the node specifies. |
| T Noetherian | `[IsLocallyNoetherian T] [CompactSpace T]`: the same exact conjunction for T. `CompactSpace` imposes no Hausdorff condition. |
| Ordinary small-etale module categories | `DerivedCategoryModule A V` and `DerivedCategoryModule A T`: exact upstream abbreviations, read in `Derived/Coefficients.lean`, for `DerivedCategory (Sheaf _ (ModuleCat.{u + 1} A))`. The recorded `Sheaf.AlgebraicGeometry.DerivedCategories` explicitly uses these categories. |
| Every L and K, in that order | `(L : DerivedCategoryModule A V) (K : DerivedCategoryModule A T)`: unrestricted, with the same quantifier order. |
| Exact inverse image r* = r inverse | `(upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor`: the dependency's standard implementation, canonically identified with the termwise exact functor by `leftDerivedUpperStarIsoMapDerivedCategory`. I read the latter definition and the exactness/adjunction interfaces, including `etaleInverseImageModulesExact`. This is the same inverse image, without a new assumption. |
| Derived right adjoint Rr* | `(lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor`: paired with the preceding pullback by `derivedUpperStarLowerStarAdjunction`, whose signature I read. |
| Ordinary uncompleted derived tensor | The endpoints of each symmetry and of `rightDerivedLowerStarProjectionMap` use the recorded `derivedTensor`, whose definition and K-flat construction I opened. No completed or bounded category is substituted. |
| First map σ : K tensor Rr*L → Rr*L tensor K | `((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app K).app ((lowerStar _ r).rightDerivedFunctor.obj L)`: exact order and direction. |
| Middle PF_r(L,K) | `((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) r).app L).app K`: exact. Its definition is the right-adjoint projection map for the recorded derived adjunction and tensor comparison. I checked `rightDerivedLowerStarProjectionMap_app_app` and `homEquiv_symm_rightDerivedLowerStarProjectionMap`: its transpose is the inverse-image tensor comparison followed by counit tensor identity, as required by the node. |
| Last map Rr*(σ) | `rightDerivedFunctor.map` applied to the component of `derivedTensorSymmetry ... V` at L and the derived inverse image of K: exact. Its target has inverse image K first and L second. |
| The displayed composite is an isomorphism | `IsIso (first ≫ middle ≫ last)`: exactly this map, with the displayed source and target; no replacement by existence of an unrelated isomorphism. |
| Canonical signed symmetry, natural in both variables | The repaired dependency's `derivedTensorSymmetry` is a natural isomorphism of the recorded tensor bifunctor with its flip. Its components are the actual `DerivedMonoidal.braiding`, as checked below. |
| No further restrictions | No boundedness, constructibility, finite Tor amplitude, pro-etale completion, invertibility, dimension bound, or arbitrary-map hypothesis occurs. |

Dependency repair review (H13): I read `lem-kun-tensor-sym`'s statement and all three
proof steps, and its 06YU source. The old `nonempty_iso_derivedTensor_flip` records only
existence; it cannot itself name the canonical arrow required in this item's composite.
The repair is justified under §1(B). `canonicalBraidingNatIso` packages the existing
`DerivedMonoidal.braiding F W` using `NatIso.ofComponents` twice, with the existing left
and right naturality identities. `derivedTensorSymmetry` specializes it at
`DerivedCategory.Qh` and homotopy quasi-isomorphisms on precisely the etale sheaf category.
I followed `braidingCounit`, `braidingNatTrans`, `braiding`, `braiding_hom_counit`, and
`braiding_hom_μ` in `CategoryTheory/Monoidal/DerivedBraided.lean`: these descend the
specified homotopy braiding through the two-variable derived universal property.
`HomotopyCategory.braiding` in `Algebra/Homology/HomotopyCategory/Braided.lean` is the
quotient image of the Koszul cochain braiding. Thus this is the signed swap of the node,
not an arbitrary choice from `Nonempty`. The generic coefficient assumptions are the
same as `derivedTensor`'s; specialization to `ModuleCat.{u + 1} A` supplies all of them
for every commutative A. Both new definitions have actual data, zero `sorry`s, source and
blueprint docstrings, and are listed in `lean.declarations`. No new definition node or
postponed helper theorem was introduced. Only this dependency's `lean` field changes.

Edge cases: the zero coefficient ring is admitted; there is no `Nontrivial A` binder.
Empty schemes and zero complexes are admitted; there is no nonemptiness assumption.
The identity morphism is included whenever the stated scheme hypotheses hold. Both
complexes may be unbounded in either direction. Scheme characteristic can divide |A|.
There is no index type or natural-number parameter, so empty-index and n=0 restrictions
do not arise. The universe `u` is explicitly bound; schemes use u, site objects u+1,
site morphisms u, and coefficients/modules u+1 exactly as the recorded derived-category
interface prescribes. The repair's `u'`, `u`, `v₁`, and `v₂` are explicitly declared, and
its generic category universes do not impose any additional equality on site universes.
No binder or free universe is left unbound.

Independent searches (different wording from the first reader):

- `msearch.py ... leanfinder "Canonical commutativity constraint of derived tensor, and
  projection map isomorphism for proper etale pushforward with torsion coefficients"`:
  eight hits about scheme pullback triplets and affine tensor products; none states this
  unbounded derived projection composite or supplies its symmetry interface.
- `msearch.py ... loogle '"braiding", "IsIso"'`: zero hits.
- `rg` in Mathlib's derived-category files, the full upstream `WeilConjectures` tree,
  and the project's `lean/Sheaf` for `projection.*[Ii]so`, `[Ii]so.*projection`,
  `curriedBraidingNatIso`, and `derivedTensorSymmetry`: no existing declaration of this
  precise composite. I opened the useful hits rather than relying on their names.
  Upstream `isIso_rightDerivedLowerStarProjectionMap_of_finite` is about the original-order
  bifunctor and has weaker geometric hypotheses; it is already recorded on its own node,
  and supports the proof without duplicating this statement. The upstream generic
  `BraidedCategory.curriedBraidingNatIso` requires a chosen braided instance; it does not
  expose the canonical derived braiding through the recorded tensor API. The repair
  directly packages the existing descended braiding, without redefining that braiding
  or tensor product. Exact-name searches found no declaration collision.

Docstrings and delivery checks: the theorem docstring follows the node's three proof
steps (finite implies torsion and exact inverse image; apply 0F0G; compose the two signed
symmetries with PF and write the inverse). The missing general 0F0G node is proof-only,
so it does not block the signature; the already available finite specialization is
imported for stage 3. The sole theorem proof remains `sorry`, as stage 2 requires.
Both Lean signatures equal their node `lean.statement` strings verbatim under the
preflight convention. Both modules have lines of at most 100 characters. Comparing the
sandbox nodes with the read-only base shows only the two authorized `lean` fields changed.

Verdict: no mathematical, signature, or definition mismatch found. I preserved both Lean
modules and both node records; the second reading changes only this report by adding the
independent clause-by-clause audit. Compilation and delivery checks are recorded below.

Second-reader validation: the prescribed `scompile.py` command compiled both sibling modules
separately and returned exit 0 with no warnings. The symmetry module's preliminary, sandbox,
and library checks took 58.0 s, 57.5 s, and 56.7 s; the projection statement's sandbox and
library checks took 2.5 s and 2.7 s. Each invocation stayed within the fixed 60-second limit.
