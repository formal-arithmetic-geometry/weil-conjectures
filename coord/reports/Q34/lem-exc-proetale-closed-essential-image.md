## Worker report

The delivery states `AlgebraicGeometry.Scheme.proEtaleRingModule_closed_essImage_iff_and_unit_isIso`
in `lean/Sheaf/AlgebraicGeometry/ProEtaleClosedEssentialImage.lean`. There is one theorem,
with proof `sorry`, and no new definition or dependency repair. Only the item's `lean`
field changes. No statement correction or disputed statement is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and morphisms are `{X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)`.
- The closed immersion is `[IsClosedImmersion i]`.
- The complementary open immersion is `[IsOpenImmersion j]` together with
  `hU : Set.range j = (Set.range i)ᶜ`. This allows any presentation of the open
  complement, not only a chosen subscheme object. The range is the underlying point map.
- Quasi-compactness as a morphism is `[QuasiCompact j]`, not compactness of U or X.
- The arbitrary commutative coefficient sheaves A_X, A_Z, A_U are `R`, `Ri`, `Rj`,
  each a `Sheaf (ProEt.topology ...) CommRingCat.{u + 1}`.
- Their specified coefficient identifications are `ci` and `cj`, respectively
  `(proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ Ri` and the same for j.
- Any A_X-module sheaf is `F : proEtaleRingModules X R`. This is the existing
  `ringedSiteModules`/Mathlib `SheafOfModules` category after forgetting commutativity.
  There is no constancy, constructibility, finiteness, torsion, noetherian, or qcqs assumption.
- Membership in the image is `(proEtaleRingModuleDirectImage i R Ri ci).essImage F`.
  Mathlib's `Functor.essImage` is exactly `∃ G, Nonempty (i_*.obj G ≅ F)`.
- The first clause is an `↔` between that membership and
  `IsZero ((proEtaleRingModulePullback j R Rj cj).obj F)`.
- The second clause is the implication from the same zero restriction to
  `IsIso ((proEtaleRingModuleAdjunction i R Ri ci).unit.app F)`.
  This is the specified canonical unit F → i_* i^* F, not an arbitrary isomorphism.
  The antecedent is equivalent to image membership by the first clause, so this
  renders precisely "for such a sheaf".

Dependency declarations read and used:

- `def-weil-pbc-proetale-operations` is recorded at
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`. Its public import
  chain retains `Sheaf.AlgebraicGeometry.ProEtaleOperations` and
  `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`. I read the former's
  full signatures/docstrings for `AlgebraicGeometry.Scheme.proEtaleRingModules`,
  `proEtaleRingDirectImageMap`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingModulePullbackObj`, `proEtaleRingModulePullbackMap`, and
  `proEtaleRingModulePullback`, and the latter's canonical normalization theorem
  `proEtaleRingModuleAdjunction_existsUnique` and construction `proEtaleRingModuleAdjunction`.
  Server sources for the recorded module and canonical adjunction were also checked with
  `scompile.py --source`; their public interface supplies the arbitrary-coefficient case.
  The recorded module is imported directly, so no dependency interface is replaced.
- `def-weil-pbc-scheme-conventions` is explicitly a convention record with no declaration.
  Its Mathlib notions are `AlgebraicGeometry.IsClosedImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, and `AlgebraicGeometry.QuasiCompact`.
- `def-weil-sheaf-of-modules-category` supplies `CategoryTheory.ringedSiteModules`
  in `Sheaf.CategoryTheory.RingedSiteModules`. Its source/docstring and the underlying
  `SheafOfModules`, `SheafOfModules.Hom`, and abelian-instance source were read.
- The stated proof dependency `lem-weil-pbc-proetale-ringed-open-closed` supplies
  `AlgebraicGeometry.Scheme.proEtale_ringed_open_closed` in
  `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`, imported for stage 3. Its full
  arbitrary-coefficient statement, actual ringed direct image and extension by zero
  definitions were read. Its qcqs restriction applies only to filtered colimits.
- `def-weil-pbc-exact-sequence` is `CategoryTheory.ComposableArrows.Exact` /
  `ShortComplex.ShortExact` in `Mathlib.Algebra.Homology.ExactSequence`, imported for
  stage 3. `def-sp-abelian` is Mathlib's `CategoryTheory.Abelian`, already available
  through `RingedSiteModules`. All other proof dependencies are statement dependencies.

Source check: the blueprint source file named by the node is absent from this read-only
clone. The node's complete statement and five proof steps were read. I opened
[Stacks Tag 09AH](https://stacks.math.columbia.edu/tag/09AH), which assumes the
quasi-compact complementary open immersion and supplies the canonical open-closed
short exact sequence without a noetherian or qcqs restriction on X. The module-sheaf
extension is precisely the existing ringed open-closed dependency. The declaration
contains the node's five-step natural-language proof, including scalar transport,
normalization of the actual unit, the forward implication, the zero-kernel/epic inverse
construction, and the essential-image witness.

Edge cases checked mathematically against the signature:

- F = 0: both image membership (take the zero module) and zero open restriction hold;
  the unit is an isomorphism between zero objects.
- Empty U: the conclusion covers all module sheaves; the statement admits closed
  immersions with full topological image, including nilpotent thickenings.
- Empty Z: the only possible essential-image object is zero; open restriction detects
  that condition. Empty X is admitted, with no nonemptiness binder.
- Zero coefficient rings and nonconstant coefficient sheaves are allowed.
- Arbitrary ci and cj, including nontrivial coefficient automorphisms, remain explicit.
  The unit is transported with these identifications, not replaced by another adjunction.
- Size convention: schemes are in universe u, the pro-etale site has objects in u+1
  and morphisms in u, and coefficients/modules are in u+1. These are the recorded
  operations' universes; no equality of site object and morphism universes is imposed.
  Every universe and binder is explicit (`set_option autoImplicit false`).

Searches performed before writing (2026-10-16):

- `msearch.py ... leanfinder` queried: "An arbitrary ring sheaf module on the pro etale
  site is in the essential image of a closed immersion direct image exactly when open
  restriction vanishes, and its adjunction unit is invertible". Eight hits concerned
  Zariski module restriction adjunctions, constant sheaves, and closed subscheme ideals;
  none is the arbitrary-ring-sheaf pro-etale statement.
- `msearch.py ... loogle '"essImage", "unit"'` returned generic adjunction lemmas,
  including `Adjunction.isIso_unit_app_iff_mem_essImage` and
  `Adjunction.mem_essImage_of_unit_isIso`. They do not provide the geometric vanishing
  criterion, nor establish full faithfulness for these ringed operations.
- `msearch.py ... grep 'essImage|closed.*unit|unit.*closed' CategoryTheory` returned
  generic essential-image/localization results; no geometric pro-etale criterion.
- `msearch.py ... leansearch` queried: "A module sheaf on the pro etale site belongs to
  the essential image of closed direct image if and only if restriction to the open
  complement is zero". The service returned Internal Server Error; recorded as unavailable.
- `rg` of upstream `WeilConjectures` and project `lean/Sheaf`, and `grep -rn` of the
  item id upstream, found
  `AlgebraicGeometry.ProEtale.lowerStar_essImage_iff_of_isCompl` and
  `isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl` in
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion`.
  I read their signatures and docstrings. They use `Sheaf ... (ModuleCat R)` for a
  single constant ring, not modules over arbitrary R, Ri, Rj with ci and cj. Thus an
  `existing: true` attachment would omit the node's general coefficient convention.
- `rg` of Mathlib, upstream, project Sheaf, and `dag/lean_names_upstream.json` for the
  proposed full declaration name found no collision. Searches of project Sheaf for
  `proEtaleRingModule.*(essImage|isIso)` / `proEtaleRingModule_closed` found no match.

Validation: `scompile.py Q34 lem-exc-proetale-closed-essential-image` is used for
single-file compilation with the prescribed overlay and time limit. The final dry run
is `deliver2.py Q34 lem-exc-proetale-closed-essential-image --no-push`; no delivery
is pushed by this worker. The independent second reader will add their own section.

## Second reading by Q34

I independently read the sandbox node, its five proof steps, the complete Lean module,
and the statement-dependency nodes and declarations. The blueprint file and local
Stacks checkout are absent here. I read the actual Stacks `proetale.tex`, label
`lemma-ses-associated-to-open` (Tag 09AH), and `sites-modules.tex`, label
`lemma-adjoint-push-pull-modules` (Tag 03D3), from the Stacks project's source repository,
as well as their published tag pages:
https://stacks.math.columbia.edu/tag/09AH and
https://stacks.math.columbia.edu/tag/03D3.
Tag 09AH assumes precisely a closed subscheme and quasi-compact complementary open
immersion, with arbitrary X. Tag 03D3 supplies the inverse-image coefficient module
adjunction. There is no ambient noetherian, qcqs, finiteness or torsion assumption.

My object/hypothesis/conclusion checklist, matched against the Lean:

- Objects X, Z, U and maps i, j: `{X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)`.
  These are schemes and their actual morphisms, with no base field. Pass.
- Closed immersion i: `[IsClosedImmersion i]`, the Mathlib closed immersion class
  named by the scheme convention dependency. Pass.
- Complementary open immersion j: `[IsOpenImmersion j]` and
  `hU : Set.range j = (Set.range i)ᶜ`. The coerced morphisms are the underlying point
  maps, so this is exactly complementary image, allowing every presentation of U. Pass.
- Quasi-compactness of the morphism j: `[QuasiCompact j]`, with no quasi-compactness
  required of X or U as a space. Pass.
- Coefficient sheaves A_X, A_Z, A_U: `R`, `Ri`, `Rj`, respectively sheaves on the
  three small pro-etale sites valued in `CommRingCat.{u + 1}`. These are arbitrary
  commutative ring sheaves, not fixed-ring or constant sheaves. Pass.
- Specified identifications: `ci` and `cj` identify the actual ring inverse images
  of R with Ri and Rj. They are quantified before F and before the conclusion. Pass.
- Arbitrary A_X-module F: `(F : proEtaleRingModules X R)`. I unfolded this public
  abbreviation to `CategoryTheory.ringedSiteModules`, then to Mathlib
  `SheafOfModules.{u + 1}` over R with commutativity forgotten. The objects and linear
  morphisms are exactly those of the module-category dependency. Pass.
- Essential-image membership: `(proEtaleRingModuleDirectImage i R Ri ci).essImage F`.
  I opened Mathlib's `Functor.essImage`: this is
  `∃ G, Nonempty (i_*.obj G ≅ F)`, exactly the node's clarified meaning of image. Pass.
- First conclusion, both directions: the first conjunct is the equivalence between
  that membership and `IsZero ((proEtaleRingModulePullback j R Rj cj).obj F)`.
  Categorical zero means the zero module sheaf up to isomorphism. Pass.
- Second conclusion: the second conjunct assumes the same zero restriction and asserts
  `IsIso ((proEtaleRingModuleAdjunction i R Ri ci).unit.app F)`. Together with the first
  conjunct this is exactly the claim for every sheaf in the essential image. Pass.
- Canonicity: I read `proEtaleRingDirectImageMap`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingModulePullbackObj`, `proEtaleRingModulePullbackMap`, and
  `proEtaleRingModulePullback`. They use the adjoint of ci, actual module inverse image,
  and sheafified tensor extension. I read the full
  `proEtaleRingModuleAdjunction_existsUnique` normalization and its selected adjunction:
  the conclusion concerns the actual tensor-unit-normalized unit, not a chosen map.
  Its unique characterization permits the choice and is not hollow data. Pass.

I checked the recorded operations module's public import chain through
`ProEtaleConstantDerivedDirectImage` to `ProEtaleOperationsCanonicalAdjunction` and
`ProEtaleOperations`. Thus it retains the arbitrary-coefficient interface despite the
finite-coefficient primary declaration. No dependency repair is necessary.
I also read `proEtale_ringed_open_closed` and its helper constructions: the slice
equivalence explicitly intertwines open inverse image with `overFunctor`; its
localization short exact sequence uses the unit of its exhibited adjunction. The qcqs
condition occurs only inside its final filtered-colimit implication. For stage 3, if
that exhibited adjunction differs from the normalized one, adjunction uniqueness gives
a natural isomorphism of left adjoints, carrying one unit to the other; invertibility
is preserved. This causes no extra hypothesis or change in the present statement.
The exactness and abelian proof dependencies use Mathlib's existing categorical notions.

Edge cases: F = 0 and zero coefficient rings are included. Empty X, Z or U are included,
without any nonemptiness binder. With empty Z, image membership means F is zero; with
empty U, every F is covered, including a closed immersion with full image and a
nontrivial nilpotent thickening. Coefficient identifications may be nonidentity
automorphisms. There is no integer degree, characteristic, or index-set binder to
restrict. I read the inverse-image small-model transport: the original site retains
object universe u+1 and Hom universe u; coefficients and modules are in u+1 as required
by the dependency convention. No equality of those site universes or additional
size/nonemptiness instance is imposed. `universe u` and `autoImplicit false` bind
everything explicitly.

Independent searches on 2026-10-16:

- LeanFinder: "Modules over a sheaf of rings supported on a closed subscheme are exactly
  closed direct images and the localization unit is invertible". Eight results concerned
  ideal sheaves and Zariski module localization; no matching theorem.
- Loogle: `"essImage", "isZero"`. No results.
- LeanSearch: "For modules over a varying sheaf of rings on the proetale site, the closed
  immersion pushforward image is the kernel of restriction to the open complement".
  Internal Server Error; this service was unavailable, not evidence of absence.
- The prescribed grep search for `supported|essImage|recollement` in CategoryTheory found
  generic localization and essential-image results. Direct `rg` searches also covered
  Mathlib's geometry sites, the upstream source, the project's Sheaf modules and the
  current `ModuleObject` framework. I opened the full signatures of
  `ProEtale.lowerStar_essImage_iff_of_isCompl` and
  `ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl`: both concern
  `Sheaf ... (ModuleCat R)` for one fixed ring, so neither matches arbitrary ring sheaves
  and specified ci/cj. Mathlib's `Adjunction.isIso_unit_app_iff_mem_essImage` assumes
  fully faithful direct image and supplies no geometric zero-restriction criterion.
  The framework's derived module-object results do not state this sheaf-level criterion.
  The proposed declaration name has no upstream, Mathlib or existing project collision.

No mismatch was found; I left the Lean and node unchanged and added this independent
review. There are no new nodes, dependency modules, private notions, hollow definitions,
statement corrections or citer audits to review. The module's only theorem has proof
`sorry`; both docstrings identify the source and blueprint, and the theorem docstring
reproduces all five proof steps. All Lean lines satisfy the 100-character limit.
I checked programmatically that `lean.statement` equals the file signature verbatim
and that only `lean` differs from the repository's node.

Validation: the prescribed `scompile.py` passed cleanly for the delivered file in its
sandbox and library forms (5.1 s and 9.7 s), with no warnings. The initial invocation
from the shared directory used a nonexistent relative path; rerunning from the sandbox
resolved this invocation error without any source or tool change.
