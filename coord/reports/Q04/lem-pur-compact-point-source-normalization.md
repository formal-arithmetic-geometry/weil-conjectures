# Section-one normalization of the compact point source

## Worker report

The module `Sheaf.Paper.CompactPointSourceNormalization` states the node in the ordinary
unbounded derived category of `ModuleCat A`, using the existing small-etale module-sheaf
encoding. Its only theorem is `AlgebraicGeometry.Etale.CompactPointSource.
compactPointSourceNormalization`, with proof `sorry`. All other declarations construct
canonical objects or arrows from existing functors; no data or auxiliary proposition is
postulated. The natural-language statement and the live stage-1 `stmt_deps` are unchanged.
`lem-trf-derived-sections-finite-pushforward-modules` remains in `proof_deps` only;
the statement constructs its augmentation directly from the derived-functor unit.

Hypotheses, individually:

- The algebraically closed field is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and
  S is literally `Spec (.of Ω)`.
- A finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the existing six-functor size convention. Every finite ring can be represented
  here; there is no condition relating its characteristic to that of Ω.
- The schemes are `{U Y : Scheme.{u}}`. The structure map is
  `(q : Y ⟶ Spec (.of Ω)) [IsProper q]`.
- The finite Noetherian affine-cover condition is `[IsNoetherian Y]`. Mathlib's
  `AlgebraicGeometry.IsNoetherian` is locally Noetherian plus quasi-compact, equivalent
  to the stated finite affine cover; see `isNoetherian_iff_of_finite_iSup_eq_top`.
- The open immersion is `(j : U ⟶ Y) [IsOpenImmersion j]`.
- The closed rational point is `(i : Spec (.of Ω) ⟶ U) [IsClosedImmersion i]`.
- k is written everywhere as the specified composite `i ≫ j`. Its closedness is the
  separate binder `[IsClosedImmersion (i ≫ j)]`.
- The specified section equation qk=id is `_hqk : (i ≫ j) ≫ q = 𝟙 (Spec (.of Ω))`.
- Invertibility of the actual counit is `[IsIso (counit A i j)]`, not a freely chosen
  morphism or comparison isomorphism.

Objects, identifications and conclusions, individually:

- `derivedSections A Y` names the existing `rightDerivedGlobalSections (ModuleCat A) Y`
  specialization once. `sheafDerivedSections A Y` composes the existing degree-zero
  embedding with that functor. These construct no different functor and assume no
  extra data; the maps share their canonical instance arguments to keep kernel
  checking inexpensive. `fromSections` shares the single-complex map followed by
  augmentation used by both of the specified constant-section arrows.

- `coefficients A X` specializes the recorded `constantSheaf` functor to the regular
  module `ModuleCat.of A A`, giving A_X. The sheaf category is exactly
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`.
- F is `(lowerStar (ModuleCat A) (i ≫ j)).obj (coefficients A S)` and G is
  `(lowerStar (ModuleCat A) i).obj (coefficients A S)`.
- `restrictionIso A i j` composes the canonical `upperStar`/open-restriction
  identification, the direct-image composition isomorphism, and the counit of
  open restriction followed by open pushforward. These are the usual fibre-product
  pasting identifications: on corresponding sections the map is the identity.
- `counit A i j` first applies j_! to `restrictionIso.inv`, then uses
  `openImmersionLowerShriekUpperStarAdjunction.counit.app F`. Thus it is exactly e.
- Compact support for the specified compactification (j,q) is represented as the node
  explicitly requests: `RΓ(Y,j_!G)`. The source of `(derivedCounitIso A i j).hom` is that object.
  No different compactification or compactification-independence is assumed.
- `closedUnit A (i ≫ j)` is the actual `upperStarLowerStarAdjunction` unit at A_Y,
  followed by k_* of the canonical constant-pullback isomorphism. Thus it is u.
- `sectionsAugmentation` composes `DerivedCategory.quotientCompQhIso` with
  `(Sheaf.Γ ...).rightDerivedFunctorUnit` directly, transporting termwise sections
  through the homotopy quotient and using the canonical single-complex comparisons.
  It is the natural augmentation on a sheaf in degree zero.
- `constantSection A Y` first applies the degree-zero embedding to the actual
  `constantSheafΓAdj` unit and then applies that augmentation. This is precisely η.
- `pointSection A k` uses constant sections on S, the inverse of
  `lowerStarCompGlobalSectionsIso` at A_S, and the same derived augmentation. Its H⁰
  map is a↦a under Γ(Y,k_*A_S)=Γ(S,A_S)=A, in particular 1↦1.
- The quantified β is an isomorphism from RΓ(Y,F) to A[0] in the actual derived
  category. The normalization `pointSection A k ≫ β.hom = 𝟙 _` means its degree-zero
  map is the specified identity on sections. It is equivalent to the node's
  normalization: `pointSection` is an isomorphism by finite pushforward and point
  cohomology, and maps between degree-zero coefficient objects are determined by H⁰.
- `∃! β` expresses the canonical nature of this normalized isomorphism; no scalar
  multiple can satisfy the displayed normalization. The conjunction inside ∃! includes
  both required equations. Requiring uniqueness there is equivalent to uniqueness
  under the normalization alone, since both equations follow for the normalized β.
- `unitSection A k` is η followed by RΓ(u), so
  `unitSection A k ≫ β.hom = 𝟙 _` is β∘RΓ(u)∘η=id in Lean's left-to-right convention.
- `derivedCounitIso A i j` is the functorial image of `asIso e`, and its hom is RΓ(e). The literal expression
  `inv ((derivedCounitIso A i j).hom ≫ β.hom)` is λ, with its required domain A[0] and codomain
  RΓ_c(U,G). The last equation is λ followed by RΓ(e) equal to η followed by RΓ(u),
  i.e. the node's second equation. It uses no scalar or arbitrary lift.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` / `IsAlgClosed` for the field.
- `Mathlib.AlgebraicGeometry.Scheme` / `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.OpenImmersion` / `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` /
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.RingTheory.Noetherian.Defs` / `IsNoetherianRing`, through the equivalent
  `Mathlib.AlgebraicGeometry.Noetherian` scheme interface.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves` documents the module-sheaf encoding;
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its coefficient dependency
  give `AlgebraicGeometry.Etale.DerivedCategoryModule`, the ordinary derived category.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` / `lowerStar`, `upperStar`,
  `upperStarLowerStarAdjunction`, `lowerStarComp`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` /
  `openImmersionLowerShriek`, `openImmersionRestriction`,
  `upperStarIsoOpenImmersionRestriction`, `openImmersionRestrictionLowerStarAdjunction`,
  and `openImmersionLowerShriekUpperStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf` /
  `constantSheafCompUpperStarIso`, fixing the constant-pullback identification in u.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf` / `CategoryTheory.constantSheaf` and
  `Mathlib.CategoryTheory.Sites.GlobalSections` / `constantSheafΓAdj`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections` /
  `lowerStarCompGlobalSectionsIso`, the specified direct-image section comparison.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` /
  `rightDerivedGlobalSections` and `rightDerivedLowerShriekOfCompactification`:
  its chosen candidate uses extension by zero followed by unbounded right pushforward.
  The statement uses the node's explicit RΓ(Y,j_!G) realization of compact sections.
- `DerivedCategory.quotientCompQhIso` /
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` and
  `(Sheaf.Γ ...).rightDerivedFunctorUnit` /
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs` give the canonical
  augmentation directly.
- `Sheaf.TraceFormula.DerivedSectionsFinitePushforwardModules` is imported privately
  for the proof dependency `derivedSectionsFinitePushforwardModules`; neither its
  theorem conclusion nor its helper `finitePushforwardSectionsUnit` is used in the
  statement or any of its definitions.
- The stated proof dependencies are imported privately, including the existing
  injective-resolution, geometric-point, module/abelian, single-complex full-faithfulness
  and bounded/unbounded comparison interfaces. Their full five-step use is in the
  theorem docstring, including the actual-unit degree-zero calculation.

Sources opened: Stacks `etale-cohomology.tex`, labels
`proposition-finite-higher-direct-image-zero`, `theorem-equivalence-sheaves-point`,
`lemma-compare-cohomology-point`; `sites-cohomology.tex`, labels
`lemma-cohomology-modules-abelian-agree` and `lemma-derived-pushforward-composition`;
the current blueprint `thm-pur-rank-one-thom.proof.md`, Step 2.

Edge cases checked before stating:

- A=0 is permitted: all coefficient objects and arrows are zero and the unique
  isomorphism and both equations still have their intended meaning.
- U=Y=S and both immersions identity: the counit and closed unit reduce to their
  canonical identity identifications, and the section-normalized β is the point
  cohomology comparison.
- Disconnected Y with the point on one component: F and G have zero restriction away
  from the point; no connectedness of Y or U was introduced.
- Nonreduced Y is permitted. A closed point has finite pushforward without requiring
  reducedness, smoothness, purity, or invertibility of the coefficient characteristic.
- U or Y cannot be empty under the given maps from the nonempty field spectrum;
  no additional nonemptiness assumption is imposed.
- No boundedness restriction is put on the derived category; the particular sheaves
  are embedded in degree zero as in the node. No universe equality is imposed.

Actual searches for an existing statement:

- `msearch.py`, LeanFinder: "Compactly supported etale cohomology of a closed rational
  point skyscraper is the coefficient ring in degree zero, with the constant section
  one normalized to one". Eight hits: structure-sheaf stalk/sections declarations
  and topological skyscrapers, none the specified derived etale module comparison.
- `msearch.py`, Loogle: `constantSheafΓAdj, rightDerivedGlobalSections,
  lowerStarCompGlobalSectionsIso`. Zero hits; service reports unknown identifier
  `constantSheafΓAdj`. This does not assert the declaration is absent locally: it was
  found and used by direct source search.
- `msearch.py`, Mathlib grep: `compactPoint|compact_point|pointSource|point_source|
  skyscraper` in AlgebraicGeometry. Zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `compactPoint|compact_point|pointSource|point_source|lem-pur-compact-point-source-normalization`:
  no matching theorem, only unrelated adic compact-point structures and a private
  countable-product helper. Separate source searches found and reused the constant
  pullback, direct-image sections, adjunction, and derived augmentation APIs.
- No new definition node or dependency replacement is necessary: every needed notion
  already exists, and the helpers specialize or compose those canonical constructions.

No statement dispute or source correction.

Compilation: `scompile.py` checked both its private sandbox module and the actual delivery
module separately. Sharing the existing functor composites reduced kernel checking from
the timeout to 6–10 seconds; the final line-length warning was corrected before dry run.


## Repair of H2 (immutable head 0e15772e5bb4)

The saved packet first passed `deliver2.py --no-push` (commit 5cd454a29d7), but the
reviewer's H2 objection still applied. The repair follows the second proposed option:
`sectionsAugmentation` now constructs the augmentation directly from
`DerivedCategory.quotientCompQhIso` and `(Sheaf.Γ ...).rightDerivedFunctorUnit`.
There is no call to `finitePushforwardSectionsUnit` in the module. The direct
construction is the same composite, specialized to the single complex of the sheaf;
it changes none of the section arrows or the theorem's signature.

Removed `lem-trf-derived-sections-finite-pushforward-modules` from `stmt_deps`,
restoring exactly the live stage-1 list; retained it in `proof_deps` and changed its
import to a private proof import. Added explicit public imports of the recorded
unbounded derived-sections and direct-image sections modules. Comparing the saved
node to current main confirms that only `lean` differs. No definition node, statement
correction, dependency repair or proof change is required.

## Self-check by Q04 after repair

Read the return, the saved node and module, and current main's stage-1 node. The
maintainer's independent review already matched every hypothesis and clause and
found only H2. After repair the theorem signature remains verbatim the saved
signature, with the same coefficients, actual adjunction maps, normalization and
two equations. The direct augmentation is the defining composite formerly reached
through the finite-pushforward helper, so the checked edge cases are unaffected.
No additional worker was started, as required by the dispatcher brief. The independent
review of the final delivery remains the maintainer's responsibility.


Repair validation: `scompile.py Q04 lem-pur-compact-point-source-normalization
lean/Sheaf/Paper/CompactPointSourceNormalization.lean` compiled the sandbox module
(18.9 s) and delivery module (24.0 s) without errors or warnings. The final self-check
also verified the verbatim `lean.statement`, explicit universe and auto-implicit
settings, a single postponed theorem, no call to the finite-pushforward helper, and
all Lean lines at most 100 characters.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
