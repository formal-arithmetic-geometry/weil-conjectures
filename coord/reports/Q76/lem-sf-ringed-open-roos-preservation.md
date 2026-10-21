## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenRoosPreservation` states
`AlgebraicGeometry.Scheme.proEtaleRingedOpenDerived_products_roos`, with one postponed
proof (`sorry`). Its helper `proEtaleRingedOpenDerived` is an abbreviation for the
existing exact functor's `mapDerivedCategory`, with actual data throughout. It extracts
finite-limit and finite-colimit preservation from `proEtale_ringed_open_closed` and
obtains additivity by the existing finite-biproduct API. Choosing the witnesses of that
existing theorem is used only to extract these proof-valued properties; it does not
choose the extension functor, its action, a product comparison or a derived functor
from a mere existence theorem.

The source was read in the local Bhatt--Scholze PDF, Lemma 6.1.13 and its proof,
and in `literature/stacks-project/proetale.tex`, labels `lemma-jshriek-zero`,
`lemma-open-immersion`, `lemma-ses-associated-to-open`, and `lemma-j-shriek-limits`
(Tags 09AG, 09BN, 09AH, 09BP). The ringed refinement is precisely the item's
four-step proof using the already recorded arbitrary-ring sheaf-product theorem.
No statement correction, dependency repair, new DAG node or disputed statement is needed.

Clause-by-clause correspondence (write `J` here for the displayed helper):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Any scheme X, a closed immersion i:Z→X | `{X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]` |
| Complementary quasi-compact open immersion | `(U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]`, with `hU : Set.range U.hom = (Set.range i)ᶜ` |
| Any sheaf of commutative rings R | `R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}` |
| Restricted coefficient ring R_U=j⁻¹R | The open category is `ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)`, exactly the localized-site presentation of the dependency. The equivalence `q` in `proEtale_ringed_open_closed` identifies it with modules over `proEtaleModuleCoefficients ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj R)` and intertwines actual inverse image with `overFunctor`. |
| Ordinary unbounded derived categories | `DerivedCategory` of those module categories, with `HasDerivedCategory.{v}` and `HasDerivedCategory.{w}` as separate universe choices. There is no truncation or bounded subcategory. |
| J=D(j!) is the termwise exact extension | `proEtaleRingedOpenDerived i U hU R`, whose body ends in `(proEtaleRingedExtensionByZero U R).mapDerivedCategory`; exactness is obtained from the recorded open/closed theorem, not assumed. |
| Products exist for every countable family | The conclusion supplies `HasCountableProducts` for both derived categories. These are conclusion witnesses, not additional hypotheses. |
| For every countable family C_n | `∀ C : ℕ → DerivedCategory (...)`. This enumerates arbitrary countable families; the preceding existence witnesses also cover finite and empty countable products. |
| Canonical map J(∏ C_n)→∏ JC_n is an isomorphism | `∃ phi : J.obj (∏ᶜ C) ≅ ∏ᶜ (fun n ↦ J.obj (C n)), phi.hom = piComparison J C ∧ ...` |
| Its nth projection is J of the original projection | `∀ n, phi.hom ≫ Pi.π (fun m ↦ J.obj (C m)) n = J.map (Pi.π C n)` |
| Every inverse system, including arbitrary derived transitions | `∀ d : ∀ n : ℕ, C (n + 1) ⟶ C n`; equivalently this is `Functor.ofOpSequence d`. No complexes representing all transitions simultaneously are assumed. |
| The image of 1-s is 1-s_J after the product identifications | `J.map (towerTransitionEndomorphism d) ≫ phi.hom = phi.hom ≫ towerTransitionEndomorphism (fun n ↦ J.map (d n))` |
| Every given distinguished Roos triangle | Arbitrary `L`, `c : L ⟶ ∏ᶜ C`, `delta : ∏ᶜ C ⟶ L⟦1⟧`, followed by `IsDerivedLimitTriangle d L c delta → ...` |
| The resulting triangle is a distinguished Roos triangle for Jd_n | `IsDerivedLimitTriangle (fun n ↦ J.map (d n)) (J.obj L) (J.map c ≫ phi.hom) (phi.inv ≫ J.map delta ≫ (J.commShiftIso 1).hom.app L)` |
| Its first arrow has components J(c_n) | `∀ n, J.map c ≫ phi.hom ≫ Pi.π (fun m ↦ J.obj (C m)) n = J.map (c ≫ Pi.π C n)` |
| No constructibility, boundedness or constant-ring hypothesis | None occurs in the binders. No qcqs assumption on X occurs either. |

The two localization universes `v` and `w` are independent of the scheme universe `u`.
The small pro-etale site's object/morphism universes are unchanged. The open immersion
is an object of that site because an open immersion is weakly etale; this presentation
adds no mathematical hypothesis. Reindexing the positive-integer tower of
`def-weil-inverse-system` by `n ↦ n+1` gives precisely the natural-number tower used
by the recorded Roos and transition declarations.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms `X ⟶ Y`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (the quasi-compactness component
  recorded by the finite-type node): `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation of Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the standard derived triangulated structure.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`:
  `proEtaleModuleCoefficients`, `proEtaleRingedExtensionByZero`,
  `proEtale_ringed_open_closed`. Their full definitions and theorem signature were read.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, its `CommShift ℤ` and `IsTriangulated` instances.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`, identifying
  the transition-map presentation with the recorded inverse-system notion.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `IsDerivedLimitTriangle`, with the exact `towerTransitionEndomorphism` from
  `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `piObj`, `Pi.π`, `Pi.lift`,
  `piComparison`; `Mathlib.CategoryTheory.Limits.Shapes.Countable`: `HasCountableProducts`.
- Proof-only imports: `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts`
  (`proEtaleRingedExtensionByZero_products`),
  `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived` (`ProEt.products_derived`).
  These implement proof steps 1 and 2, respectively. All other recorded proof
  dependencies enter through the public modules above; no import cycle is introduced.

Edge cases checked mathematically before writing: U empty makes J zero; U=X makes
J equivalent to the identity; the empty scheme and zero coefficient ring give zero
module categories. None is excluded by a binder. Zero families and zero transitions
are allowed (the latter give the identity transition endomorphism); arbitrary unbounded
complexes and nonconstant ring sheaves are allowed. The first arrow and last arrow
have the original sign convention `1-s`; no unnoticed sign change occurs. The
comparison is the canonical map, not an arbitrary chosen isomorphism: its hom is
explicitly equated to `piComparison`. Its nth projection and the first-arrow component
are explicitly stated as requested by the node, despite being immediate from that
normalization and functoriality.

Searches for an existing declaration (all msearch calls were run with group Q76 and
this item; their actual digests are in the sandbox's `searches.jsonl`):

- LeanFinder: `Extension by zero on the ringed pro-etale site preserves countable products in the unbounded derived category and Roos distinguished triangles`.
  Eight hits, including light-condensed countable AB4*, Grothendieck-abelian instances,
  `HasDerivedCategory.standard` and general localization; no match.
- LeanSearch: `Exact extension by zero of sheaves of modules preserves unbounded derived countable products and Roos triangles`.
  Eight hits, including exact short-complex maps, derived zero objects and general
  module-sheaf finite-limit preservation; no match.
- Loogle: `CategoryTheory.Limits.piComparison, CategoryTheory.IsDerivedLimitTriangle`.
  No hits: the latter is a project declaration and unknown to public Loogle.
- Loogle: `CategoryTheory.Limits.piComparison`.
  Twelve hits: canonical comparison, projection equation, preservation criteria and
  product-triangle formulas. These supply the general canonical map, not this result.
- msearch grep in Mathlib `CategoryTheory`: `piComparison|IsDerivedLimitTriangle|proEtaleRingedExtensionByZero`.
  Twenty-five displayed generic product-comparison hits; no ringed open Roos theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `ringed.*[Rr]oos|[Rr]oos.*ringed|proEtaleRingedExtensionByZero|ringed-open-roos-preservation`
  found the existing open/closed and sheaf product interfaces and unrelated Koszul/Roos
  constructions, but no theorem stating this derived product/Roos preservation.
- `rg` in both source roots for `Ringed.*Roos|ringed.*roos|ExtensionByZero.*[Dd]erived`
  found constant-coefficient intrinsic extension consumers and unrelated Roos helpers,
  with no exact statement match. The item id has no upstream source occurrence.
- `rg` in `dag/lean_names_upstream.json` and both source roots for the two proposed
  full declaration name suffixes found no collision.

Validation: compilation and delivery preflight are run using only the prescribed
`scompile.py` and `deliver2.py` wrappers. No live source was edited; no direct Git
operation or global build was run. The source and node were compared again after
writing, including the projection directions, the transition equation and the shift
comparison on the final arrow. Independent review is left to the maintainer, as in
the current direct-delivery instruction.

### Compilation infrastructure failure

Three full-module `scompile.py` attempts failed before elaborating the delivered module.
The first prepared many dependencies, then timed out preparing the existing upstream
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` and failed server
confirmation on an existing dependency import. Subsequent attempts consistently report:

```
Sheaf/CategoryTheory/SiteInverseImageTensor.lean:6:0: error: object file
.../lean/.lake/build/lib/lean/WeilConjectures/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.olean
of module WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings does not exist
```

The prescribed `scompile.py --source` successfully reads that module from the server.
An isolated scratch file importing it also compiles cleanly through `scompile.py`, but
this does not repair loading the full published dependency closure. The third full-module
attempt's server confirmation advances to `ProEtaleInverseImage.lean` and additionally
reports a missing existing upstream object:

```
WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean
```

This is a published-artifact/import-resolution failure in the prescribed compiler path,
not a missing mathematical notion or an elaboration error in this delivery. No upstream
source, compiler tool or build artifact was changed. The new module remains unvalidated;
no clean-compile claim is made.

The required `deliver2.py Q76 lem-sf-ringed-open-roos-preservation --no-push`
confirmed the `ProEtaleInverseImage.lean` / `TensorProduct/Basic.olean` failure on
both the overlay and server confirmation, printing `COMPILE FAILED on the server,
nothing pushed`. It could not reach preflight or elaborate the proposed module.

## Retry of the saved packet (2026-10-21)

As instructed, I first inspected this report and ran `deliver2.py Q76
lem-sf-ringed-open-roos-preservation --no-push` on the retained packet. It failed
before checking the item, while preparing
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleObject`: the overlay
reported a missing published `SheafCohomology/Basic.olean`, and server confirmation
reported a missing published `GrothendieckAbelian/ConcreteCoefficients.olean`.

Two subsequent full-module `scompile.py` retries also failed in that existing
upstream dependency, first for
`WeilConjectures/Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Sheaf.olean`,
then for `WeilConjectures/SixFunctors/Etale/UpperLowerStar/Defs.olean`.
Both local-overlay and server-confirmation paths failed. The current server sources
of all three direct project dependencies were read using `scompile.py --source`.
The required open-closed dependency imports `ProEtaleInverseImage`; the missing
published artifacts are inside this necessary dependency closure, not an optional
import introduced by the item. Removing that dependency would discard the recorded
extension functor and exactness interface and would not be a valid statement repair.
No tool, live source, or published artifact was modified. The saved Lean and node
remain retained and unvalidated. Nothing was pushed.

## Saved-packet repair and validation (2026-10-21)

The next required dry run successfully prepared the dependency closure and reached
the item. The historical missing-artifact failures above no longer blocked it.
Elaboration reported missing `PreservesZeroMorphisms` instances in the helper's
finite-biproduct and additivity constructions. Added the public Mathlib import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero` and explicitly installed
`Functor.preservesZeroMorphisms_of_preserves_terminal_object` after the finite-limit
and finite-colimit instances. The latter is an existing Mathlib construction applied
to the already supplied exactness properties, with no new hypothesis or postponed
proof. The import alone did not resolve instance synthesis; the explicit instance did.

The prescribed full-module `scompile.py Q76 lem-sf-ringed-open-roos-preservation
lean/Sheaf/AlgebraicGeometry/ProEtaleRingedOpenRoosPreservation.lean` then passed
both sandbox compilation (6.0 seconds) and compilation at the delivered library
module path (5.8 seconds), without warnings or errors. The node's recorded theorem
signature is unchanged and was checked verbatim against the repaired source.

## Second reading by Q76

This is the author's required self-check of the retained packet; the maintainer
performs the independent review. Reopened the saved node, module and the current
recorded dependency declarations. The only node-field difference from the current
repository is `lean`; the source has one `sorry`, in the item's theorem, and no
line exceeds 100 characters. All universes and variables are explicitly bound.

The closed immersion, complementary quasi-compact open, and arbitrary commutative
ring sheaf match the first three rows of the correspondence table above. The
current open-closed theorem still supplies the exact functor on the localized
module category and the equivalence with modules over the inverse-image ring.
The helper extracts only its proof-valued exactness properties, then applies the
canonical `mapDerivedCategory`; the zero-morphism instance repair changes neither
its objects nor its action. The independent localization universes remain free.

Rechecked `phi.hom = piComparison`, every projection equation, the arbitrary maps
`d n`, and the transition endomorphism's sign `1-s`. The conclusion quantifies over
every distinguished input triangle via `IsDerivedLimitTriangle`; the output first
arrow is `J.map c` followed by `phi.hom`, and its final arrow is `phi.inv` followed
by `J.map delta` and the canonical shift comparison. These directions match the
node's four proof steps. Empty open, identity open, empty scheme, zero ring and
zero-transition cases are still included. No statement correction, new node or
dependency repair was introduced; the only defect found was the missing explicit
zero-morphism instance, now fixed and compiled.
