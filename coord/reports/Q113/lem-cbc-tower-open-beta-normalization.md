## Worker report

The module `Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization` states
`lem-cbc-tower-open-beta-normalization`, with all theorem proofs `sorry`.
The primary declaration is
`AlgebraicGeometry.ProEtale.StrictTower.openBetaNormalization`; the node's
`lean.declarations` lists the component statements and canonical helper constructions.
Definitions have real data: adjunctions, specified mates, inverses of named isomorphism
assertions, whiskering, and exact derived descent. No arbitrary isomorphism is chosen.

Sources read: Stacks `proetale.tex`, `definition-extension-zero` (09AE), and
`sites-modules.tex`, `lemma-localize-morphism-ringed-sites` (04J0), including its
restricted structural ring map and sectionwise direct-image identity. Also read the
last sentence of main-20261015 `thm-cbc-complete-proetale.proof.md`, and all nine proof
steps of this node. The normalization and pasting refinement is the node's explicit
categorical refinement of that source, rather than an assertion that 09AE alone states
all the coherence formulas.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The coefficient ring is `B : Type (u + 1)` with `[CommRing B]`. The arbitrary-ring
  results have no `Finite`, topology, torsion, flatness, completeness or Noetherian
  assumption. Schemes and arrows are arbitrary `Scheme.{u}` objects and morphisms.
  This is the existing coefficient/site universe convention; it retains site object
  universe `u+1` and morphism universe `u`.
- Small pro-etale sites, constant rings, module sheaves, strict towers and ordinary
  unbounded localization are exactly the existing `StrictTower.coefficients`,
  `Modules`, `Towers`, `Derived`. In particular `Towers B X = ℕᵒᵖ ⥤ Modules B X`;
  index `n` means positive level `n+1`. It is not a tower of separate derived objects.
- The operations, units and compositors are the recorded `modulePullback`,
  `moduleDirectImage`, `moduleJ`, `moduleJAdj`, `G`, `J`, `jAdj`, `moduleGComp`,
  `gComp`, `jComp`, `gId`, `jId`, `evalG`, `evalJ`, `ev`. `R` and its adjunction are
  already supplied by the operation dependency and are not replaced here.
- A cartesian open square is bound by the four arrows `a,j',j,g`, the two
  `IsOpenImmersion` instances and `sq : IsPullback a j' j g`. The explicitly bound
  `w : a ≫ j = j' ≫ g` is its commutativity (already implied by `sq`), retained to
  pass the specified square to the existing API. This includes arbitrary chosen
  cartesian squares, not just Mathlib's literal pullback object. The recorded
  `OpenImmersionSquare` supplies exactly these data via its inherited chosen
  cartesian square and its two open-immersion fields.
- `openBetaRestriction` is the exchange mate of the canonical `moduleSquareG.inv`.
  `openBetaRestriction_normalized` asserts invertibility and the section identity.
  The concrete `openBetaSectionObjectMap` is the map
  `V ×_U U' → V ×_X X'` preserving the two projections. `openBetaSection` expresses
  the canonical open restriction of a section using the inverse-image unit and
  the map/base-change adjunction unit. The displayed equation compares the same
  section after this canonical restriction; it is not a choice of an unnamed map.
- `openBetaModule_isIso` asserts invertibility of the existing `singleBetaInv`
  for arbitrary B. `openBetaModule` is its inverse, with type
  `moduleJ B j ⋙ modulePullback B g ≅ modulePullback B a ⋙ moduleJ B j'`.
  The first conjunct of `openBetaModule_normalized` says its inverse conjugates
  to the section-normalized restriction comparison under the two specified
  composite adjunctions. Its second conjunct is exactly the open Hom-transpose
  equation, with the pulled-back open unit followed by `moduleSquareG.inv`.
- `openBetaTower` applies this particular comparison termwise, with the existing
  functor composition identifications. `openBetaComplex` applies it in every
  cochain degree. Their natural-isomorphism types include naturality, inverse
  identities, transition compatibility and the differential compatibility.
  `openBetaComplex_component` explicitly identifies every degree/index component
  with the original module comparison. Hence the sheaf equations also hold as
  equations of tower and complex maps by componentwise equality.
- `openBetaNormalization` identifies the existing derived `beta` with exact descent
  of this tower comparison and states the inverse open-unit transpose for every
  `M : Derived B U`. Both conjuncts are before evaluation. There is no appeal to
  faithfulness of derived evaluations and no boundedness hypothesis.
- Base-change composition is `openBetaModuleBaseChangeComp` on sheaves and
  the imported `beta_comp` on derived strict towers. The left side first inserts
  `gComp h g`, then `G_h beta_{j,g}`, then `beta_{j',h} G_a`; the right side is the
  comparison for the composite followed by `J` of `gComp b a`. Composite square
  witnesses are explicit and follow by pullback pasting, so these binders impose
  no extra condition on composable cartesian squares.
- Open composition is `openBetaModuleOpenComp` and the imported `beta_open_comp`. It inserts
  the inverse source open compositor, the two beta maps in the node's order,
  and the target open compositor. `openBetaModuleJComp` is the unique adjoint
  comparison conjugate to the existing `moduleGComp`, exactly as `jComp` is on
  derived towers. The composite pullback witness is again just pasted squares.
- Identity base changes are `openBetaModuleBaseChangeId` and
  the imported `beta_id`; identity opens are `openBetaModuleOpenId` and
  `openBetaOpenId`. These use the specified conjugate `moduleRId`, `gId`, `jId`
  unit comparisons, rather than assuming chosen adjunction units are literal
  identity arrows. The module identity helpers are those same adjoint formulas.
- `openBetaEvaluation` states commutativity with the actual derived `ev`, `evalG`
  and `evalJ`, for every index and arbitrary B. `openBetaSingle` is the exact
  descent of the same sheaf comparison, without a finiteness assumption.
- The finite section binds `[Finite B]` and a discrete topology, as used by the
  existing finite coefficient realization `C`. Every finite ring has this
  canonical discrete topology; it imposes no extra algebraic restriction.
  `openBetaFinitePullHom` is the inverse mate of the published section-normalized
  `cDirect`; `openBetaFiniteOpenHom` is the open inverse mate of that pullback
  comparison. Their named isomorphism assertions give `openBetaFinitePull` and
  `openBetaFiniteOpen`. `openBetaFiniteCompatibility` identifies `openBetaSingle`
  with the dependency's actual `ordinaryOpenExtensionBaseChangeIso`, after these
  unit-preserving scalar-presentation comparisons. The presentation equivalence
  ensures this applies to every constant-ring module object, not just a special
  source of objects. Together with `openBetaEvaluation` this is precisely the
  final finite-evaluation clause.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent general-site abbreviation of Mathlib `SheafOfModules`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`, with the existing n-to-n+1 reindexing convention.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: the ring sheaf,
  module/tower/derived categories, exact pullback, derived direct image,
  adjunctions, compositors, identities and evaluation comparisons listed above.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `moduleJ`, `moduleJAdj`,
  `towerJ`, `J`, `jAdj`, `jComp`, `jId`, `evalJ`.
- `Sheaf.AlgebraicGeometry.OpenImmersionSquare`: `OpenImmersionSquare`.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, its unit/counit
  formulas and `Adjunction.id`. This dependency is a Mathlib leaf without a lean
  record; its `mathlib_match` is usable directly.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`:
  `AlgebraicGeometry.ProEtale.ordinaryOpenExtensionBaseChangeIso`, including its
  specific conjugate of `ProEtale.baseChangeMap` and exact derived descent.
- Three already landed nodes added to `stmt_deps`, with no changes to their records:
  `def-cbc-strict-tower-proper-open-arrows` supplies `squareG`, `beta`, and its
  actual inverse transpose; `def-cbc-finite-constant-coefficient-transport`
  supplies `C`, `finiteRestriction`, `cDirect`; `def-weil-pbc-proetale-modules`
  supplies `finiteCoefficientRealization` and its exactness. None reaches this
  item through statement or proof dependencies, so these additions are acyclic.

Proof imports retain the stated localization theorem, general ringed-site
localization, adjunction-mate transpose, open tensor normalization, and Mathlib
mate-pasting/exact-descent/localization interfaces. The proof-only
`lem-cbc-open-square-section-restriction-mate` is not yet recorded in Lean;
its intended mate formula is spelled out directly here, as the present statement
requires, and its eventual proof module can be added by the maintainer.

Edge cases checked before finalizing: the zero coefficient ring, infinite
commutative rings, empty schemes and empty opens, identity base changes and
identity opens, arbitrary open immersions without quasi-compactness, towers
without uniform boundedness, arbitrary cochain degrees in ℤ, and every positive
level including the first (n=0). None is excluded. Redundant commutativity and
composite pullback witnesses are proof-irrelevant data already forced by the
square hypotheses. Isomorphism helpers are constructed as inverses of the
specified maps and cannot introduce an unrelated comparison.

Searches actually run (also recorded in `searches.jsonl`):

- LeanFinder: “Open extension by zero on pro-etale module sheaves commutes with
  pullback for arbitrary constant rings with the open adjunction unit transpose
  and coherent base change on strict towers”. Eight results: module pullback/free
  generator and unit facts, plus `Scheme.Modules.restrictFunctorIsoPullback`;
  none gives this pro-etale tower normalization or coherence assertion.
- Loogle: `CategoryTheory.Adjunction.leftAdjointCompIso, CategoryTheory.mateEquiv`:
  zero results for that combined query. The actual Mathlib mate declarations
  were then read directly in `Adjunction/Mates.lean` and `Basic.lean`.
- msearch grep: `extension.*zero|open.*base.*change` in `CategoryTheory`: nine
  unrelated extension-closed object-property and triangulated-category results.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `openBetaNormalization`, `openBetaFinitePresentation`, `openBetaFinitePull`:
  no existing declaration. The existing strict-tower beta definition and finite
  evaluation theorem were read and are used; they do not state all the arbitrary
  coefficient, section-normalization and pasting clauses of this item.
- Searched `moduleJComp|moduleJId|openBetaModuleBaseChangeComp|openBetaModuleOpenComp`
  in both project roots: only the separate varying-ring framework has its own
  module compositors, not the present StrictTower ones. The new helpers are
  explicit adjoint comparisons of the existing strict constant-ring operations.

No statement correction, disputed statement, new definition node or dependency
module is needed. All additions belong to the canonical comparison notion of
this item and are listed in its lean record. The interrupted partial attempt had
no node record or report and had not delivered. Its line-length warning was
repaired, and missing sheaf-level coherence statements were added.

## Validation

Every compiler invocation uses the prescribed `scompile.py`, in module mode,
with explicit universe and variable binders and `autoImplicit false`.
All new theorem proofs remain `sorry`; no live source or artifact was edited.
The final dry run and delivery will compile this module again and run server preflight.

## Repair of immutable head c9ad2e860f91

The required initial dry run of the saved packet passed (commit 0fee2f27325),
but self-check against the return confirmed that all four duplicate statements
were still present. They have now been removed, including their entries in
`lean.declarations`; the normalization statement and the node statement stay unchanged.

- `openBetaBaseChangeComp` is removed. The public import of
  `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` supplies `beta_comp`.
- `openBetaBaseChangeId` is removed. The same public import supplies `beta_id`.
- `openBetaOpenComp` is removed. The same public import supplies `beta_open_comp`;
  its private `beta_open_comp_aux` is not duplicated or required separately.
- `openBetaFinitePresentation_isEquivalence` is removed. The proof import
  `import all Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized` supplies
  its existing private `realization_equivalence` for the finite comparison proofs.
  The docstring of `openBetaFinitePullHom_isIso` now names that existing result.

I read each existing declaration's full signature, docstring and surrounding
binders. All have `B : Type (u+1)` and `[CommRing B]`; the first three require
neither finiteness nor properness nor quasi-compactness. Their schemes, arrows,
open instances, commutativity witnesses, pullback witnesses and derived object
binders match the removed statements literally. The finite equivalence has
exactly `[Finite B] [TopologicalSpace B] [DiscreteTopology B]` and `X : Scheme.{u}`,
with conclusion `(C B X B (RingHom.id B)).IsEquivalence`. Thus no changed
`variable` or `open` context distinguishes the old declarations.

No downstream DAG node is added as a statement prerequisite: the existing
calculus statements are reused as the return explicitly requests, while this
node's canonical normalization constructions still use its original dependency
interfaces. Its own node statement, proof and proof dependency list are preserved.

## Self-check by Q113

Read the retained module against the node again after deleting the duplicates.
The section identity remains `openBetaRestriction_normalized`; the specified
inverse open-unit transpose and exact strict-tower descent remain
`openBetaModule_normalized` and `openBetaNormalization`. Tower transition and
complex differential compatibility remain in the natural isomorphisms and
`openBetaComplex_component`. The sheaf composition and identity formulas remain
in the four `openBetaModule*` theorems. The derived composition and base identity
clauses are exactly the imported `beta_comp`, `beta_open_comp`, `beta_id`;
the derived identity-open clause remains `openBetaOpenId`. Evaluation and the
finite canonical comparison remain `openBetaEvaluation` and
`openBetaFiniteCompatibility`, using the existing finite equivalence in their
proof plan. Zero rings, empty opens, identities and arbitrary unbounded towers
remain covered. No hypothesis or conclusion was changed by this repair.

## Second reading by Q113

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
