## Worker report

Module: `Sheaf.AlgebraicGeometry.QCohTruncationDerivedLimit`. It states both clauses
of lem-pc-qcoh-truncation-derived-limit as two named theorems, both with `sorry`.
There are no new definitions and no changes to the natural-language statement.

Hypothesis and conclusion correspondence:

- Scheme X: `(X : Scheme.{u})` in each theorem, with no geometric assumptions.
- E in D_QCoh(O_X): `(E : schemeDerivedCategory X)` and
  `(hE : schemeDerivedQCohProperty X E)`. This is an ambient derived object together
  with the membership predicate defining the dependency's full subcategory.
- E_n = tau_{>=-n} E for n >= 0: the product family is
  `fun n : ℕ => (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E`, with its
  category explicitly supplied. Index zero is included. Transition n+1 -> n is
  `natTransTruncGEOfLE (-((n+1 : ℕ) : ℤ)) (-(n : ℤ))` applied to E.
- Canonical reconstruction is an isomorphism: the first theorem supplies a
  connecting map δ for `IsDerivedLimitTriangle` with vertex E and first map
  `Pi.lift (fun n => (t.truncGEπ (-(n : ℤ))).app E)`. Thus it is the canonical
  truncation projections, not an arbitrary map to the product, that exhibit E as
  the derived limit. This is the intrinsic Roos-triangle formulation of the
  claimed isomorphism: the recorded derived-limit definition chooses neither
  an Rlim object nor a map into one. Transporting this triangle to a representative
  of Rlim gives the comparison isomorphism; conversely the comparison isomorphism
  transports the Roos triangle to this one. No assertion of uniqueness of arbitrary
  triangle lifts is made.
- Ambient products: all `∏ᶜ` are in `DerivedCategory (SheafOfModules ...)` or in
  `DerivedCategory AddCommGrpCat`, never in `schemeDerivedQCohCategory X`.
- F: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤ AddCommGrpCat.{u})`.
- Additive: `[F.Additive]`, the recorded dependency's additive notion.
- Commutes with countable products: `[PreservesLimitsOfShape (Discrete ℕ) F]`.
  No left-exactness hypothesis is added: the statement requires additivity only.
- RF: the existing unbounded `F.rightDerivedFunctor`, from the source repository.
  The second theorem supplies the target Roos triangle with vertex RF(E), family
  RF(E_n), transitions RF(f_n), and first arrow the product lift of RF applied to
  the very same canonical truncation projections. This expresses the second
  canonical comparison isomorphism, including its compatibility with projections.
- `HasDerivedCategory.{w}` and `HasDerivedCategory.{w'}` bind the choices of
  localization, independently in source and target. The shared SheafOfModules
  category is exactly the dependency's, without the distinct X.Modules instance.
  `HasKInjectiveResolutions` bind the infrastructure for computing derived products
  and RF, as in the landed derived-functor comparison: these exist for module
  sheaves and abelian groups (Grothendieck categories), so do not impose a geometric
  or boundedness restriction. No products-exist assumption is added separately.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.DerivedCategory: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty` (also read `schemeDerivedQCohCategory`).
- Mathlib.Algebra.Homology.DerivedCategory.TStructure:
  `DerivedCategory.TStructure.t`.
- Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE:
  `TStructure.truncGE`, `truncGEπ`, `natTransTruncGEOfLE`.
- Sheaf.CategoryTheory.Triangulated.DerivedLimit:
  `CategoryTheory.IsDerivedLimitTriangle` (also read `IsDerivedLimit`).
- def-sp-left-exact-additive's Mathlib match describes multiple notions:
  `Functor.Additive` is the clause used here. `Functor.rightDerived n` was read;
  it is the individual derived functor on the abelian category, not the unbounded
  RF needed here. The latter is already `Functor.rightDerivedFunctor` in
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs,
  imported via WeilConjectures.Algebra.Homology.HomotopyCategory.Products.
  No replacement dependency module is needed: the dependency's additive notion
  is usable, and the distinct unbounded RF construction already exists upstream.

Source checks: local Stacks tex files are absent on this machine. Opened the actual
Stacks pages https://stacks.math.columbia.edu/tag/08D3 and
https://stacks.math.columbia.edu/tag/08U1. The former gives reconstruction from lower
truncations by affine vanishing; the latter gives preservation by RF under the
stated product-preservation assumption, since the source is Grothendieck and Ab
has exact countable products. The docstrings contain the node's full proof route:
affine vanishing, the ringed-space reconstruction lemma, derived-functor comparison,
and compatibility of the projection maps.

Edge cases: n=0 means tau_{>=0}, with next transition tau_{>=-1} -> tau_{>=0};
casts are into ℤ before negating. Zero E, the empty scheme and zero F are admitted.
No boundedness on E is imposed; arbitrary unbounded quasi-coherent cohomology is
allowed. There is no independent index universe: the tower is ℕ. Scheme universe u
is arbitrary and both localization morphism universes w and w' are explicit.

Searches (2026-10-11):

- msearch leanfinder, `quasi coherent derived category object is derived inverse
  limit of lower truncations`: eight hits, generic DerivedCategory.Q, bounded
  representatives and localization results; none is this theorem.
- msearch loogle, `DerivedCategory.TStructure.t, CategoryTheory.IsDerivedLimit`:
  no hits, unknown identifier CategoryTheory.IsDerivedLimit (project definition).
- msearch grep, `truncGE|derived.*limit` in Algebra/Homology/DerivedCategory:
  fourteen hits on truncation constructions, none reconstructs QCoh complexes.
- msearch leansearch, `quasi coherent complex reconstructed by derived inverse
  limit of truncations`: unavailable, Internal Server Error.
- rg on WeilConjectures and lean/Sheaf for the item id, IsDerivedLimit and
  truncGEπ: no source declaration of the item; found and read the existing Roos
  definition, derived-functor comparison, lower-truncation triangle and upstream
  truncation maps. No duplicate statement exists.

Validation: server single-file compile passes with no errors and no warnings.
No STATEMENT-DISPUTED issue and no statement correction.

## Second reading by J1

Independent verdict: the two theorem signatures render the two clauses of the
node, using its recorded triangle-valued definition of derived limit. No change
to the module, node statement, dependencies or Lean record is needed. This reading
adds only this review to the report.

Source reading: local `literature/stacks-project/*.tex` is absent. I read the actual
`perfect.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex,
including `lemma-nice-K-injective` (08D3), and
`lemma-application-nice-K-injective` (08D4), especially its proof of (2).
I also read `injectives.tex`, `lemma-RF-commutes-with-Rlim` (08U1), from
https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex,
and checked the rendered pages https://stacks.math.columbia.edu/tag/08D3,
https://stacks.math.columbia.edu/tag/08D4 and
https://stacks.math.columbia.edu/tag/08U1. No ambient geometric assumption is
inherited: 08D3 assumes just a scheme and quasi-coherent cohomology. The larger
08D4 lemma also has an integer N and a derived vanishing bound, but the initial
reconstruction paragraph uses only 08D3 and 08U1. The latter independently
requires a Grothendieck source, exact countable products in the target, additivity
and countable-product preservation. Thus omitting N and the vanishing hypothesis
from this extracted node is correct.

Node inventory and item-by-item correspondence (all verdicts: pass):

1. Object X, an arbitrary scheme: `(X : Scheme.{u})` in both signatures. I read
   def-pc-scheme's Mathlib record and the scheme category signature. No field,
   characteristic, Noetherian, separated, quasi-compact or nonempty restriction.
2. Object E in D_QCoh(O_X): `(E : schemeDerivedCategory X)` with
   `(hE : schemeDerivedQCohProperty X E)` in both signatures. I opened
   `Sheaf.AlgebraicGeometry.DerivedCategory`: the ambient abbreviation is
   `DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))`, and the
   predicate is exactly `∀ n : ℤ, ((DerivedCategory.homologyFunctor ... n).obj
   E).IsQuasicoherent`. Its full subcategory carries precisely this predicate.
   An ambient object with its membership proof is the same mathematical datum.
3. Index n >= 0 and object E_n = tau_{>=-n} E: the family indexed by `n : ℕ` is
   `((DerivedCategory.TStructure.t (C := ...)).truncGE (-(n : ℤ))).obj E`.
   I read Mathlib's standard t-structure (strictly bounded representatives,
   `isGE_iff` in terms of all cohomology objects), and `truncGE`. These are the
   dependency's standard truncations, not brutal truncations or a different
   t-structure. Cast into integers occurs before negation.
4. Implicit transition E_{n+1} -> E_n: `natTransTruncGEOfLE
   (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)`, evaluated at E. Its source and
   target follow from the signature `t.truncGE a ⟶ t.truncGE b` for a <= b.
   Mathlib's `π_natTransTruncGEOfLE_app` confirms compatibility with projections.
5. First conclusion, canonical reconstruction in D(O_X): the first theorem
   asserts `∃ δ, IsDerivedLimitTriangle transitions E p δ`, where
   `p = Pi.lift (fun n => (t.truncGEπ (-(n : ℤ))).app E)`.
   I read both `IsDerivedLimitTriangle` and `IsDerivedLimit`, and the underlying
   `towerTransitionEndomorphism`: the triangle has middle map `1 - s`, with
   s's n-th component the next projection followed by the transition. The
   dependency explicitly defines a derived limit as a triple, chooses no object
   and warns that uniqueness is noncanonical. The displayed proposition says
   exactly that E with the specified canonical projections is such a triple;
   transporting to a representative of Rlim gives the claimed comparison
   isomorphism. It does not merely assert that E is abstractly isomorphic to
   some object, and does not assert uniqueness of comparison morphisms.
6. Product category: the first product is in the ambient `schemeDerivedCategory
   X`; the second is in `DerivedCategory AddCommGrpCat.{u}`. Neither is a product
   in `schemeDerivedQCohCategory X`, as the node's parenthetical clause demands.
7. Object F: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
   AddCommGrpCat.{u})`, using the same O_X-module category as E. I checked the
   moduleRings-based category rather than silently using the distinct category
   instance on X.Modules.
8. Additivity and commutation with countable products: `[F.Additive]` and
   `[PreservesLimitsOfShape (Discrete ℕ) F]`. I opened the dependency's Mathlib
   `Functor.Additive` declaration (preservation of addition of maps; equivalent
   to finite biproduct preservation). No left exactness assumption appears.
9. Existence and identity of RF: `F.rightDerivedFunctor` is the upstream total
   unbounded right derived functor. I opened its declaration in
   `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`:
   it derives `F.mapHomotopyCategory ... ⋙ DerivedCategory.Qh`, using
   K-injective resolutions. It is not the dependency's separate `F.rightDerived
   n` on the original abelian category. The recorded additive notion is usable;
   the already existing unbounded construction needs no private definition or
   replacement dependency module.
10. Second conclusion and quantifier order: after X, E and hE, F and its two
    properties, the second theorem asserts `∃ δ, IsDerivedLimitTriangle ...`.
    Its vertex is `F.rightDerivedFunctor.obj E`, its family is RF(E_n), its
    transitions are RF of precisely the transitions of item 4, and its first
    map is `Pi.lift` of RF of the canonical truncation projections. This retains
    every clause and the specified induced map in D(Ab).
11. Infrastructure binders: independent localization choices
    `[HasDerivedCategory.{w} ...]` and `[HasDerivedCategory.{w'} AddCommGrpCat.{u}]`
    are explicit. The two `HasKInjectiveResolutions` binders provide the
    K-injective product construction and RF. I read the imported
    `DerivedCategory.hasLimitsOfShape_discrete` signature: it derives existence
    of the products from these binders and products in the abelian categories.
    Both module sheaves and Ab have K-injective resolutions, so these binders
    exclude no schemes or objects in the node; they add no boundedness or
    exactness hypothesis on F.

Edge cases: the index is fixed to the nonempty countable tower ℕ, so an empty
index set is not a case of this node. At n = 0 the object is tau_{>=0} E and
the next map is tau_{>=-1} E -> tau_{>=0} E, as intended. All integer cohomological
degrees are included and E can be unbounded in both directions. E = 0, the empty
scheme and the zero additive functor are admitted; no nonzero or point binder
excludes them. No characteristic restriction occurs. Scheme universe u is
arbitrary, both derived morphism universes are separately explicit, and the
index is ℕ rather than an independent possibly larger type. All variables and
universes are bound by eye and by the clean server compile.

Independent searches using different wording from the worker:

- `msearch leanfinder "left completeness quasi coherent cohomology sheaves
  homotopy limit truncation"`: eight hits (sheaf cohomology, Grothendieck
  sheaf categories, complex factorization, module-sheaf limits and bounded
  truncation quasi-isomorphisms); none is either statement.
- `msearch loogle "DerivedCategory.TStructure.t.truncGE"`: no hits; the dotted
  expression is not a declaration identifier understood by the service.
- `msearch leansearch "derived category of quasi coherent sheaves is left
  complete"`: service unavailable, Internal Server Error; no mathematical
  verdict inferred from this failure.
- Independent `rg` for `left.?[Cc]omplete`, `[Rr]econstruct`, `IsDerivedLimit`,
  `truncation.*limit` and `limit.*truncation` across WeilConjectures, project
  lean/Sheaf, Mathlib homology and Mathlib triangulated categories. I opened the
  matches: DerivedLimit, DerivedLimitExistence, TowerTransitionEndomorphism
  and DerivedFunctorDerivedLimit. The generic RF preservation statement is
  already present, but does not state reconstruction of E from its truncations;
  it is a proof ingredient, not this node. Other matches are homotopy colimits,
  Milnor sequences and adic reconstruction. Neither clause is duplicated.
- Exact declaration-name and item-id search in project Lean, upstream source
  and `dag/lean_names_upstream.json` found no existing declaration of this item.

No new definition node, dependency module or statement correction is present.
I checked H5/H6/H8/H9: there are no new definitions, the only two theorem proofs
are `sorry`, each docstring names its source and blueprint node and includes
its proof route, including affine vanishing, reconstruction, product comparison
and naturality. The imports support the actual constructions and all lines meet
the 100-character convention. An upstream proof ingredient currently uses
X.Modules' category instance, whereas this statement correctly shares the
moduleRings instance with def-pc-derived-category; transporting that proof
ingredient is stage-3 proof work, not a change to this statement.

Validation: `scompile.py J1 lem-pc-qcoh-truncation-derived-limit` on the module
passed in 3.1 seconds with exit code 0 and no warnings. The node's
`lean.statement` is verbatim the first theorem signature and its `declarations`
records both conclusion theorems. No mismatch found; no right Lean rewritten.
