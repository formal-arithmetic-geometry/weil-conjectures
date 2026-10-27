## Worker report

The module `Sheaf.CategoryTheory.CondensedUnipotentBoundaryNaturality` states all
parts of `lem-sfb-condensed-unipotent-boundary-naturality`, using the already
constructed unipotent extension and normalized ordinary derived functors. Its
seven public theorems all have `sorry` as their entire proof. No definition,
extra node, dependency module, or mathematical statement correction is needed.
Only the item's `lean` record changes.

The sources read were the item's statement and all eight proof steps; each of
its eight statement-dependency nodes and their recorded declarations; the current
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3); and the recorded Mathlib SES-boundary and exact-functor interfaces.
The current blueprint paragraph supplies the direct-image context. The detailed
unipotent calculation is explicitly agent-formulated in the node, with an exact
external reference wanted; the module preserves that attribution.

Clause-by-clause correspondence:

* The small coherent profinite site and coefficient-size convention are the
  imported `CondensedBar.Ring.{u}`: `CommMon (Sheaf (coherentTopology
  Profinite.{u}) AddCommGrpCat.{u+1})`. Thus `A` and `A'` are arbitrary
  commutative condensed rings, including the zero ring, rather than just rings
  presented by topological rings. The internal module category is the recorded
  `Modules A`, transparently Mathlib `Mod`. `universe u` is explicit.
* `G` and `H` have exactly `Group`, `TopologicalSpace`, `IsTopologicalGroup`.
  No compactness, separation, discreteness or profiniteness is assumed.
  `Equivariant A G` is the recorded `ActionModule` on all `C(S,G)` sections;
  inverse group elements make its linear endomorphisms automorphisms.
* The normalized invariant subsheaf and inclusion, computation unit, exact
  trivial inflation, canonical derived adjunction, and ordinary unbounded
  derived categories are those of `CondensedDerivedInvariants`. The formulas
  use `derived`, `groupDerived`, `scalarDerived`, and `scalarBase`, all in
  `DerivedCategory.{u+1}`, without introducing another model or comparison.
* `a : Character A G` is exactly the natural family on every profinite test
  object, with identity value zero and additive multiplication law. Actual
  precomposition is `a.restrict v`; actual coefficient composition is
  `a.coefficients φ`. `v : H →ₜ* G` is an arbitrary continuous group
  homomorphism and `φ : A ⟶ A'` an arbitrary condensed ring morphism.
* `unipotentBoundary_positive` gives short exactness of `extensionSequence a`
  and the two coordinates `first(act g z)=first z+a(g)*second z` and
  `second(act g z)=second z`. Linearity, the group law and naturality are
  part of the imported `UnipotentAction` and `extension` structures. The
  actual underlying object is `Mod.regular A.X ⊞ Mod.regular A.X`.
* The actual maps i and p are the imported `extensionInclusion` and
  `extensionProjection`, whose underlying maps are `biprod.inl` and
  `biprod.snd`; the endpoints are `regularTrivial A G`. The boundary is
  `(extensionExact a).singleδ`, not a chosen arbitrary triangle arrow.
* The displayed formula for xi and its identification with the positive
  class uses the existing definitions, without restating a definition:
  `classShifted a = (baseUnitIso A).inv ≫ cupUnit ≫ derived.map
  (extensionExact a).singleδ ≫ derived.commShiftIso(1).hom.app(coefficient)`;
  `characterClass a` is its shift by -1 followed by `shiftFunctorCompIsoId`.
  In particular the domain is the actual regular module R[-1].
* The positive section defect is the last conjunct of
  `unipotentBoundary_positive`, on every S and g: `act g t(1)-t(1)` is the
  first inclusion of `a.app S g`. The second inclusion is the underlying
  splitting. The character laws show that this is the normalized cocycle +a,
  including its naturality under all base changes. No comparison with a
  complex of underived continuous cochains is asserted.
* `unipotentBoundary_restriction` asserts an isomorphism between the
  restricted extension and `extension (a.restrict v)`, with underlying map
  exactly identity. Its next two equations preserve i and p, with the
  trivial endpoint comparisons being literal identities. Its fourth equation
  preserves the splitting `biprod.inr`. The other conjunct is the boundary
  equation for `groupDerived`, with `coefficientRestriction` and the signed
  `commShiftIso (1 : ℤ)`. Thus the whole sequence and its canonical boundary
  are identified, not merely their eventual classes.
* `unipotentBoundary_scalarSequence` supplies the actual equivariant middle
  map. After the specified `scalarAction.underlying` comparison it is
  `biprod.desc (regularScalar φ ≫ scalarModules.map biprod.inl)
  (regularScalar φ ≫ scalarModules.map biprod.inr)`, which is precisely
  `(x,y) ↦ (φ(x),φ(y))`. The following two equations give both endpoint
  maps `regularScalarAction φ`; the last equation is `v t=t' φ` under the
  same underlying comparison. The type of f already requires linearity
  after scalar restriction and equivariance on every generalized section.
* `unipotentBoundary_scalarBoundary` is the scalar connecting square in the
  ordinary derived action category. It retains `coefficientArrow φ` at
  both endpoints and the canonical signed shift comparison of scalar
  restriction. `unipotentBoundary_coefficientConnecting` then states its
  image under normalized derived invariants: the last-arrow square with
  `coefficientCupMap φ`, including the scalar shift comparison. This
  explicitly covers the node's normalized coefficient connecting square.
* `unipotentBoundary_naturality` is the pair of requested derived equalities.
  Its first conjunct is `characterClass a ≫ groupCupMap v =
  characterClass (a.restrict v)`. Its second is the coefficient equality,
  with `baseRingArrow φ` shifted by -1, the inverse scalar `commShiftIso`
  on the actual regular-module object, and `scalarBase.map` of
  `characterClass (a.coefficients φ)`. Lean composition is left-to-right,
  explaining the order relative to the TeX formulas.
* `unipotentBoundary_zero` states both the zero boundary and zero class for
  any character vanishing on every S and g. Thus it states the a=0 clause
  without needing a second zero-character definition. The trivial group
  case forces a=0 by `Character.one`; the zero ring case has only zero
  sections. No nontriviality hypothesis excludes either case.

Dependency declarations used (full names are in the indicated namespaces):

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, via
  `CondensedBar.Ring`'s bundled commutative specialization. No replacement
  ring, site, or section object is defined.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`,
  its morphisms and scalar restriction. The signatures and docstrings of
  the structure, Hom and regular construction were read.
* `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.ActionModule`, `Equivariant`, `inflate`,
  `trivial`, and the original internal module category.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`; the former is localization at quasi-isomorphisms.
* `Sheaf.CategoryTheory.CondensedDerivedInvariants`:
  `CategoryTheory.CondensedDerivedRestriction.derived`, `groupDerived`,
  `scalarDerived`, `scalarBase`, `scalarAction`, `regularTrivial` and their
  exactness and canonical signed-shift structures.
* `Sheaf.CategoryTheory.CondensedDerivedCup`: in the same namespace,
  `coefficient`, `cohomology`, `cupUnit`, `baseUnitIso`,
  `coefficientRestriction`, and `groupCupMap`.
* `Sheaf.CategoryTheory.CondensedUnipotentClass`: `Character`,
  `Character.restrict`, `Character.coefficients`, `first`, `second`,
  `extension`, `extensionSequence`, `extensionInclusion`,
  `extensionProjection`, `extensionExact`, `extensionOneSection`,
  `classShifted`, `characterClass`. Every relevant full signature and
  docstring, including the actual data in the definitions, was read.
* Its public dependency `Sheaf.CategoryTheory.CondensedScalarTensor`:
  `regularScalar`, `regularScalarAction`, `scalarModules`,
  `coefficientArrow`, `baseRingArrow`, `coefficientCupMap`.
* Proof imports: `Sheaf.CategoryTheory.CondensedRestrictionMateNormalization`
  for the normalized restriction mate; Mathlib `DerivedCategory.ShortExact`
  for the canonical SES triangle; Mathlib `DerivedCategory.Ext.Map` for
  exact-functor boundary comparison. The proof dependencies for injective
  infrastructure, cup-mate coherence, and scalar-restriction interchange
  have no recorded module in the checkout, so none is invented or imported.
  All statement dependencies above are public through the unipotent-class
  module's public dependency chain. The size convention has no declaration
  and is implemented by the displayed universes.

Edge cases checked before drafting: a=0 makes the second inclusion equivariant;
a trivial group forces every section character to be zero; the zero ring gives
zero coordinates; the empty profinite test object has its unique sections.
The identity restriction and identity coefficient map give the same maps under
the prescribed comparisons. Noninjective or nonflat coefficient maps are allowed:
this is restriction of scalars, not extension of scalars. No hypothesis excludes
any characteristic or nonprofinite topological group.

Searches actually run with `msearch.py Q144
lem-sfb-condensed-unipotent-boundary-naturality`:

* LeanFinder: `The unipotent extension of internal condensed modules has
  positive connecting class natural under group restriction and scalar change`.
  Eight hits: condensed solid modules and Nobeling exactness; none is this
  internal-action/normalized-derived-boundary statement.
* Loogle: `"ShortComplex", "singleδ"`. Seven hits: the actual general
  `ShortComplex.ShortExact.singleδ` and its exact-functor comparison lemmas.
  These are used; none states the condensed unipotent calculation.
* Grep: `(unipotent|characterClass).*(condensed|Condensed)|(condensed|Condensed).*(unipotent|characterClass)`.
  No Mathlib hits.
* LeanSearch: `Naturality of the positive unipotent extension connecting
  morphism for internal condensed group representations`. Eight hits, chiefly
  condensed-morphism naturality and ordinary group-cohomology functoriality;
  none is the required statement.
* `rg -n 'unipotent|characterClass|boundaryNaturality|boundary_naturality'
  lean/WeilConjectures lean/Sheaf` and plain grep of the item id in
  `lean/WeilConjectures`: no upstream declaration for the item. The Sheaf
  hits give the recorded unipotent constructions and `restrictionClass` /
  `coefficientClass` in `CondensedDerivedRestrictionCalculus`. Those two
  individual formulas do not give this node's full sequence identifications,
  boundary squares, positivity and zero clause. That downstream module is
  not imported: it uses this node in its proof plan. No notion is redefined.

There is no STATEMENT-DISPUTED finding. Validation uses only the authorized
`scompile.py` and `deliver2.py` wrappers; no live file or git state was edited.

## Second reading by Q144

I reopened the node and delivered file for a second clause-by-clause pass.
This is a self-check, not a claim of review by a separate agent: the assignment
explicitly prohibits starting agents and reserves independent review to the
maintainer.

The ring is still arbitrary condensed and commutative; the group hypotheses
remain only those of a topological group. The action formula and positive defect
refer to every profinite test object, and the first inclusion and second
projection are the actual endpoint maps. The class is the existing construction
from `(extensionExact a).singleδ`, so no arbitrary connecting arrow or choice of
sign has entered. The restriction isomorphism's underlying identity fixes i, p
and t; the boundary formula uses the original exact localized functor and its
signed shifts. The coefficient middle map is fixed by its underlying biproduct
desc, and both endpoints are the original ring map. I added the explicit
`unipotentBoundary_coefficientConnecting` square after this pass so that the
normalized invariant connecting square is stated before the final shifted class
formula, rather than left to be reconstructed by the reader. I removed a
redundant definitional reassertion of `characterClass` and explain the existing
formula above. The first compiler found that subtraction needed the explicit
section-carrier `@Sub.sub` already used upstream in `extensionPositive`; that was
repaired without changing the formula. All theorem proofs remain solely sorry.

The zero assertion includes zero boundary as well as zero class. A vanishing
character is expressed by its pointwise zero property, and the trivial group
and zero ring are covered without nontriviality assumptions. There are no new
nodes or dependency repairs, and no original node field besides lean changes.
