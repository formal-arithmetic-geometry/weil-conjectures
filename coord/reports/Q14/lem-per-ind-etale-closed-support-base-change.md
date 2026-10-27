## Worker report

The module `Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange` states the accepted
node unchanged. Its only postponed proof is
`AlgebraicGeometry.Etale.indEtale_closedSupport_baseChange`.
Two helper definitions construct actual canonical data: termwise closed direct-image exchange
and its mate under the actual bounded-below support adjunctions. There is no new support
functor, arbitrary comparison map, choice of a merely existent isomorphism, or new axiom.
The stage-1 repair note is resolved: its reconstructed 2026-10-24 split, rather than the
withdrawn theorem attachment, supplies the proof plan. No excluded completion comparison,
excellence hypothesis, SGA source, or constructibility theorem is used.

Hypothesis and conclusion correspondence:

- The finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The coefficient universe is the published six-functor convention; finite rings can be
  represented in this universe, including the zero ring. No invertibility is assumed.
- Noetherian source and target of g are `[IsNoetherian T] [IsNoetherian T']`.
  Mathlib's class is locally Noetherian plus quasi-compact, equivalent to the stated finite
  cover by spectra of Noetherian rings. Noetherian rings use `IsNoetherianRing`.
- Affineness is `[IsAffineHom g]`. Local ind-etaleness is `hg`: for every affine open V in T,
  `(g.app V).hom` satisfies the dependency's `RingHom.IndEtaleAcrossUniverses`.
  Since g is affine its full preimage is affine, and this is precisely the affine-chart
  condition for an affine locally ind-etale morphism. Restrictions to smaller affine charts
  follow by localization; conversely these full-preimage charts form a cover.
- Closed immersions are `[IsClosedImmersion i]` and `[IsClosedImmersion i']`.
  The latter structure is the base-change closed immersion already named in the statement;
  it follows from the square and imposes no additional mathematical condition.
- `sq : IsPullback h i' i g` presents Z' as the fibre product with its two projections.
  Using any presented Cartesian square, rather than only Mathlib's chosen pullback object,
  preserves all cases and makes the composition clause literal.
- `j`, `j'`, their open-immersion instances, and `hij`, `hij'` present the open complements
  already used in the node's definition of a^!. The range equalities are exactly
  complementary closed/open ranges. Such complements always exist; these are presentations
  of the specified construction and do not restrict the closed immersions.
- The coefficient categories are `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`
  and likewise on Z, T', Z'. These are the dependency's constant-A module-sheaf encoding.
  The categories in the main assertion are `DerivedCategory.Plus` of these categories,
  not constructible subcategories and not only individual cohomology groups.
- The exceptional inverse image is exactly
  `(closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctorPlus`.
  `closedUpperShriek` is the existing `sectionsWithSupport` kernel followed by `upperStar i`.
  Thus it is R of the supported kernel specified in the node, not an arbitrary right adjoint.
- Exact inverse images and closed direct images are `upperStar ... .mapDerivedCategoryPlus`
  and `lowerStar ... .mapDerivedCategoryPlus`. The latter is already exact.
- `closedDirectImageBaseChangePlus` is obtained from the existing finite-exchange
  `baseChangeMap` by `asIso`, `mapDerivedCategoryPlusNatIso`, and the canonical exact-functor
  composition identifications. The isomorphism proof is the published finite-exchange
  theorem. Its data is not chosen from an uncharacterized existence theorem.
- `closedSupportBaseChangePlus` is `mateEquiv` applied to inverse closed exchange, using
  `(lowerStarClosedUpperShriekAdjunction ...).derivedPlus` on each closed immersion.
  This fixes the canonical comparison before asserting that it is invertible.
- The first conjunct `IsIso (...)` states that this natural transformation is a natural
  isomorphism on all D^+. All its components and inverses are morphisms in derived
  A-module categories, hence A-linear. There is no coefficient forgetting in its definition.
- The second conjunct `NatTrans.CommShift ... ℤ` states compatibility with every cohomological
  shift, using the existing right-derived shift structure and exact pullback shift structure.
- The third conjunct spells out `c ≫ i'_*(beta) ≫ epsilon' = g^*(epsilon)` for every K.
  This fixes precisely the mate normalization specified in the node.
- The fourth conjunct quantifies over a second affine locally ind-etale g₂ with Noetherian
  source, its Cartesian square, and its complementary open. `sq₂.paste_horiz sq` is the
  composite square. The displayed equation compares the pasted beta maps with the single
  composite beta, using `upperStarCompDerivedPlus` for h₂/h and g₂/g.
- The final conjunct spells out the identity law using `IsPullback.id_horiz i` and
  `upperStarIdDerivedPlus`. It includes identity base change explicitly.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme interpretation is
  `Mathlib.AlgebraicGeometry.Noetherian.IsNoetherian` (namespace AlgebraicGeometry).
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: `RingHom.IndEtaleAcrossUniverses`,
  transporting to the existing `RingHom.IndEtale`; its publicly imported
  `Algebra.IndEtale` is a filtered colimit of finitely presented etale algebras.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`; its universal property is presented by `IsPullback`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, the `Sheaf ... (ModuleCat A)` encoding,
  and Mathlib's `DerivedCategory.Plus`.
- Section 1(B) repairs rebind `def-pur-etale-supported-kernel` to
  `AlgebraicGeometry.Etale.sectionsWithSupport` and `closedUpperShriek`, and
  `lem-pur-etale-supported-kernel-adjunction` to
  `AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction`, all in
  `WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek`.
  The former records were specialized to AddCommGrpCat and did not expose the actual
  module-valued supported inverse image and adjunction used here. The general upstream
  declarations specialize to precisely the abelian-sheaf notions of the dependency nodes,
  and also supply their constant-A module versions. Only the two dependencies' `lean`
  fields change; their statements and every other field stay unchanged. Their notes
  explain the old interface defect, the replacement, and all clauses of each node.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  the published module-valued-sheaf encoding implements modules over this constant sheaf.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`.
- `def-weil-pbc-underived-exchange` records `Etale.baseChangeMap` in
  `WeilConjectures.SixFunctors.BaseChange.Square`. It defines the map localized in c.
- `lemma-weil-pbc-finite-exchange` records `Etale.isIso_baseChangeMap_of_isFinite` in
  `WeilConjectures.SixFunctors.Finite.BaseChange`. This theorem is used in the construction
  of c through `asIso`, so it is a statement dependency as well as a proof dependency.
- `prop-weil-pbc-derived-inverse-image-adjunction` records
  `CategoryTheory.Adjunction.derivedPlus` in the published PlusAdjunction module. Its
  general exact-left-adjoint construction derives the actual closed-support adjunction.
- `def-weil-pbc-derived-inverse-image` records `Functor.mapDerivedCategoryPlus` in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, the exact-functor
  localization used for both pullbacks and exact closed direct images here.
- `lem-weil-pbc-derived-inverse-image-composition` records
  `Etale.derivedInverseImageComposition` in `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`.
  Its publicly imported `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`
  supplies the `upperStarCompDerivedPlus` and `upperStarIdDerivedPlus` used in the statement.
- `CategoryTheory.mateEquiv` is the recorded adjunction-mate construction.
- Proof-only imports include the recorded ambient/support triangle modules, exact module
  inverse-image and coefficient-forgetting interfaces, exact derived adjunction, triangle
  extension and two-out-of-three, ind-etale stability, open-closed vanishing, and adjunction
  shift compatibility. Derived inverse-image composition is also a statement dependency. The new stage-1 prerequisite
  `lem-per-ind-etale-qcqs-direct-image-base-change` has no Lean module yet, so its import
  is omitted; its role is recorded explicitly in Step 6 of the theorem docstring.

Edge cases checked mathematically before writing: empty Z, empty T or T', zero ring A,
identity i, arbitrary integral shifts (including zero and negative), identity g,
nonconstructible bounded-below K, and positive-characteristic coefficients with no
invertibility on T. For empty support both exceptional inverse images vanish; for full
support the assertion reduces to pullback with the canonical identity identifications.
Neither nonemptiness nor nontriviality is imposed. The Cartesian presentation includes
arbitrary isomorphic realizations of the fibre product. No theorem about unbounded K is
asserted.

Searches (2026-10-24):

- msearch.py leanfinder: "Affine ind-etale base change commutes with derived supported
  inverse image on etale module sheaves" returned 8 hits concerning Kaehler differentials
  and etale morphism/ring-map base change; no derived supported-sheaf comparison.
- msearch.py loogle: "AlgebraicGeometry.Etale.closedUpperShriek,
  AlgebraicGeometry.Etale.baseChange" returned 0 hits (project identifier unknown to
  the Mathlib search index).
- msearch.py grep: "IndEtale|indEtale|closedUpperShriek" returned 0 Mathlib hits.
- msearch.py leansearch: "Etale sheaf local cohomology closed immersion exceptional inverse
  image ind-etale base change" returned 8 hits for closed/etale immersion geometry and
  structure-sheaf stalks, no matching theorem.
- rg in lean/WeilConjectures and lean/Sheaf for closedSupport, supportedKernel,
  closedUpperShriek, IndEtale, and the exact item id found the existing generic support
  construction and finite exchange, but no current statement of this node. The old module
  is absent; lean_removed records its withdrawal and supplies no usable declaration.
- rg in dag/lean_names_upstream.json found no IndEtaleClosedSupport attachment.

No statement correction, disputed statement, or new node is needed. Two existing-declaration
record repairs under Section 1(B) are included; they need no new Lean module.
Compilation is exclusively through scompile.py. Every declaration binds its universes
and variables with autoImplicit false. Only the main named theorem has sorry.

## Second reading by Q14

A separate second pass by the same dispatcher worker (the brief forbids starting other
agents; the maintainer supplies the independent review) checked the actual Lean file
against the node. All geometric hypotheses and all five conclusion clauses above are
present. The first compile exposed only field-access syntax errors, repaired by keeping
`.derivedPlus.counit.app` attached to its receiver. The subsequent check found only two
long lines, which were wrapped. The review additionally made the identity law explicit.
The counit equation has c in the forward direction before i'_*(beta); the defining mate
uses c inverse. Both composition isomorphisms point from pullback along the composite
to successive pullbacks, so the displayed pasting equation has matching source and target.
The statement uses actual D^+ functors and actual natural transformations, rather than
unrelated per-degree isomorphisms. The two helper definitions have full construction data.


## Dependency modules

`def-pur-etale-supported-kernel`: existing-declaration repair under Section 1(B), with no
new module. The AddCommGrpCat-only `supportedKernel` attachment did not supply the
module-valued support construction used by the item. The repaired record uses
`sectionsWithSupport` and `closedUpperShriek` from
`WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek`. The first is the
pointwise kernel of the open unit, with kernel-induced maps; the second composes it with
i inverse image. Pointwise kernels compute the functor-category kernel in the dependency
statement. At AddCommGrpCat they give the node's abelian-sheaf notions, while ModuleCat
provides the constant-A module version needed here. Neither a closed nor an open immersion
is required just to define these two functors, matching the dependency's arbitrary i,j.

`lem-pur-etale-supported-kernel-adjunction`: existing-declaration repair under Section 1(B),
with no new module. The old record provided an AddCommGrpCat-only Nonempty adjunction;
the item needs the actual canonical adjunction to derive its counit. The repaired primary
declaration is `lowerStarClosedUpperShriekAdjunction` in the same upstream module. Its
`lowerStarClosedUpperShriekHomEquiv` supplies the stated natural Hom bijection.
For the other clauses, `isZero_upperStar_sectionsWithSupport` and
`isIso_upperStarLowerStarAdjunction_unit_app_of_isZero` give the canonical closed unit
isomorphism on the support kernel; `preservesFiniteLimits_lowerStar` and
`preservesFiniteColimits_lowerStar_of_isFinite` give exactness for the closed immersion.
All are published declarations accessible through the recorded module and listed in the
record. Complementarity written as a range equality is equivalent to the old IsCompl.
Specialization to AddCommGrpCat recovers every clause of the node; ModuleCat supplies
the same construction used by this item. This node is now also in the item's stmt_deps.

## Repair of return 3977feaf3409

H2: added all five requested landed nodes to stmt_deps:
`def-weil-pbc-underived-exchange`, `lemma-weil-pbc-finite-exchange`,
`prop-weil-pbc-derived-inverse-image-adjunction`, `def-weil-pbc-derived-inverse-image`, and
`lem-weil-pbc-derived-inverse-image-composition`. The declaration-to-node correspondence
is given above. Also added `lem-pur-etale-supported-kernel-adjunction` so the actual
sheaf-level support adjunction used in the mate is directly cited.

H4/H13: supplied both requested Section 1(B) existing-declaration records with notes.
The definition now records the general sectionsWithSupport/closedUpperShriek interface,
and the adjunction records lowerStarClosedUpperShriekAdjunction. The Dependency modules
section explains the former interfaces' defects, the exact replacement, and the remaining
unit/exactness clauses. Removed the erroneous claim that no dependency repair was needed.

Compared the retained returned sandbox with the current main node: before this repair,
their only differing field was lean. Rebuilt the item record on the current main node,
retaining the returned Lean signature and adding the six authorized dependency edges.
Copied both dependency nodes from current main and changed only lean. All three natural
language statements, proofs, proof dependencies and review metadata remain as on main.
The Lean module is byte-for-byte unchanged from the returned version (SHA256
15b38d711ed4f147b1edac26d19f401daeb177df0af8002142e3326dbc4e5885).

The repair second pass read both dependency statements and their published declaration
signatures and docstrings. It checked that their AddCommGrpCat specializations retain the
original definitions and all adjunction clauses, that their ModuleCat specializations are
the exact functors and adjunction used by the consumer, and that every requested node is
now directly in stmt_deps. The original mathematical clauses are unchanged, as requested
by the independent maintainer review. Validation uses the unchanged consumer module via
scompile.py, followed by the server dry run and normal delivery wrapper.
