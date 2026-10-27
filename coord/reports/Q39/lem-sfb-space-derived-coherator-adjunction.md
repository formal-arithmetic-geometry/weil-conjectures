## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceDerivedCoheratorAdjunction` states
`AlgebraicGeometry.AlgebraicSpace.exists_derivedCoheratorAdjunction`, with exactly
one postponed theorem and no new definitions. Its proof is `by sorry`.

Source checked: `literature/stacks-project/spaces-perfect.tex`,
`lemma-better-coherator` (Tag 0CR4), especially the second proof (Brown,
coproducts, compact perfect generator); `derived.tex`, `lemma-adjoint-is-exact`
(Tag 0A8D); Mathlib's adjunction Hom formulas and fully faithful unit theorem
implement the final categorical consequences (Stacks 07RB). This technical
prerequisite is not the blueprint unit's own statement. No statement correction,
new node, or dependency-interface repair is needed.

Hypotheses and clauses, individually:

- Fixed universes: `universe u w`, `Scheme.{u}`, and the explicit
  `[HasDerivedCategory.{w} X.SmallModules]` binder. The site skeleton and module
  sections retain the recorded universe `u`; `w` is independent and specifies
  the chosen localization Hom universe. Neither boundedness nor a universe
  equality is imposed. There are no auto-bound implicit variables.
- Scheme and algebraic space: `{S : Scheme.{u}} (X : AlgebraicSpace S)` use
  Mathlib's scheme and the recorded full subcategory of fppf sheaves with
  representable diagonal and surjective representable etale atlas.
- Quasi-compactness in the item's stated form: `hqc` is existence of a scheme
  `U : Over S` and a map `a : yoneda.obj U ⟶ X.obj.obj` with
  `CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`. Thus it is precisely a
  surjective etale atlas from a quasi-compact scheme, rather than an extra
  assumption on the base or its diagonal.
- Quasi-separatedness in the item's stated form: `hqs` ranges over all affine
  schemes `U,V` over `S` and representable etale chart maps `a,b`. The overlap
  is the presheaf `Limits.pullback a b`. A scheme `W` representing this overlap
  is required to have `CompactSpace W.left`. The isomorphism
  `Nonempty (yoneda.obj W ≅ Limits.pullback a b)` expresses representability
  of this exact fibre product, not an arbitrary substitute. Representability
  already follows from the algebraic-space diagonal (and the cited etale
  fibre-product theorem); compactness is independent of the representing
  scheme. This is exactly quasi-compactness of the scheme overlap in the node.
  No condition is imposed on non-etale affine maps and no assumption is made
  that `S` is quasi-separated.
- The small etale ringed model: `X.SmallModules`, through the existing
  `smallModuleEquivalence`, is the exact specified restriction equivalence to
  the original small-etale module category. Its commutative rings are actual
  regular-function rings and the section universe is unchanged.
- Unbounded derived category: `X.DerivedModules` is the recorded
  `DerivedCategory X.SmallModules`.
- Quasi-coherent cohomology and the full triangulated subcategory:
  `X.DerivedQCoh` is the existing full subcategory for
  `X.derivedQCohProperty`, which tests every integer cohomology sheaf after
  inverse restriction. `derivedQCohProperty_isTriangulated` supplies precisely
  the inherited ambient shifts and distinguished triangles. This is not
  the derived category of the abelian category QCoh.
- Inclusion: `X.derivedQCohProperty.ι` is Mathlib's actual full-subcategory
  inclusion, with object and morphism maps inherited from the ambient category.
- Right adjoint: `∃ (DQ : X.DerivedModules ⥤ X.DerivedQCoh)
  (adj : X.derivedQCohProperty.ι ⊣ DQ), ...` asserts existence of a specified
  adjunction, not merely an arbitrary functor or arbitrary maps.
- Triangulated right adjoint: `@Functor.IsTriangulated ... DQ
  (adj.rightAdjointCommShift ℤ) ...` states exactness using the coherent
  integer shifts canonically induced by this adjunction. This construction
  also makes unit and counit compatible with the inherited inclusion shifts.
  The explicit instance argument avoids hidden statement-local `let` binders.
- Natural Hom bijections: the displayed `Function.Bijective` has domain
  `(P ⟶ DQ.obj E)` and sends `a` to
  `X.derivedQCohProperty.ι.map a ≫ adj.counit.app E`. It has exactly the
  direction and counit formula in the node. Naturality is part of the supplied
  adjunction: this function is definitionally the inverse of
  `adj.homEquiv P E` (Mathlib `Adjunction.homEquiv_symm_apply`), whose
  naturality in both variables is in `Adjunction.Basic`. Thus the conclusion
  includes natural bijections, not merely unrelated pointwise cardinalities.
- Invertible unit: `IsIso adj.unit` means the natural transformation
  `𝟭 X.DerivedQCoh ⟶ X.derivedQCohProperty.ι ⋙ DQ` is an isomorphism.
- No Noetherian, separatedness, finite-type, or finite-dimensional condition
  occurs in the signature. Complexes are not bounded and the base is arbitrary.

Dependency declarations used (their source signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `IsSurjective`, `structureSheaf`, `Modules`, `EtaleSite`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme` (the overlap is their scheme fibre product).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallStructureSheaf`, `smallModuleRestriction`, `smallModuleEquivalence`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules` with its canonical abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; its cohomology is `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  etale-slice sheafification instances, using `SheafOfModules.IsQuasicoherent`.
- `Mathlib.CategoryTheory.Triangulated.Functor`: `Functor.IsTriangulated`,
  with `Pretriangulated` and `IsTriangulated` for the ambient structure.
- The already landed `def-sfb-space-derived-module-calculus` is added to
  `stmt_deps`: its module `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`
  supplies `DerivedModules`, `derivedQCohProperty`, `DerivedQCoh`.
- The already landed `def-sfb-space-qcoh-derived-triangulation` is added to
  `stmt_deps`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceQCohTriangulated` supplies
  `derivedQCohProperty_isTriangulated`, `qcohDerivedTriangulation`. Reusing these
  avoids duplicating the derived category or choosing a different triangulation.
- `Mathlib.CategoryTheory.Shift.Adjunction`: `Adjunction.rightAdjointCommShift`.
  `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.homEquiv`, its inverse
  counit formula, and its naturality in both variables.
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  its role is the explicit universe parameters and localization binder above.

All available proof-dependency modules are imported with plain imports:
`RingedSiteGrothendieckAbelian`, `GrothendieckDerivedCoproductsColimit`,
`SpacePerfectLocalizingGeneration`, `AlgebraicSpaceCompactPerfectGenerator`,
`CompactlyGenerated`, `BrownRepresentabilityRightAdjoint`, and Mathlib's
`Triangulated.Adjunction` and `Adjunction.FullyFaithful`. The small ringed model
is already a public transitive statement import. The two proof-only nodes
`lem-a1-space-finite-affine-subatlas` and
`lem-sfb-etale-affine-pairs-test-quasiseparated` have no recorded Lean modules
in the read repository, so there is no module to import for them. They are
explicitly retained in the proof docstring and no mathematical dependency or
proof step was removed. They are not needed to type the statement, since the
atlas and etale overlap conditions are rendered directly.

Edge cases checked before writing and again against the finished signature:

- Empty space: a quasi-compact empty scheme is permitted as the atlas; empty
  overlaps have a representing empty scheme. Neither atlas nonemptiness nor
  a nonempty point space is required. The zero derived category has the asserted
  adjunction and invertible unit.
- Affine schemes considered as spaces satisfy the stated atlas/overlap tests;
  the predicate still describes arbitrary algebraic spaces, including
  nonseparated qcqs examples. A base that is not quasi-separated is allowed.
- A zero complex and zero Hom groups cause no exceptional case. The Hom map has
  the same formula for zero, identity, and arbitrary maps.
- All integer shifts and unbounded cohomology degrees are retained. No finite
  cohomological dimension, torsion restriction, or coefficient lift is added.
- Choosing a different scheme representing an overlap changes no condition:
  Yoneda full faithfulness identifies the schemes and transports compactness.
- The independent localization universe is retained. Canonical full-subcategory
  triangulation and shifts are used throughout, not existential replacements.

Searches actually run:

1. `msearch.py ... leanfinder`: "The inclusion of the unbounded derived category
   with quasi coherent cohomology on a quasi compact quasi separated algebraic
   space has a triangulated right adjoint". Eight results, including
   `DerivedCategory.Q`, `Qh`, `HasDerivedCategory.standard`, generic derived
   adjunctions and localization lifting instances. None gives this space theorem.
2. `msearch.py ... loogle '"coherator"'`: zero hits.
3. `msearch.py ... grep 'coherator|DQCoh|derivedQCoh'`: zero Mathlib hits.
4. `msearch.py ... leansearch`: "Right adjoint to inclusion of objects with quasi
   coherent cohomology in the derived category of an algebraic space". Eight
   results about sheaf inclusion, localization fractions, and global sections;
   none is the requested theorem.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `coherator|Coherator|coreflector` and for derived quasi-coherent definitions.
   The upstream `WeilConjectures.AlgebraicGeometry.DQCoheratorAdjunction` has
   `AlgebraicGeometry.exists_dqCoheratorAdjunction` for qcqs schemes and the
   Zariski `schemeDerivedCategory`; its full signature/docstring were read.
   It is not the algebraic-space etale category or the full stated result here.
   The project contains the already reused definitions and no space coherator.
6. `grep -rn 'lem-sfb-space-derived-coherator-adjunction'
   lean/WeilConjectures`: no attachment. `rg` of `dag/lean_names_upstream.json`
   for coherator existence names: no matching exact space declaration.

No STATEMENT-DISPUTED flag or node fault remains. Only `lean` and the addition
of the two existing landed definition nodes to `stmt_deps` change in the item.

Validation: the delivered module was compiled by the prescribed `scompile.py`
against the server's live published build, in both sandbox and library modes,
with no errors or unexpected warnings (34.8 s and 7.9 s respectively). Every
compiler probe used `module` and the same import visibility as the delivery.

## Second reading by Q39

Author's second reading, with the JSON statement and completed Lean module open;
the maintainer supplies the independent review under this direct-delivery brief.
The atlas existential includes exactly compactness, representable etaleness and
surjectivity. The affine-pair quantifier includes both etaleness premises, and its
representing scheme is isomorphic to the exact sheaf pullback. The full inclusion
and both categories are the landed ones; transported cohomology tests every
integer. The right-adjoint shift structure is tied to the same `adj` used by the
counit and unit, rather than independently chosen. The Hom map is in the requested
direction, and naturality follows from that same adjunction's inverse Hom
bijection. `IsIso adj.unit` concerns the whole natural transformation. No
Noetherianity, separation, finite type, finite dimension, boundedness, nonempty
atlas, or equality of universes was inserted. The source of the inherited
triangulation and derived categories was made explicit by adding the two existing
landed definition nodes to `stmt_deps`; no definition was copied or repaired.
No mismatch was found on this second reading and no statement correction was made.
