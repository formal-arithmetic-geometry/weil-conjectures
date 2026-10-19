## Worker report

This delivery records existing declarations; no Lean module is added. The main declaration is
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap` in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`, lines 119–123.
The same module supplies the canonical mate and its transpose formula, both included in
`lean.declarations`. The recorded signature is verbatim from the source; its section parameters
are the coefficient category A, four schemes, four arrows, and the two open-immersion instances.

Clause-by-clause correspondence:

- The four schemes are `U' U Z' Z : Scheme.{u}` and the four arrows are
  `g' : U' ⟶ U`, `j' : U' ⟶ Z'`, `j : U ⟶ Z`, `g'' : Z' ⟶ Z`.
  Thus upstream `Z'`, `Z`, `g'`, `g''` mean the node's `X'`, `X`, `gU`, `g`.
- Open immersions are `[IsOpenImmersion j] [IsOpenImmersion j']`. Cartesianness is
  `hsq : IsPullback g' j' j g''`, with no condition on `g''`. For the recorded dependency
  `sq : AlgebraicGeometry.OpenImmersionSquare gU j' j g`, use its two open-immersion fields
  as instances and `IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd`.
  A chosen pullback identification supplies exactly this universal property, without extra
  geometric restrictions or a dependence of the result on the choice.
- Abelian sheaves are the specialization `A := AddCommGrpCat.{u+1}`. The theorem says the
  canonical natural transformation is invertible, hence each component at every
  `F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u+1}` is invertible.
- The source defines `α := openImmersionLowerShriekBaseChangeMap A hsq.toCommSq` in the
  opposite direction `j'_! gU^* ⟶ g^* j_!`. The node's map is precisely
  `(asIso α).inv.app F`, with the `IsIso α` instance supplied by the recorded theorem.
  Its domain is `g^* (j_! F)` and its codomain is `j'_! (gU^* F)`.
- The mate characterization is the existing
  `Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app A hsq.toCommSq F`:
  `unit_j'.app (gU^*.obj F) ≫ j'^*.map (α.app F)` equals
  `gU^*.map (unit_j.app F) ≫ (squareUpperStarIso A hsq.toCommSq.flip).hom.app (j_!.obj F)`.
  By the adjunction hom-equivalence this states exactly that α is the mate of the node's
  composite. Inverting α gives the requested map, not an arbitrary isomorphism.
- For a finite commutative ring take `Λ : Type (u+1)`, `[CommRing Λ] [Finite Λ]`,
  `A := ModuleCat.{u+1} Λ`. These coefficient categories satisfy the general theorem's
  category, Abelian, Grothendieck and sheafification assumptions. No property of Λ beyond
  being a commutative ring is needed by that theorem, so in particular every finite Λ is
  covered. For `K : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u+1} Λ)) ℤ`,
  apply the theorem to `K.X n` for every integer n. More explicitly,
  `(asIso α).symm.mapHomologicalComplex (ComplexShape.up ℤ)` is the natural isomorphism
  on complexes: Mathlib's definition gives its degree-n component as `(asIso α).inv.app
  (K.X n)`. Natural transformations commute with the differentials by construction.
  No boundedness or derived replacement is imposed. Small coefficient rings can be lifted
  to this universe; the coefficient universe is the site's usual u+1 convention.

Dependency declarations read:

- `def-weil-pbc-extension-by-zero`: `Etale.openImmersionLowerShriek`, in upstream
  `...LowerShriek.OpenImmersion.Defs`, together with its actual stalk declarations in
  `...OpenImmersion.FiniteComparison` (the dependency's extra-declaration module metadata
  is stale, but its primary declaration and interface are usable).
- `def-cbc-open-immersion-square`: `AlgebraicGeometry.OpenImmersionSquare`,
  `Sheaf.AlgebraicGeometry.OpenImmersionSquare`; its parent is
  `AlgebraicGeometry.ChosenCartesianSquare` in the corresponding Sheaf module.
- `lem-weil-pbc-extension-by-zero-adjunction`:
  `Etale.openImmersionLowerShriekUpperStarAdjunction` and
  `Etale.openImmersionLowerShriekAdjunction`, upstream `...OpenImmersion.Defs`.
  The canonical map uses exactly the former adjunction.
- `lemma-weil-pbc-geometric-stalk-conservative`:
  `Scheme.isIso_of_isIso_sheafFiber_map`, upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `lem-kun-stalk-as-pullback`: `Scheme.geometricStalk_as_pullback`,
  `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`.
- `lem-cbc-base-change-mate-stalk`:
  `Etale.openImmersionLowerShriekBaseChangeMate_stalk`,
  `Sheaf.AlgebraicGeometry.BaseChangeMateStalk`. This already uses the same upstream
  canonical mate, its proved invertibility, and its inverse; it confirms the orientation.

The last three dependencies give the node's stalk-based proof route. Since the theorem is
already available, no new proof or dependency imports are required. No missing notion,
statement correction, new node, or dependency module is needed.

Edge cases checked: j or j' the identity, empty U (so both extensions are zero), empty X'
(the empty base change), F the zero sheaf, zero complexes, unbounded complexes, degree zero
and negative degrees, and the zero coefficient ring. No nonemptiness, nonzero ring,
separatedness, finiteness condition on g, or boundedness assumption occurs upstream.
A general natural isomorphism gives each component and each complex degree, including these
cases. The theorem's sheafification assumptions are standard instances for the specified
coefficient categories, not extra geometric hypotheses.

Searches made:

- `msearch.py ... leanfinder "extension by zero commutes with arbitrary base change open
  immersion etale sheaves"`: 8 hits, including Scheme.Modules.restrict and Kähler
  differentials; no Mathlib small-etale extension-by-zero match.
- `msearch.py ... loogle "NatTrans.mapHomologicalComplex, Functor.mapHomologicalComplex"`:
  no hits; service reported unknown identifier NatTrans.mapHomologicalComplex.
- `msearch.py ... grep "extension.by.zero|LowerShriekBaseChange" CategoryTheory`:
  zero Mathlib hits.
- Direct rg on upstream OpenImmersion modules for BaseChange/baseChange found the exact
  general Cartesian-square map, invertibility lemma and transpose formula in
  BaseChangeSquare.lean. Read all three signatures and docstrings and their section context.
- Direct rg for the item id throughout upstream WeilConjectures: zero hits. Direct rg on
  project lean/Sheaf found BaseChangeMateStalk using exactly these existing declarations;
  the module-sheaf lower-shriek base-change siblings concern a different API.
- Direct rg on Mathlib Algebra/Homology/Additive.lean found and was followed by reading
  NatTrans.mapHomologicalComplex and NatIso.mapHomologicalComplex; their definitions give
  exactly the degreewise extension and its inverse.
- Direct rg on dag/lean_names_upstream.json for openImmersionLowerShriekBaseChangeMap:
  zero hits; the source text is newer and establishes the match.

Validation: a scratch-only server probe checks the abelian and ModuleCat specializations,
its inverse natural isomorphism on complexes, and the conversion of the recorded chosen
Cartesian square. Delivery preflight additionally checks all three existing declarations
on the server. No local compiler or global build is used.

## Second reading by ND

I read the node statement, its blueprint source place, and the recorded declarations
independently. The objects and hypotheses match as follows. The schemes and arrows are
`U' U Z' Z : Scheme.{u}` with `g' : U' ⟶ U`, `j' : U' ⟶ Z'`, `j : U ⟶ Z`, and
`g'' : Z' ⟶ Z`; these render the node's `U' \xrightarrow{g_U} U` and
`X' \xrightarrow{g} X` square after the stated renaming. The hypotheses
`[IsOpenImmersion j] [IsOpenImmersion j']` and `hsq : IsPullback g' j' j g''`
are exactly the two open-immersion hypotheses and cartesian-square hypothesis. No
properness, finiteness, separatedness, nonemptiness, or characteristic assumption is
introduced.

The first conclusion clause, that the canonical base-change map is an isomorphism, is
rendered by `Etale.openImmersionLowerShriekBaseChangeMap` together with
`Etale.isIso_openImmersionLowerShriekBaseChangeMap`; the node's displayed direction
`g^{-1} j_! F ⟶ j'_! g_U^{-1} F` is the inverse of the recorded map
`j'_! g'^* ⟶ g''^* j_!`, as stated in the worker report and confirmed by the source
docstring. The second clause, the mate characterization, is rendered by
`Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app`, whose two sides are exactly
the unit of `j_! ⊣ j^{-1}`, inverse image along `g_U`, and the cartesian square
identification. Thus the map is canonical and not an arbitrary isomorphism. The final
finite-commutative-ring clause is obtained by specializing the same theorem to
`A := ModuleCat.{u+1} Λ` and applying `NatIso.mapHomologicalComplex`; its degree-n
component is the preceding isomorphism at `K.X n`, and naturality preserves the
differentials. The quantifier order (ring, module sheaf complex, then degree) is
preserved, and no boundedness condition is added.

I checked the empty open, identity open immersion, empty scheme, zero sheaf, zero ring,
zero complex, degree zero, negative degrees, and unbounded complexes. In every case the
existing natural-isomorphism statement remains applicable; no hidden `Nonempty` or
nonzero assumption occurs. I searched Mathlib, the project `lean/Sheaf`, and the upstream
`WeilConjectures` tree using LeanFinder/Loogle/grep queries for extension-by-zero
base-change and found no competing declaration. The upstream BaseChangeSquare source was
read directly, including the theorem, its map definition, and its mate formula. No
mismatch was found, so no statement, dependency, or module change was required.
