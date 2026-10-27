## Worker report

Existing declaration, with no new module:
`AlgebraicGeometry.ProEtale.StrictTower.openBetaRestriction_normalized` in
`lean/Sheaf/AlgebraicGeometry/TowerOpenBetaNormalization.lean`, lines 119–134.
The file and all four preceding helper declarations were read locally and checked
against the current live server source with `scompile.py --source
Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization`.
Only the item's `lean` field changes. The TeX statement and accepted proof split stay intact.
The existing theorem has proof `sorry`; this delivery supplies no proof.

The existing theorem states that the specified compositor-square mate is an
isomorphism and has exactly the section action defining t. This is the same
assertion as identifying the section-identity isomorphism t with that mate:
its first conjunct provides the natural isomorphism, and its second fixes its
underlying map on every common section. Conversely, the node's t=mate equation
and section specification give precisely these two conjuncts. This is not a
restriction to towers, derived objects, finite rings or a literal pullback.

Hypothesis and clause matching:

- Commutative ring B: the module's explicit `variable (B : Type (u + 1)) [CommRing B]`.
  The theorem and its four helpers have no `[Finite B]` or other coefficient hypothesis.
- Schemes U', U, X', X and maps gU, j', j, g: the four `Scheme.{u}` binders and
  `(a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)`; `a` denotes gU.
- Small pro-etale sites, constant rings and module sheaves: the imported
  `StrictConstantTowerOperations.coefficients`, `Modules`, `modulePullback` and
  `moduleDirectImage` are precisely the declarations in the item's recorded
  dependency. `coefficients B T` is `constantSheaf (Scheme.ProEt.topology T)
  CommRingCat` at `CommRingCat.of B`; `Modules B T` is
  `Scheme.proEtaleRingModules T (coefficients B T)` and hence the actual
  `SheafOfModules` category, not a newly defined module category.
  The site has object universe u+1, morphism universe u; coefficients and modules
  are in u+1. No equality of the site object and morphism universes is imposed.
- Open-immersion square: `[IsOpenImmersion j] [IsOpenImmersion j']`,
  `w : a ≫ j = j' ≫ g`, and `sq : IsPullback a j' j g` unpack the
  recorded `OpenImmersionSquare`. Its `isoPullback`, `hom_fst`, `hom_snd`
  give this IsPullback by `IsPullback.of_iso_pullback`. Conversely a Cartesian
  square supplies the unique projection-compatible isomorphism. No use is made
  of a noncanonical identification or of an extra assumption on g.
- The ordinary module operations: `openBetaModuleAdj B f` is definitionally
  `Scheme.proEtaleRingModuleAdjunction f (coefficients B Y) (coefficients B X)
  (constantRingIso B f)`, the normalized ordinary identified-coefficient adjunction.
  `moduleDirectImage` is the actual sectionwise pushforward: on W its module
  is evaluated at `(Scheme.proEtaleBaseChange f).obj W`, the fibre product over
  the target. The scalar action is the adjoint canonical constant-section action.
- Specified c and its orientation: `openBetaRestriction` is defined by
  `mateEquiv (openBetaModuleAdj B g) (openBetaModuleAdj B a)` at
  `(TwoSquare.mk _ _ _ _ (moduleSquareG B a j' j g w).inv)`.
  The read equality `moduleSquareG_eq` in `FiniteOpenBaseChangeNormalized.lean`
  identifies `moduleSquareG` with
  `(moduleGComp B j' g).symm ≪≫ eqToIso (congrArg (modulePullback B) w.symm)
  ≪≫ moduleGComp B a j`.
  Its inverse therefore goes from `modulePullback B j ⋙ modulePullback B a`
  through the equality w to `modulePullback B g ⋙ modulePullback B j'`.
  This is exactly c, with the direct-image/conjugation compositor convention of
  `def-cbc-strict-constant-tower-operations`; the mate uses c, not its inverse.
- Natural isomorphism t: `IsIso (openBetaRestriction B a j' j g w)` gives it by
  `asIso` of this exact natural transformation. Its source is
  `moduleDirectImage B g ⋙ modulePullback B j` and target is
  `modulePullback B j' ⋙ moduleDirectImage B a`.
- Identity on common sections: the second conjunct quantifies over all
  `M : Modules B X'`, all `V : U.ProEt`, and every section x over
  `V ×[X] X'`. `openBetaSection B j` is the canonical open-slice coprojection,
  defined by the module unit followed by restriction along the site unit.
  The equality sends this section to `openBetaSection B j'` of
  `M.val.map (openBetaSectionObjectMap a j' j g w V).op x`.
  The object map is the explicit pullback lift with projections identity on V
  and j' on U'. Cartesianity makes it the unique isomorphism
  `V ×[U] U' ≅ V ×[X] X'` required by the node. In open-slice coordinates
  the displayed equation is exactly identity on the common section module.
  Naturality and all restriction maps are part of the natural transformation,
  the module maps and the site-object functor, rather than extra unspecified maps.
- Exchange-mate formula: expand the read Mathlib `CategoryTheory.mateEquiv`.
  In Lean's diagrammatic order its component is η_gU followed by
  `(gU)_*.map (c.hom.app (g_*.obj M))` followed by
  `(gU)_*.map (j'⁻¹.map (ε_g.app M))`. Reversing to the node's usual composition
  notation gives exactly its displayed formula. The equality to the mate is fixed
  by the definition of `openBetaRestriction`, not assumed of an arbitrary map.

Dependency declarations read and used in this match:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (transparent abbreviation of `SheafOfModules`).
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: its reexported
  arbitrary-ring `Scheme.proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`
  and `proEtaleRingModuleAdjunction`; the last is defined in
  `ProEtaleOperationsCanonicalAdjunction` by its unique tensor-unit normalization.
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: `coefficients`, `Modules`,
  `constantRingIso`, `modulePullback`, `moduleDirectImage`, `moduleRComp`, `moduleGComp`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`, `pullback.map`.
- `Sheaf.AlgebraicGeometry.OpenImmersionSquare`: `AlgebraicGeometry.OpenImmersionSquare`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`.
- Proof interfaces were also read: `Scheme.ProEtaleOpenRestriction.proEtaleOpenRestrictionCounit`
  in `Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit`, including its Sectionwise,
  AlphaNormalization and CounitEquation predicates; and
  `CategoryTheory.constant_left_module_inverse_image` in
  `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.

Edge cases checked semantically against the signatures and concrete maps: B the zero
ring, B infinite, g the identity, j the identity, U empty, and empty schemes.
All allow the same adjunctions and pullback lifts. No nonemptiness, properness,
quasi-compactness, finiteness or Noetherian hypothesis occurs. The chosen Cartesian
representative is arbitrary; only its projections are used. There is no degree or
boundedness restriction because this is an ordinary module-sheaf statement.

Searches actually run using the prescribed `msearch.py` wrapper:

- leanfinder: "For module sheaves on small proetale sites the open restriction section
  identity is the adjunction mate of the inverse image compositor square".
  Eight results: Zariski scheme module restriction/unit/counit/compositor declarations,
  including `Scheme.Modules.restrictAdjunction_counit_app_app`; no exact pro-etale match.
- loogle: "CategoryTheory.mateEquiv, SheafOfModules.pushforward". Zero hits.
- grep: "mateEquiv|restrictAdjunction", CategoryTheory. Twenty results, chiefly the
  generic mates APIs in `Adjunction/Mates.lean`; no section-normalized pro-etale theorem.
- leansearch: "Open restriction of a proetale module direct image is the mate of the
  inverse image composition square". Eight results, all generic/Zariski restriction
  constructions and properties; no exact match.
- `rg` on `lean/WeilConjectures` for the item id: no hits. Broader `rg` searches for
  open restriction, sections, `sectionArrow`, `objectCoprojection`, `moduleSquareG`
  and mate names in `lean/WeilConjectures` and `lean/Sheaf` found the exact existing
  helper in `TowerOpenBetaNormalization.lean`. Its whole signature and the helper
  bodies were read. `ModuleDirectImageOpenPasting` is for condensed internal modules,
  and `ProEtaleOpenRestrictionCounit` uses inverse-image coefficient rings and a
  literal pullback; neither was mistaken for the constant-coefficient exact match.

Source read: `literature/stacks-project/sites-modules.tex`, Tag 04J0,
`lemma-localize-morphism-ringed-sites`, lines 2369–2408. It states the localized
ringed-topos square and the restriction/direct-image equality; the mate calculation
is the explicit adjunction calculation already in the item's accepted proof.
No statement fault or disputed statement was found.

Proof ownership: the existing helper is in the consumer module
`TowerOpenBetaNormalization`, whose main node cites this item. This attachment does
not add that consumer as a dependency and does not cite its theorem as a proof of
itself. It assigns this already-stated helper to this item. Its existing docstring
mentions this item; stage 3 should prove the helper from this item's three-step
proof (the general counit theorem, coefficient transport, then transposition).
No self-import should be added to the owning module. The present delivery changes
neither the module nor the DAG's acyclic dependency edges.

## Second reading by O4

This is a second in-thread reading; the dispatcher explicitly prohibited starting
other agents. The maintainer supplies the independent review of this delivery.
I reopened the node, the existing theorem, its four concrete helper definitions and
`moduleSquareG_eq`. The comparison of hypotheses found the same unrestricted B and
arbitrary g, and the open/Cartesian data unpack the recorded open-square structure.
The comparison of conclusions found both necessary parts: `IsIso` constructs the
natural isomorphism, and the all-sections equation fixes it independently of its
mate description. The `.inv` on `moduleSquareG` is essential: that square goes
from the g,j' path to the j,gU path, so its inverse is exactly the node's c.
Expanding `mateEquiv` gave the displayed unit–c–counit formula with the stated order.
The section map uses identity on V and j' on U', so there is no arbitrary
coefficient or fibre-product automorphism. No hypothesis/clause mismatch remains.
The delivery records the existing declaration and contains no replacement Lean module.

Validation: a module-mode probe imported the existing module and checked the full types
of `openBetaRestriction_normalized`, `openBetaRestriction`, and `moduleSquareG_eq`.
`scompile.py O4 lem-cbc-open-square-section-restriction-mate` compiled that probe cleanly
both in its sandbox and under its module name (1.8 s and 1.7 s). The probe was removed;
there are no delivered Lean files because the record has `existing: true`.
