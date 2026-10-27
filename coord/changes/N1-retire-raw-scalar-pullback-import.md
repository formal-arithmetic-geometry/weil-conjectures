# AlgebraicGeometry.Etale.RawModuleScalarComparison.pullbackIso

## Reason

The assigned retirement row in coord/retire-items.tsv identifies the Sheaf path
RawModuleScalarPullbackComparison as the duplicate of the adopted upstream module.
P2 has already reconciled the canonical constructions and preserved the historical
forgetting aliases in RawModuleScalarDerivedPullbackIso. B4 and C2 subsequently added
three fully proved characterization lemmas to the old import path. Preserve those
lemmas by transferring them verbatim into the existing derived-comparison module,
then migrate the two current direct importers and withdraw the old path.

This completes the import-path retirement without discarding the explicit
Kan-extension/sheafification characterization. All source-library signatures,
attributes, bodies and public imports are untouched. No arbitrary data are chosen.

## Old

The assigned module's public import is:

```lean
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
```

It additionally declares the following three theorems, verbatim (including proofs):

```lean
/-- The scalar pullback comparison has the forgotten module unit as its adjoint.
Source: Stacks Project, Tags 03D3 and 03D7, the inverse-image adjunction.
Proof: the canonical comparison is the inverse image of the forgotten module
unit under the abelian adjunction Hom equivalence. Applying that equivalence
recovers the module unit by `Equiv.apply_symm_apply`.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
theorem pullback_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((forget Λ Y).obj F) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map (pullback Λ f F) =
      (forget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F) := by
  change (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
    ((moduleAbelianUpperStarComparison Λ f).app F) = _
  exact Equiv.apply_symm_apply _ _

/-- The unit equation uniquely determines the scalar pullback comparison.
Source: Stacks Project, Tags 03D3 and 03D7, the inverse-image adjunction.
Proof: apply the injective abelian adjunction Hom equivalence. Its value on
each map is the unit followed by the direct image of that map, so the asserted
unit equation and `pullback_unit` identify the two values.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
theorem eq_pullback_of_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (c : (upperStar AddCommGrpCat.{u + 1} f).obj ((forget Λ Y).obj F) ⟶
      (forget Λ X).obj ((upperStar (ModuleCat.{u + 1} Λ) f).obj F))
    (hc : (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((forget Λ Y).obj F) ≫ (lowerStar AddCommGrpCat.{u + 1} f).map c =
      (forget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F)) :
    c = pullback Λ f F := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _ |>.injective
  simpa only [Adjunction.homEquiv_unit, pullback_unit] using hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The Kan-extension and sheafification composite is the canonical scalar comparison.
Source: Stacks Project, Tags 03D3 and 03D7; Mathlib's canonical Kan-extension
and sheafification comparison unit factorizations.

Proof: form the inverse Kan-extension comparison, sheafify it, and follow it
by the sheafification coefficient comparison. Naturality of the abelian
sheafification unit and `sheafComposeNatTrans_fac` compute the composite with
that unit. Expand the module and abelian inverse-image units as composite
Kan-extension/sheafification units. The inverse Kan-extension unit factorization
then identifies the abelian adjoint of the composite with the forgotten module
unit. Injectivity of the abelian adjunction Hom equivalence identifies the
composite with `pullback`. No nonempty, finiteness or nonzero hypotheses occur.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
theorem kanSheafification_eq_pullback (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let G := (MorphismProperty.Over.pullback @Etale ⊤ f).op
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (U.leftKanExtensionCompIsoOfPreserves F.obj G).inv ≫
      (sheafComposeNatTrans X.smallEtaleTopology U
        (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
          (G.lan.obj F.obj) = pullback Λ f F := by
  let G := (MorphismProperty.Over.pullback @Etale ⊤ f).op
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let c := (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (U.leftKanExtensionCompIsoOfPreserves F.obj G).inv ≫
    (sheafComposeNatTrans X.smallEtaleTopology U
      (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
        (G.lan.obj F.obj)
  have hm : ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom =
      ((G.lanAdjunction (ModuleCat.{u + 1} Λ)).comp
        (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).unit.app
          F.obj := by
    change (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F) = _
    dsimp only [upperStarLowerStarAdjunction,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp [G]
    rfl
  have ha : ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      ((sheafCompose Y.smallEtaleTopology U).obj F)).hom =
      ((G.lanAdjunction AddCommGrpCat.{u + 1}).comp
        (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).unit.app
          ((sheafCompose Y.smallEtaleTopology U).obj F).obj := by
    change (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((sheafCompose Y.smallEtaleTopology U).obj F)) = _
    dsimp only [upperStarLowerStarAdjunction,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp [G]
    rfl
  have hf : toSheafify X.smallEtaleTopology (G.lan.obj (F.obj ⋙ U)) ≫ c.hom =
      (U.leftKanExtensionCompIsoOfPreserves F.obj G).inv ≫
        Functor.whiskerRight (toSheafify X.smallEtaleTopology (G.lan.obj F.obj)) U := by
    change (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app
      (G.lan.obj (F.obj ⋙ U)) ≫
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (U.leftKanExtensionCompIsoOfPreserves F.obj G).inv ≫
          (sheafComposeNatTrans X.smallEtaleTopology U
            (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
            (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
              (G.lan.obj F.obj)) = _
    rw [Functor.map_comp, ← Category.assoc]
    erw [← (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.naturality]
    rw [Category.assoc]
    erw [sheafComposeNatTrans_fac]
    rfl
  change c = pullback Λ f F
  apply eq_pullback_of_unit Λ f F c
  apply (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map_injective
  change ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
    ((sheafCompose Y.smallEtaleTopology U).obj F)).hom ≫
      Functor.whiskerLeft G c.hom =
    Functor.whiskerRight
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom U
  rw [hm, ha]
  simp only [Adjunction.comp_unit_app]
  change (G.lanUnit.app (F.obj ⋙ U) ≫
    Functor.whiskerLeft G (toSheafify X.smallEtaleTopology (G.lan.obj (F.obj ⋙ U)))) ≫
      Functor.whiskerLeft G c.hom =
    Functor.whiskerRight (G.lanUnit.app F.obj ≫
      Functor.whiskerLeft G (toSheafify X.smallEtaleTopology (G.lan.obj F.obj))) U
  rw [Category.assoc, ← Functor.whiskerLeft_comp, hf, Functor.whiskerLeft_comp,
    ← Category.assoc]
  erw [Functor.leftKanExtensionCompIsoOfPreserves_inv_fac]
  ext W
  simp
  rfl

```

The two direct consumers OrdinaryFiniteP1Kummer and CartierRelativeBoundaryRealization
both have the following import:

```lean
public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison
```

The receiving module RawModuleScalarDerivedPullbackIso ends after
`derivedPullbackIsoImpl_eq_formula`; its existing public imports, private import,
private helper, definitions and instances are preserved verbatim.

## New

Withdraw lean/Sheaf/AlgebraicGeometry/RawModuleScalarPullbackComparison.lean via
deleted.txt. The delivery tool installs the standard empty module at this path.

Insert the exact three declarations quoted above, including their docstrings,
attributes and proof bodies, before the final namespace end in
RawModuleScalarDerivedPullbackIso. Their full names, signatures and visibility
are identical, and the existing definitions and instances in that module are
unchanged. No new module or new mathematical statement is introduced.

In both direct consumers replace only the quoted import with:

```lean
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
```

The consumers therefore retain the entire former public environment: the old path
publicly imported this same receiving module, and its only own declarations have
been transferred there. Consumer declarations and proofs are unchanged byte for byte.

The canonical node keeps its upstream Lean attachment, mathematical statement,
statement dependencies and proof dependencies. Its proof text and Lean note now
locate the retained characterization lemmas in the receiving module. All DAG parents
continue to refer to the same canonical upstream construction; no parent dependency
or blueprint unit step is removed. The unit sk-lem-failure-field has no realized
attachment to this compatibility path. A scan of both lean/ and quarantine/ finds
exactly the two current direct importers and no archived importer of the Sheaf path.

## Users

`tools/downstream.py --direct --uses pullback_unit eq_pullback_of_unit
kanSheafification_eq_pullback` identifies the two direct consumers below and no
external textual use of these characterization lemmas. A separate import scan of
lean/ and quarantine/ agrees. The retirement inventory's nine consumers describe
an older source state: the other seven listed modules have already migrated to
upstream, as their current source imports show. Both direct consumer import closures retain exactly the same modules except
for the retired path (1253 to 1252 and 12963 to 12962 modules respectively);
they see the same declarations through the migrated public imports.
No target statement or the meaning of any definition changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison | N1, assigned | Withdraw duplicate import path after preserving all its declarations. |
| Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso | unclaimed in current local claim records | Receive the three existing proved theorems verbatim; all existing code retained. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | unclaimed in current local claim records | Replace only the public import by the receiving module. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed in current local claim records | Replace only the public import by the receiving module; keep its existing hole. |

The compiler checks the receiving module and both adapted consumers in import order.
The final delivery additionally checks axioms and preflight. No source-root module
is changed, and no adaptation to a mathematical interface is required.

## Status

landed 20261025T030524-L-2856984 2026-10-25 (merge of deliver/N1/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison)
