# SheafOfModules.CanonicalRingedTensorComparison

## Reason

The existence obligation needs an independent module, while its type was defined in the
item that must import that obligation. Relocate the unchanged structure to the data
module and publicly reexport it from the original module, breaking that import cycle.
This is a dependency separation for the strict construction/uniqueness reduction.
No field, parameter, universe, visibility, constructor, projection or definition value
changes. No target meaning changes. The existing unit and derived theorem signatures
and proof holes remain unchanged.

Also remove the unused public imports RingedTopoiDerivedTensorPullback and
ModulePullbackTensorIso, replacing their needed public foundational imports directly.
A repository-wide search found no uses of either removed theorem outside its own module.
The data import supplies the same coefficient-universe sheafification instances.

## Old

Location: lean/Sheaf/Paper/RingedTopoiCanonicalTensorPullback.lean

```lean
structure CanonicalRingedTensorComparison where
  /-- Scalar-extension insertion, as a map of underlying sheaves of sets. -/
  q : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI) ⋙ sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (L.obj M))
  /-- Insertion is specifically m mapped to 1 tensor m. -/
  q_one : ∀ (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W),
    (q M).hom.app W m = (eqToHom (hobj M).symm).val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
        (changeOfRingsPresheaf.{u, u, u} c (I.modules.obj M))).app W
          ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m))
  /-- Tensor preservation with the orientation of 07A4. -/
  mu : ∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N)
  /-- Naturality in both variables. -/
  naturality : ∀ {M M' N N' : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
    L.map ((monoidalCategory R).tensorHom f g) ≫ (mu M' N').hom =
      (mu M N).hom ≫ (monoidalCategory S).tensorHom (L.map f) (L.map g)
  /-- Canonical generalized pure-tensor formula, rather than an arbitrary tensor iso. -/
  pure : ∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (Z : Sheaf JC (Type u))
    (x : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj N))
    (z : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((monoidalCategory R).tensorObj M N))),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
      (tensorObjIsoSheafification M N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app W (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
    ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
      (uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        q ((monoidalCategory R).tensorObj M N) ≫
          (toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
            (CategoryTheory.forget AddCommGrpCat.{u})).map (mu M N).hom).hom.app W t =
      (tensorObjIsoSheafification (L.obj M) (L.obj N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
          ((L.obj M).val ⊗ (L.obj N).val)).app W
            ((uInv.map x ≫ I.moduleUnderlying.inv.app M ≫ q M).hom.app W t
              ⊗ₜ[S.obj.obj W]
              (uInv.map y ≫ I.moduleUnderlying.inv.app N ≫ q N).hom.app W t))
```

## New

Location: lean/Sheaf/Paper/RingedTopoiTensorComparisonData.lean, publicly imported by
the original module. The declaration is verbatim identical:

```lean
structure CanonicalRingedTensorComparison where
  /-- Scalar-extension insertion, as a map of underlying sheaves of sets. -/
  q : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI) ⋙ sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (L.obj M))
  /-- Insertion is specifically m mapped to 1 tensor m. -/
  q_one : ∀ (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W),
    (q M).hom.app W m = (eqToHom (hobj M).symm).val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
        (changeOfRingsPresheaf.{u, u, u} c (I.modules.obj M))).app W
          ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m))
  /-- Tensor preservation with the orientation of 07A4. -/
  mu : ∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N)
  /-- Naturality in both variables. -/
  naturality : ∀ {M M' N N' : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
    L.map ((monoidalCategory R).tensorHom f g) ≫ (mu M' N').hom =
      (mu M N).hom ≫ (monoidalCategory S).tensorHom (L.map f) (L.map g)
  /-- Canonical generalized pure-tensor formula, rather than an arbitrary tensor iso. -/
  pure : ∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (Z : Sheaf JC (Type u))
    (x : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj N))
    (z : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((monoidalCategory R).tensorObj M N))),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
      (tensorObjIsoSheafification M N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app W (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
    ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
      (uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        q ((monoidalCategory R).tensorObj M N) ≫
          (toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
            (CategoryTheory.forget AddCommGrpCat.{u})).map (mu M N).hom).hom.app W t =
      (tensorObjIsoSheafification (L.obj M) (L.obj N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
          ((L.obj M).val ⊗ (L.obj N).val)).app W
            ((uInv.map x ≫ I.moduleUnderlying.inv.app M ≫ q M).hom.app W t
              ⊗ₜ[S.obj.obj W]
              (uInv.map y ≫ I.moduleUnderlying.inv.app N ≫ q N).hom.app W t))
```

## Users

`tools/downstream.py` found 181 downstream modules; its declaration-use filter found
exactly the following six. All retain access through the original public module.
No existing module outside the item is edited or requires adaptation.
The separate proof-class API change record likewise preserves its exact proposition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionFormulaArrows | unclaimed | identical public declaration through reexport |
| Sheaf.Paper.ProjectionFormulaFiniteFree | unclaimed | identical public declaration through reexport |
| Sheaf.Paper.ProjectionFormulaProjectiveSummand | unclaimed | identical public declaration through reexport |
| Sheaf.Paper.ProjectionFormulaTotalization | unclaimed | identical public declaration through reexport |
| Sheaf.Paper.RingedTensorSquarePresentation | unclaimed | identical public declaration through reexport |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullback | A4 | identical public declaration through reexport |

## Status

landed 20261016T011142-L-263526 2026-10-16 (merge of deliver/A4/Sheaf.Paper.RingedTopoiCanonicalTensorPullback)
