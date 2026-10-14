# perfectOverlapStageStatement, perfectOverlapCoherenceStatement, perfectOverlapCoreStatement

## Reason

Repair H10's fresh artifact-generation timeout. Native sampling located the repeated
work in Lean.Meta.FunInfo.collectDeps_visit (50.93% of sampled CPU cycles, with a
further 9.53% in its free-variable lookup). This traversal has no expression cache;
expanding the nested dependent lets repeats large comparison and instance terms.
A stage-only profile spent 24.5 seconds in .olean serialization. The returned complete
module exceeded the unchanged 60-second limit in a fresh artifact build.

Name each complete proposition with a transparent, fully constructed definition.
Keep every original binder, quantifier, local definition and equation: each definition's
body is the formerly inline result verbatim. The theorems have the same outer binders
and state these propositions. Their proofs unfold only the named propositions; the
core still applies stage and coherence with the same witnesses and induced equation.
This does not move or split a sorry, change a mathematical statement, choose data,
or weaken a target. These are statement representations of the three existing DAG
nodes, recorded as additional lean.declarations on those nodes, not new notions.

The definitions retain default transparency, so the unchanged direct importer can
use core exactly as before. Three independent original-signature examples check the
received theorem types against the delivered declarations by unfolding the definition.
No existing geometric definition or Challenge declaration changes, and no forced
adaptation is made. The users below are the full 425-module downstream list plus the
own module already inventoried for this delivery; their mathematical statements hold
because the result propositions are definitionally identical. The sole direct importer
is compiled unchanged against fresh delivered artifacts; see report.md for the results.

## Old

```lean
theorem perfect_overlap_transition_comparison_core_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
      let LU := (Equivalence.inverse
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over P))
        (D := SheafOfModules.{u} (moduleRings P.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv P)).mapDerivedCategory
      let LV := (Equivalence.inverse
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Q))
        (D := SheafOfModules.{u} (moduleRings Q.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv Q)).mapDerivedCategory
      ∃ (d : SchemeTwoOpenComparisonDiagram X Yk g U' V' P Q)
        (κU : derivedPullback (f ∣_ U) ⋙ d.toDiagram.HU ≅
          derivedPullback (gj ∣_ U) ⋙ LU)
        (κV : derivedPullback (f ∣_ V) ⋙ d.toDiagram.HV ≅
          derivedPullback (gj ∣_ V) ⋙ LV)
        (siteU : PU ⋙ LU ≅ RU) (siteV : PV ⋙ LV ≅ RV)
        (e : SU.obj A' ≅ SV.obj B')
        (θU : d.toDiagram.HU.obj A' ≅ RU.obj E)
        (θV : d.toDiagram.HV.obj B' ≅ RV.obj E),
        θU = κU.app A ≪≫ LU.mapIso φU ≪≫ siteU.app E ∧
        θV = κV.app B ≪≫ LV.mapIso φV ≪≫ siteV.app E ∧
        (d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E) =
          d.toDiagram.HW.mapIso e ≪≫
            (d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E)
```

```lean
theorem perfect_overlap_transition_comparison_core_coherence
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∀ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
      ∀ (d : SchemeTwoOpenComparisonDiagram X Yk g U' V' P Q)
        (e₀ : SU.obj A' ≅ SV.obj B')
        (θU : d.toDiagram.HU.obj A' ≅ RU.obj E)
        (θV : d.toDiagram.HV.obj B' ≅ RV.obj E),
        (d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E) =
          d.toDiagram.HW.mapIso e₀ ≪≫
            (d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E) →
        d.toDiagram.γU.inv.app A' ≫ SP.map θU.hom ≫ τU.hom.app E =
          d.toDiagram.HW.map e₀.hom ≫ d.toDiagram.γV.inv.app B' ≫
            SQ.map θV.hom ≫ τV.hom.app E
```

```lean
theorem perfect_overlap_transition_comparison_core
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
      ∃ (d : SchemeTwoOpenComparisonDiagram X Yk g U' V' P Q)
        (e : SU.obj A' ≅ SV.obj B')
        (θU : d.toDiagram.HU.obj A' ≅ RU.obj E)
        (θV : d.toDiagram.HV.obj B' ≅ RV.obj E),
        d.toDiagram.γU.inv.app A' ≫ SP.map θU.hom ≫ τU.hom.app E =
          d.toDiagram.HW.map e.hom ≫ d.toDiagram.γV.inv.app B' ≫
            SQ.map θV.hom ≫ τV.hom.app E
```

## New

```lean
noncomputable def perfectOverlapStageStatement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : Prop :=
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
      let LU := (Equivalence.inverse
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over P))
        (D := SheafOfModules.{u} (moduleRings P.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv P)).mapDerivedCategory
      let LV := (Equivalence.inverse
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Q))
        (D := SheafOfModules.{u} (moduleRings Q.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv Q)).mapDerivedCategory
      ∃ (d : SchemeTwoOpenComparisonDiagram X Yk g U' V' P Q)
        (κU : derivedPullback (f ∣_ U) ⋙ d.toDiagram.HU ≅
          derivedPullback (gj ∣_ U) ⋙ LU)
        (κV : derivedPullback (f ∣_ V) ⋙ d.toDiagram.HV ≅
          derivedPullback (gj ∣_ V) ⋙ LV)
        (siteU : PU ⋙ LU ≅ RU) (siteV : PV ⋙ LV ≅ RV)
        (e : SU.obj A' ≅ SV.obj B')
        (θU : d.toDiagram.HU.obj A' ≅ RU.obj E)
        (θV : d.toDiagram.HV.obj B' ≅ RV.obj E),
        θU = κU.app A ≪≫ LU.mapIso φU ≪≫ siteU.app E ∧
        θV = κV.app B ≪≫ LV.mapIso φV ≪≫ siteV.app E ∧
        (d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E) =
          d.toDiagram.HW.mapIso e ≪≫
            (d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E)
```

```lean
theorem perfect_overlap_transition_comparison_core_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : perfectOverlapStageStatement R c hc i Z t j hij hstage
```

```lean
noncomputable def perfectOverlapCoherenceStatement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : Prop :=
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∀ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
      ∀ (d : SchemeTwoOpenComparisonDiagram X Yk g U' V' P Q)
        (e₀ : SU.obj A' ≅ SV.obj B')
        (θU : d.toDiagram.HU.obj A' ≅ RU.obj E)
        (θV : d.toDiagram.HV.obj B' ≅ RV.obj E),
        (d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E) =
          d.toDiagram.HW.mapIso e₀ ≪≫
            (d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E) →
        d.toDiagram.γU.inv.app A' ≫ SP.map θU.hom ≫ τU.hom.app E =
          d.toDiagram.HW.map e₀.hom ≫ d.toDiagram.γV.inv.app B' ≫
            SQ.map θV.hom ≫ τV.hom.app E
```

```lean
theorem perfect_overlap_transition_comparison_core_coherence
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : perfectOverlapCoherenceStatement R c hc i Z t j hij hstage
```

```lean
noncomputable def perfectOverlapCoreStatement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : Prop :=
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
      ∃ (d : SchemeTwoOpenComparisonDiagram X Yk g U' V' P Q)
        (e : SU.obj A' ≅ SV.obj B')
        (θU : d.toDiagram.HU.obj A' ≅ RU.obj E)
        (θV : d.toDiagram.HV.obj B' ≅ RV.obj E),
        d.toDiagram.γU.inv.app A' ≫ SP.map θU.hom ≫ τU.hom.app E =
          d.toDiagram.HW.map e.hom ≫ d.toDiagram.γV.inv.app B' ≫
            SQ.map θV.hom ≫ τV.hom.app E
```

```lean
theorem perfect_overlap_transition_comparison_core
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : perfectOverlapCoreStatement R c hc i Z t j hij hstage
```

## Users

Only the own module references either changed declaration by name. Its core proof now passes the prescribed equation. The table includes every transitive importer reported by downstream.py, although no other declaration signature changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | N2 | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore | H1 | Own stage/coherence interfaces corrected; core packaging adapted, core signature unchanged. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex | H3 | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| TargetsCheck | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No named use of changed stage/coherence declarations; public core signature unchanged; no adaptation. |


## Status

landed 20261014T050526-L-1684913 2026-10-14 (merge of deliver/H1/Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore)
