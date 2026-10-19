module

public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.LerayComplexCocycleComparison

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

def LerayEdge (X Y : Scheme.{u}) (f : X ⟶ Y) :=
  ∀ q : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ⟶
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q ⋙
      RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat

def LerayEdgeCocycle {X Y : Scheme.{u}} (f : X ⟶ Y) (ε : LerayEdge X Y f) : Prop :=
  ∀ (q : ℕ) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (I : InjectiveResolution F)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℕ)
    (hK : K = ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
    (s : (RingedSpace.globalSectionsComplex I).cycles q),
    ∃ z : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj (K.cycles q),
      (I.cocomplex.X q).val.presheaf.map
          (eqToHom (congrArg op (Opens.map_top f.base).symm))
          ((RingedSpace.globalSectionsComplex I).iCycles q s) =
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
          (K.iCycles q ≫ (eqToHom hK).f q) z ∧
      (ε q).app F
          ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv
            ((RingedSpace.globalSectionsComplex I).homologyπ q s)) =
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
          ((K.homologyπ q) ≫ HomologicalComplex.homologyMap (eqToHom hK) q ≫
            (I.isoRightDerivedObj
              (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) q).inv) z

set_option maxHeartbeats 800000 in
-- Resolution comparison unfolds both module-valued derived functors and forgetful maps.
set_option backward.isDefEq.respectTransparency false in
/-- Construction of the cocycle Leray edge.
(blueprint: lem-pc-leray-edge-cocycle-data)

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.

Proof: apply the Grothendieck spectral-sequence edge construction to direct image
followed by global sections. The resulting edge is represented on an injective
resolution by the displayed cycle and homology maps, which gives the stated
cocycle equation. More explicitly, direct images of injectives are acyclic
for sections by module_pushforward_injective_acyclic. Apply
grothendieck_left_edge_cocycle to these two additive left exact functors and
identify their composite with sections on X via restriction along Opens.map_top.
Left exactness identifies sections of the cycle sheaf with cycles of the
sections complex, so the global cocycle lifts uniquely to z. The generic edge
equation, transported by the resolution comparison isomorphisms, is the second
equality. Resolution comparison and functoriality give a single natural edge
for every coefficient module, independent of the chosen resolution. -/
theorem leray_edge_cocycle_data {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ ε : LerayEdge X Y f, LerayEdgeCocycle f ε := by
  classical
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let H := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  choose τ hτ using leray_complex_cocycle_comparison f
  let ε : LerayEdge X Y f := fun q ↦
    { app := fun F ↦
        (forget₂ _ AddCommGrpCat).map
            ((injectiveResolution F).isoRightDerivedObj G q).hom ≫
          (τ q).app (injectiveResolution F).cocomplex ≫
          (H ⋙ forget₂ _ AddCommGrpCat).map
            ((injectiveResolution F).isoRightDerivedObj D q).inv
      naturality := by
        intro F F' a
        let I := injectiveResolution F
        let J := injectiveResolution F'
        let φ := InjectiveResolution.desc a J I
        have comm : I.ι.f 0 ≫ φ.f 0 = a ≫ J.ι.f 0 := by
          simp [φ]
        have hG := InjectiveResolution.isoRightDerivedObj_hom_naturality a I J φ comm G q
        have hD := InjectiveResolution.isoRightDerivedObj_inv_naturality a I J φ comm D q
        have hG' := congrArg ((forget₂ _ AddCommGrpCat).map) hG
        have hD' := congrArg ((H ⋙ forget₂ _ AddCommGrpCat).map) hD
        simp only [Functor.map_comp] at hG' hD'
        change (forget₂ _ AddCommGrpCat).map ((G.rightDerived q).map a) ≫
            (forget₂ _ AddCommGrpCat).map (J.isoRightDerivedObj G q).hom ≫
            (τ q).app J.cocomplex ≫
            (H ⋙ forget₂ _ AddCommGrpCat).map (J.isoRightDerivedObj D q).inv =
          ((forget₂ _ AddCommGrpCat).map (I.isoRightDerivedObj G q).hom ≫
            (τ q).app I.cocomplex ≫
            (H ⋙ forget₂ _ AddCommGrpCat).map (I.isoRightDerivedObj D q).inv) ≫
            (H ⋙ forget₂ _ AddCommGrpCat).map ((D.rightDerived q).map a)
        rw [← Category.assoc, hG', Category.assoc]
        have hnat := (τ q).naturality φ
        change (forget₂ _ AddCommGrpCat).map
            ((G.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ q).map φ) ≫
            (τ q).app J.cocomplex =
          (τ q).app I.cocomplex ≫ (H ⋙ forget₂ _ AddCommGrpCat).map
            ((D.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ q).map φ)
          at hnat
        rw [← Category.assoc _ ((τ q).app J.cocomplex), hnat]
        simp only [Category.assoc]
        rw [← hD'] }
  dsimp only [LerayEdge, RingedSpace.moduleCohomology] at ε
  refine ⟨ε, ?_⟩
  intro q F I K hK s
  subst K
  obtain ⟨z, hz, hz'⟩ := hτ q I.cocomplex s
  refine ⟨z, ?_, ?_⟩
  · simpa only [eqToHom_refl, Category.comp_id, Functor.map_id, HomologicalComplex.id_f,
      RingedSpace.globalSectionsComplex] using hz
  · have hε : (forget₂ _ AddCommGrpCat).map (I.isoRightDerivedObj G q).inv ≫
        (ε q).app F = (τ q).app I.cocomplex ≫
          (H ⋙ forget₂ _ AddCommGrpCat).map (I.isoRightDerivedObj D q).inv := by
      let J := injectiveResolution F
      let φ := InjectiveResolution.desc (𝟙 F) J I
      have comm : I.ι.f 0 ≫ φ.f 0 = (𝟙 F) ≫ J.ι.f 0 := by simp [φ]
      have hG := InjectiveResolution.isoRightDerivedObj_inv_naturality
        (𝟙 F) I J φ comm G q
      have hD := InjectiveResolution.isoRightDerivedObj_inv_naturality
        (𝟙 F) I J φ comm D q
      rw [(G.rightDerived q).map_id, Category.comp_id] at hG
      rw [(D.rightDerived q).map_id, Category.comp_id] at hD
      have hG' := congrArg ((forget₂ _ AddCommGrpCat).map) hG
      have hD' := congrArg ((H ⋙ forget₂ _ AddCommGrpCat).map) hD
      simp only [Functor.map_comp] at hG' hD'
      change (forget₂ _ AddCommGrpCat).map (I.isoRightDerivedObj G q).inv ≫
          ((forget₂ _ AddCommGrpCat).map (J.isoRightDerivedObj G q).hom ≫
            (τ q).app J.cocomplex ≫
            (H ⋙ forget₂ _ AddCommGrpCat).map (J.isoRightDerivedObj D q).inv) = _
      rw [hG']
      rw [Category.assoc]
      have hc : (forget₂ _ AddCommGrpCat).map (J.isoRightDerivedObj G q).inv ≫
          (forget₂ _ AddCommGrpCat).map (J.isoRightDerivedObj G q).hom = 𝟙 _ := by
        rw [← Functor.map_comp, Iso.inv_hom_id]
        exact (forget₂ _ AddCommGrpCat).map_id _
      rw [← Category.assoc _ ((forget₂ _ AddCommGrpCat).map
        (J.isoRightDerivedObj G q).hom), hc]
      erw [Category.id_comp]
      have hnat := (τ q).naturality φ
      change (forget₂ _ AddCommGrpCat).map
          ((G.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ q).map φ) ≫
          (τ q).app J.cocomplex =
        (τ q).app I.cocomplex ≫ (H ⋙ forget₂ _ AddCommGrpCat).map
          ((D.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ q).map φ)
        at hnat
      rw [← Category.assoc, hnat, Category.assoc, ← hD']
    have heval := congrArg
      (fun a : (forget₂ _ AddCommGrpCat).obj
          ((RingedSpace.globalSectionsComplex I).homology q) ⟶
        (H ⋙ forget₂ _ AddCommGrpCat).obj ((D.rightDerived q).obj F) ↦
        a ((RingedSpace.globalSectionsComplex I).homologyπ q s)) hε
    simp only [eqToHom_refl, HomologicalComplex.homologyMap_id]
    rw [Category.id_comp, H.map_comp]
    change (ε q).app F
        ((I.isoRightDerivedObj G q).inv
          ((RingedSpace.globalSectionsComplex I).homologyπ q s)) =
      (H.map (I.isoRightDerivedObj D q).inv)
        ((H.map ((((D.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).homologyπ q))) z)
    exact heval.trans (congrArg
      (fun t ↦ (H.map (I.isoRightDerivedObj D q).inv) t) hz')
end AlgebraicGeometry
