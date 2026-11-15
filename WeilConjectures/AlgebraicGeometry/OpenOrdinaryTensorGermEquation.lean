/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
import WeilConjectures.AlgebraicGeometry.OpenStalkRepresentativeCoherence
import WeilConjectures.AlgebraicGeometry.OpenTensorRestrictionRepresentative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange
private theorem assemble_homology_transport
    {D : Type*} [Category D]
    {A B C E Z A' B' C' E' C₁ E₁ : D}
    {p : A ⟶ B} {x : B ⟶ C} {b : C ⟶ E} {ν : E ⟶ Z}
    {a : B ⟶ B'} {q : B' ⟶ E'} {c : E' ⟶ E₁} {d : E₁ ⟶ Z}
    {u : A ⟶ A'} {l : A' ⟶ B'} {v : A' ⟶ C'} {w : C' ⟶ E'}
    {t : C' ⟶ C₁} {r : C₁ ⟶ E₁}
    (hc : x ≫ b ≫ ν = a ≫ q ≫ c ≫ d)
    (h₀ : p ≫ a = u ≫ l) (h : v ≫ w = l ≫ q) (h₁ : w ≫ c = t ≫ r) :
    p ≫ x ≫ b ≫ ν = u ≫ v ≫ t ≫ r ≫ d := by
  rw [hc, reassoc_of% h₀, ← reassoc_of% h, reassoc_of% h₁]

attribute [local irreducible] tensorStalkIso tensorComplex openPinnedTensorRestrictionIso
attribute [local irreducible] openDerivedAdditiveStalkIso comparisonStalkHomologyIso

/-- A degreewise canonical open tensor-stalk square induces the homology square. -/
theorem openOrdinaryTensor_germ_transport_equation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let C₀ := C z
    let C₁ := C z.val
    let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
    let T := tensorComplex f f' g g' sq z.val P
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    let k₀ := HomologicalComplex.homologyMap
      (tensorStalkIso (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀).hom i ≫
      (comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z
        (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q₀) i).inv
    let k := HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z.val P).hom i ≫
      (comparisonStalkHomologyIso X' z.val
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv
    let L₀ := RingedSpace.moduleStalkFunctor (f' ⁻¹ᵁ V').toScheme.toRingedSpace z
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f' ⁻¹ᵁ V'))
        (L₀ ⋙ F₀) ≪≫ Scheme.Modules.restrictStalkNatIso (f' ⁻¹ᵁ V').ι z
    ∀ (τ : (F₀.mapHomologicalComplex (.up ℤ)).obj T₀ ≅
        (F.mapHomologicalComplex (.up ℤ)).obj T),
      (∀ n : ℤ,
        τ.hom.f n ≫ F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n) =
          F₀.map ((tensorStalkIso (f ∣_ V) (f' ∣_ V')
            (g.resLE V V' hV') j sq₀ z Q₀).hom.f n) ≫
            F₀.map (L₀.map ((openPinnedTensorRestrictionIso g'
              (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))) ≫
            γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n))) →
      F₀.map k₀ ≫ F₀.map (H₀.map β) ≫
          ν.hom.app (DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
        ((T₀.sc i).mapHomologyIso F₀).inv ≫
          HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom ≫
            F.map k := by
  intro Q₀ C₀ C₁ T₀ T F₀ F H₀ β ν k₀ k L₀ γ τ hτ
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
    schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
  have : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).Additive :=
    schemeOpenRestriction_additive X' (f' ⁻¹ᵁ V')
  have : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive := fun k ↦ tensorPullbackAdditive k
  let N₀ : CochainComplex
      (SheafOfModules.{u} (moduleRings (f' ⁻¹ᵁ V').toScheme.toRingedSpace)) ℤ :=
    ((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q₀
  let N : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ :=
    ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let L := RingedSpace.moduleStalkFunctor X'.toRingedSpace z.val
  let γ' : schemeOpenRestriction X' (f' ⁻¹ᵁ V') ⋙ L₀ ⋙ F₀ ≅ L ⋙ F := γ
  let a : N₀ ⟶ ((schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapHomologicalComplex
      (.up ℤ)).obj N :=
    (NatTrans.mapHomologicalComplex
      (openPinnedTensorRestrictionIso g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv (.up ℤ)).app P
  let ρ := (F₀.mapHomologicalComplex (.up ℤ)).map
      ((L₀.mapHomologicalComplex (.up ℤ)).map a) ≫
    (NatTrans.mapHomologicalComplex γ'.hom (.up ℤ)).app N
  let e₀ := tensorStalkIso (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
  let e := tensorStalkIso f f' g g' sq z.val P
  have hchain : τ.hom ≫ (F.mapHomologicalComplex (.up ℤ)).map e.hom =
      (F₀.mapHomologicalComplex (.up ℤ)).map e₀.hom ≫ ρ := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hτ n
  have hhom := congrArg (fun t ↦ HomologicalComplex.homologyMap t i) hchain
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  have hc := openStalk_representative_coherence X' (f' ⁻¹ᵁ V') z i N₀ N a
  have hn₀ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map e₀.hom) F₀
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map e.hom) F
  change F₀.map (HomologicalComplex.homologyMap e₀.hom i) ≫
      ((((L₀.mapHomologicalComplex (.up ℤ)).obj N₀).sc i).mapHomologyIso F₀).inv =
    ((T₀.sc i).mapHomologyIso F₀).inv ≫
      HomologicalComplex.homologyMap ((F₀.mapHomologicalComplex (.up ℤ)).map e₀.hom) i
    at hn₀
  change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map e.hom) i ≫
      ((((L.mapHomologicalComplex (.up ℤ)).obj N).sc i).mapHomologyIso F).hom =
    ((T.sc i).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap e.hom i) at hn
  have hresult := assemble_homology_transport hc hn₀ hhom hn
  calc
    _ = F₀.map (HomologicalComplex.homologyMap e₀.hom i) ≫
        F₀.map (comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z N₀ i).inv ≫
        F₀.map (H₀.map β) ≫ ν.hom.app (DerivedCategory.Q.obj N) :=
      (congrArg (fun t ↦ t ≫ F₀.map (H₀.map β) ≫ ν.hom.app (DerivedCategory.Q.obj N))
        (F₀.map_comp _ _)).trans (Category.assoc _ _ _)
    _ = ((T₀.sc i).mapHomologyIso F₀).inv ≫
        HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.homologyMap e.hom i) ≫
        F.map (comparisonStalkHomologyIso X' z.val N i).inv := hresult
    _ = _ := congrArg (fun t ↦ ((T₀.sc i).mapHomologyIso F₀).inv ≫
        HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom ≫ t)
      (F.map_comp _ _).symm


end AlgebraicGeometry
