/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.TensorPullbackKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs

/-! Natural comparison transformation for the derived stalk extension.
(blueprint: lem-pc-stalk-derived-extension-comparison-core) -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem extendScalars_transport_naturality
    {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀]
    {a b : R₀ →+* S₀} (h : a = b) {M N : ModuleCat.{u} R₀} (s : M ⟶ N) :
    (ModuleCat.extendScalars.{u, u, u} a).map s ≫
        eqToHom (congrArg (fun r ↦ (ModuleCat.extendScalars.{u, u, u} r).obj N) h) =
      eqToHom (congrArg (fun r ↦ (ModuleCat.extendScalars.{u, u, u} r).obj M) h) ≫
        (ModuleCat.extendScalars.{u, u, u} b).map s := by
  subst b
  simp


variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

private theorem tensorStalkIso_naturality (z : X')
    {P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (a : P ⟶ Q) :
    let := leftAlgebra f g' z
    let := rightAlgebra f f' g g' sq z
    let E := ModuleCat.extendScalars.{u, u, u}
      ((tensorMap f f' g g' sq z).comp
        (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))
    (E.mapHomologicalComplex (.up ℤ)).map
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (g' z)).mapHomologicalComplex (.up ℤ)).map a) ≫
        (tensorStalkIso f f' g g' sq z Q).hom =
      (tensorStalkIso f f' g g' sq z P).hom ≫
        ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
          (.up ℤ)).map
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).map a) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z Q) i,
    Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z P) i]
  erw [← Category.assoc, extendScalars_transport_naturality
      (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1,
    Category.assoc]
  exact congrArg (fun k ↦ _ ≫ k)
    ((Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.naturality
      (a.f i))

-- Keep the original named proof binders, even though they do not occur in the conclusion.
set_option linter.unusedVariables false in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
-- The default 200000 times out at whnf; this historical limit passed in 40 seconds remotely.
/-- A natural comparison with the specified K-flat representative equation, without an
invertibility assertion.

Proof: identify the composite stalk ring map with the actual stalk map of g'.
On K-flat sheaf complexes use the scalar-extension counit, the Q/Qh factors,
the specified tensorStalkIso, the inverse exact-stalk factor and the inverse
pullback counit in the displayed order. Exact stalks preserve quasi-isomorphisms,
and their K-flatness follows from the stalk criterion. Naturality of the counits
and the degreewise pullback-stalk identification gives naturality for chain maps
between K-flat representatives. Every derived arrow is represented by a roof;
replace its middle complex by a K-flat resolution. Common refinements show the
induced maps are independent of the roof and resolution. They therefore descend
to a natural transformation on derived categories. For a K-flat P with invertible
pullback counit use P itself as its resolution; the construction is precisely the
stated equation. Invertibility of this transformation is a separate argument.
Source: Stacks Project, perfect.tex, equation-bc before Tag 0DJ8 (Tag 0DJ7);
Cohomology, Tags 06YB and 0D5S; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-stalk-derived-extension-comparison-core). -/
theorem exists_stalkDerivedExtensionComparisonTransformation (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (C z))
    ∀ (L : DerivedCategory (ModuleCat.{u} (A g' z)) ⥤
      DerivedCategory (ModuleCat.{u} (C z)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars.{u, u, u}
          ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
            (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategory
              (.up ℤ) ⋙ DerivedCategory.Qh)
      (hL : L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{u} (A g' z)) (.up ℤ))),
    ∃ j : comparisonDerivedStalk X (g' z) ⋙ L ⟶
        derivedPullback g' ⋙ comparisonDerivedStalk X' z,
      ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsKFlatTensor)
        (hcP : IsIso ((counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))),
        L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (g' z)).mapDerivedCategoryFactors.inv.app P) ≫
            j.app (DerivedCategory.Q.obj P) =
          L.map ((DerivedCategory.quotientCompQhIso _).inv.app (stalkComplex g' z P)) ≫
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (stalkComplex g' z P)) ≫
            DerivedCategory.Qh.map
              (((ModuleCat.extendScalars.{u, u, u}
                ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
                  (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategoryFactors
                  (.up ℤ)).hom.app
                (stalkComplex g' z P)) ≫
            (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (C z))).hom.app
              (tensorComplex f f' g g' sq z P) ≫
            DerivedCategory.Q.map (tensorStalkIso f f' g g' sq z P).hom ≫
            (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapDerivedCategoryFactors.inv.app
                (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) ≫
            (comparisonDerivedStalk X' z).map
              (cast (by rfl)
                (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (C z))
  dsimp only
  intro L ε hL
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let St := RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)
  let St' := RingedSpace.moduleStalkFunctor X'.toRingedSpace z
  let E := ModuleCat.extendScalars.{u, u, u}
    ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
      (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))
  let T := derivedPullback g' ⋙ comparisonDerivedStalk X' z
  let A₀ := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B₀ := SheafOfModules.{u} (moduleRings X'.toRingedSpace)
  let W := HomotopyCategory.quasiIso A₀ (.up ℤ)
  let α := (Functor.associator DerivedCategory.Qh (derivedPullback g')
    (comparisonDerivedStalk X' z)).inv ≫
    Functor.whiskerRight (counit g') (comparisonDerivedStalk X' z)
  have hT : T.IsLeftDerivedFunctor α W := by
    dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
    let : MonoidalCategory A₀ := SheafOfModules.monoidalCategory X.sheaf
    let : SymmetricCategory A₀ := SheafOfModules.symmetricCategory X.sheaf
    have : MonoidalPreadditive A₀ := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
    let : MonoidalClosed A₀ := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
    have : HasColimitsOfSize.{0, 0} A₀ :=
      hasColimitsOfSizeShrink.{0, 0, u, u} A₀
    have : Abelian.HasFunctorialFlatResolution A₀ := schemeModule_hasFunctorialFlatResolution X
    have : IsGrothendieckAbelian.{u} A₀ :=
      SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
    let G : A₀ ⥤ B₀ := Scheme.Modules.tensorPullback g'
    have : G.Additive := tensorPullbackAdditive.{u, w} g'
    have : (derivedPullback g').IsLeftDerivedFunctor (counit g') W :=
      (Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) g'
    have : G.PreservesKFlatQuasiIso := by
      refine ⟨?_⟩
      intro P Q hP hQ s hs
      have toIsKFlat (P : CochainComplex A₀ ℤ)
          (hP : (HomologicalComplex.quasiIso A₀ (.up ℤ)).kFlat P) :
          CochainComplex.IsKFlatTensor (R := X.sheaf) P := by
        intro F hF
        have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
          ((HomotopyCategory.quotient A₀ (.up ℤ)).obj P)).mp
            ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
        exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
          (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF)).2
      exact tensorPullback_quasiIso_of_isKFlat g' s (toIsKFlat P hP) (toIsKFlat Q hQ) hs
    exact W.localizerMorphismKFlat
      |>.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure (counit g')
        (fun P ↦ G.derives_kFlat.isIso_of_isLeftDerivedFunctor (counit g') P)
        (comparisonDerivedStalk X' z)
  have := hT
  let Sc := St.mapHomologicalComplex (.up ℤ)
  let Pc := (Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)
  let Stc := St'.mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient A₀ (.up ℤ)
  let F := ((Scheme.Modules.tensorPullback g').mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh (C := B₀)) ⋙ comparisonDerivedStalk X' z
  let βc : q ⋙ (DerivedCategory.Qh ⋙ (comparisonDerivedStalk X (g' z) ⋙ L)) ⟶
      q ⋙ F :=
    { app := fun P ↦
        L.map (St.mapDerivedCategoryFactors.hom.app P) ≫
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (Sc.obj P)) ≫
        DerivedCategory.Q.map (tensorStalkIso f f' g g' sq z P).hom ≫
        St'.mapDerivedCategoryFactors.inv.app (Pc.obj P)
      naturality := by
        intro P Q a
        change L.map (St.mapDerivedCategory.map (DerivedCategory.Q.map a)) ≫ _ =
          _ ≫ St'.mapDerivedCategory.map (DerivedCategory.Q.map (Pc.map a))
        rw [← L.map_comp_assoc, St.mapDerivedCategoryFactors_hom_naturality,
          L.map_comp_assoc]
        have hε := ε.naturality
          ((HomotopyCategory.quotient _ (.up ℤ)).map (Sc.map a))
        change L.map (DerivedCategory.Q.map (Sc.map a)) ≫
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (Sc.obj Q)) =
          ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (Sc.obj P)) ≫
            DerivedCategory.Q.map ((E.mapHomologicalComplex (.up ℤ)).map (Sc.map a)) at hε
        rw [reassoc_of% hε]
        erw [← DerivedCategory.Q.map_comp_assoc,
          tensorStalkIso_naturality f f' g g' sq z a, DerivedCategory.Q.map_comp_assoc]
        have hSt := St'.mapDerivedCategoryFactors.inv.naturality (Pc.map a)
        change DerivedCategory.Q.map (Stc.map (Pc.map a)) ≫
            St'.mapDerivedCategoryFactors.inv.app (Pc.obj Q) =
          St'.mapDerivedCategoryFactors.inv.app (Pc.obj P) ≫
            St'.mapDerivedCategory.map (DerivedCategory.Q.map (Pc.map a)) at hSt
        simpa only [Category.assoc] using congrArg
          (fun k ↦ L.map (St.mapDerivedCategoryFactors.hom.app P) ≫
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (Sc.obj P)) ≫
            DerivedCategory.Q.map (tensorStalkIso f f' g g' sq z P).hom ≫ k) hSt }
  let β : DerivedCategory.Qh ⋙ (comparisonDerivedStalk X (g' z) ⋙ L) ⟶ F :=
    CategoryTheory.Quotient.natTransLift _ βc
  let j := T.leftDerivedLift α W (comparisonDerivedStalk X (g' z) ⋙ L) β
  refine ⟨j, ?_⟩
  intro P hP hcP
  have := hcP
  have hj := T.leftDerived_fac_app α W (comparisonDerivedStalk X (g' z) ⋙ L) β (q.obj P)
  change j.app (DerivedCategory.Q.obj P) ≫ α.app (q.obj P) = βc.app P at hj
  have hα : α.app (q.obj P) =
      (comparisonDerivedStalk X' z).map ((counit g').app (q.obj P)) := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  rw [hα] at hj
  have hcoord := congrArg
    (fun k ↦ L.map (St.mapDerivedCategoryFactors.inv.app P) ≫ k ≫
      inv ((comparisonDerivedStalk X' z).map ((counit g').app (q.obj P)))) hj
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at hcoord
  dsimp only [βc] at hcoord
  simp only [Category.assoc] at hcoord
  erw [← L.map_comp_assoc, Iso.inv_hom_id_app, L.map_id, Category.id_comp] at hcoord
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
    CategoryTheory.Quotient.lift.isLift_hom, CategoryTheory.Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp, Functor.map_inv]
  simpa only [Category.assoc] using hcoord


end AlgebraicGeometry.SingleComplexBaseChange
