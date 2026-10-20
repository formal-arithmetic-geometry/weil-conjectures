/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exactness of the etale to pro-etale comparison pullback

Source: Stacks Project, Tags 04JC and 03D2; Pro-etale Cohomology, Tags 099R and
0GLZ (blueprint: lem-sf-comparison-pullback-exact).

## Main declarations

* `AlgebraicGeometry.comparisonConstantRingMap`: the canonical constant-ring comparison.
* `AlgebraicGeometry.comparisonPullbackExact`: its tensor identification, exactness and
  compatibility with cohomology sheaves.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped ChangeOfRings

namespace AlgebraicGeometry

/-- The canonical constant-ring comparison, adjoint to the map of constant etale
rings induced by the constant scalar sections of the pro-etale ring sheaf.
Source: Stacks, Tags 0H7J, 099R and 03D2
(blueprint: lem-sf-comparison-pullback-exact). -/
noncomputable def comparisonConstantRingMap (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] :
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
      CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
        (CommRingCat.of Λ) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt T)
    CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).homEquiv _ _).symm
      (((constantSheafAdj T.smallEtaleTopology CommRingCat.{u + 1}
        (Scheme.Etale.isTerminalMkId T)).homEquiv _ _).symm
          ((toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ))).app
              (Opposite.op (Scheme.ProEt.mk (𝟙 T)))))

private noncomputable def tensorSectionMap
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J CommRingCat.{u + 1}} (c : A ≅ B)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (W : Cᵒᵖ) :
    ((ModuleCat.extendScalars (c.hom.hom.app W).hom).obj (M.val.obj W)) →+
      M.val.obj W := by
  letI : Module (A.obj.obj W) (B.obj.obj W) :=
    Module.compHom (B.obj.obj W) (c.hom.hom.app W).hom
  let e : A.obj.obj W ≃+* B.obj.obj W :=
    (((sheafToPresheaf J CommRingCat.{u + 1}).mapIso c).app W).commRingCatIsoToRingEquiv
  let f : B.obj.obj W →+ M.val.obj W →+ M.val.obj W :=
    { toFun := fun b ↦
        { toFun := fun m ↦ e.symm b • m
          map_zero' := smul_zero _
          map_add' := smul_add _ }
      map_zero' := by ext m; simp
      map_add' := by intro b d; ext m; simp [add_smul] }
  exact TensorProduct.liftAddHom f (by
    intro r b m
    change B.obj.obj W at b
    change e.symm (e r * b) • m = e.symm b • (r • m)
    rw [map_mul, e.symm_apply_apply, mul_smul, smul_comm])

private theorem tensorSectionMap_tmul
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J CommRingCat.{u + 1}} (c : A ≅ B)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (W : Cᵒᵖ)
    (b : B.obj.obj W) (m : M.val.obj W) :
    tensorSectionMap c M W (b ⊗ₜ[_, (c.hom.hom.app W).hom] m) =
      c.inv.hom.app W b • m := rfl

private noncomputable def tensorSectionIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J CommRingCat.{u + 1}} (c : A ≅ B)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (W : Cᵒᵖ) :
    AddCommGrpCat.of ((ModuleCat.extendScalars (c.hom.hom.app W).hom).obj
      (M.val.obj W)) ≅ AddCommGrpCat.of (M.val.obj W) := by
  letI : Module (A.obj.obj W) (B.obj.obj W) :=
    Module.compHom (B.obj.obj W) (c.hom.hom.app W).hom
  let e : A.obj.obj W ≃+* B.obj.obj W :=
    (((sheafToPresheaf J CommRingCat.{u + 1}).mapIso c).app W).commRingCatIsoToRingEquiv
  let back : M.val.obj W →+ ((ModuleCat.extendScalars (c.hom.hom.app W).hom).obj
      (M.val.obj W)) :=
    { toFun := fun m ↦ (1 : B.obj.obj W) ⊗ₜ[_, (c.hom.hom.app W).hom] m
      map_zero' := TensorProduct.tmul_zero _ _
      map_add' := TensorProduct.tmul_add _ }
  refine ⟨AddCommGrpCat.ofHom (tensorSectionMap c M W), AddCommGrpCat.ofHom back, ?_, ?_⟩
  · ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      change B.obj.obj W at b
      change (1 : B.obj.obj W) ⊗ₜ[_, (c.hom.hom.app W).hom] (e.symm b • m) = b ⊗ₜ m
      rw [← TensorProduct.smul_tmul]
      change (e (e.symm b) * 1) ⊗ₜ m = b ⊗ₜ m
      rw [e.apply_symm_apply, mul_one]
    | add z w hz hw =>
      change back (tensorSectionMap c M W (z + w)) = z + w
      change back (tensorSectionMap c M W z) = z at hz
      change back (tensorSectionMap c M W w) = w at hw
      rw [map_add, map_add, hz, hw]
  · ext m
    change tensorSectionMap c M W ((1 : B.obj.obj W) ⊗ₜ[_, (c.hom.hom.app W).hom] m) = m
    rw [tensorSectionMap_tmul, map_one, one_smul]

private noncomputable def tensorPresheafIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {A B : Sheaf J CommRingCat.{u + 1}} (c : A ≅ B)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
      c.hom M).presheaf ≅ M.val.presheaf := by
  refine NatIso.ofComponents (tensorSectionIso c M) ?_
  intro X Y i
  ext z
  change tensorSectionMap c M Y
    (SheafOfModules.changeOfRingsMapOfUniverses c.hom M i z) =
      M.val.map i (tensorSectionMap c M X z)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    change B.obj.obj X at b
    erw [SheafOfModules.changeOfRingsMap_tmulOfUniverses c.hom M i b m]
    rw [tensorSectionMap_tmul, tensorSectionMap_tmul]
    have hn := ConcreteCategory.congr_hom (c.inv.hom.naturality i) b
    change c.inv.hom.app Y (B.obj.map i b) = A.obj.map i (c.inv.hom.app X b) at hn
    rw [hn]
    exact ((M.val.restrictₛₗ i).map_smulₛₗ _ _).symm
  | add z w hz hw =>
    simp only [map_add, hz, hw]

/-- The inverse image along the etale/pro-etale comparison is exact on finite
coefficient module sheaves and commutes with cohomology sheaves.

Source: Stacks Project, Tags 04JC and 03D2; Pro-etale Cohomology, Tags 099R and
0GLZ (blueprint: lem-sf-comparison-pullback-exact).
Proof:
1. Compose the constant-sheaf adjunction on the etale site with the ring-valued
   comparison adjunction. Restriction preserves sections at the terminal object,
   so uniqueness of left adjoints identifies the composite with the pro-etale
   constant-sheaf functor. The hom-equivalence formula for this identification
   shows that its forward map is exactly comparisonConstantRingMap.
2. Sectionwise tensor contraction sends b tensor m to c.inv(b) times m and its
   inverse sends m to 1 tensor m. The balanced relation proves the inverse
   identities. Naturality of c.inv and semilinearity of restrictions give an
   isomorphism of abelian presheaves. Sheafify this isomorphism and compose with
   the sheafification counit. Naturality of the unit and the triangle identity
   give the required formula on the original pure tensors.
3. The existing comparisonUpperStar instances prove additivity and preservation
   of finite limits and finite colimits, directly for fixed coefficient modules.
4. Mathlib's mapHomologyIso on each three-term segment gives the natural
   cohomology isomorphism. Preservation of quasi-isomorphisms is its existing
   consequence; preservation of zero objects and the same isomorphism give
   vanishing in every degree below the specified bound. -/
theorem comparisonPullbackExact (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    (∃ c :
      ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
          CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) ≅
        (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)),
      c.hom = comparisonConstantRingMap T Λ ∧
      ∀ M : SheafOfModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
              CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).obj
                ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                  (CommRingCat.of Λ)))),
      ∃ e :
        (SheafOfModules.toSheaf
          ((sheafCompose (Scheme.ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
                (CommRingCat.of Λ)))).obj
                  (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
                    (C := T.ProEt) (J := Scheme.ProEt.topology T) c.hom M) ≅
        (SheafOfModules.toSheaf
          ((sheafCompose (Scheme.ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
                CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).obj
                  ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                    (CommRingCat.of Λ))))).obj M,
      ∀ (W : T.ProEtᵒᵖ)
        (b : ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)).obj.obj W) (m : M.val.obj W),
        e.hom.hom.app W
          (((PresheafOfModules.sheafificationAdjunction.{u + 1}
            (R := (sheafCompose (Scheme.ProEt.topology T)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
                  (CommRingCat.of Λ)))
            (𝟙 (((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
              (CommRingCat.of Λ)).obj ⋙ forget₂ CommRingCat RingCat))).unit.app
                (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
                  (C := T.ProEt) (J := Scheme.ProEt.topology T) c.hom M)).app W
                  (b ⊗ₜ[_, (c.hom.hom.app W).hom] m)) =
          c.inv.hom.app W b • m) ∧
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).Additive ∧
      PreservesFiniteLimits
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T) ∧
      PreservesFiniteColimits
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T) ∧
      (∀ (i : ℤ),
        Nonempty
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙
            HomologicalComplex.homologyFunctor
              (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))
              (ComplexShape.up ℤ) i ≅
            HomologicalComplex.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
              (ComplexShape.up ℤ) i ⋙
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T)) ∧
      (∀ {K L : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
        (f : K ⟶ L),
        HomologicalComplex.quasiIso _ (ComplexShape.up ℤ) f →
          HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f)) ∧
      (∀ (a : ℤ)
        (K : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ),
        (∀ i : ℤ, i < a → IsZero (K.homology i)) →
          ∀ i : ℤ, i < a →
            IsZero
              ((((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K).homology i)) := by
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T
  refine ⟨?_, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.toProEt T) CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)
    let adjEt := constantSheafAdj T.smallEtaleTopology CommRingCat.{u + 1}
      (Scheme.Etale.isTerminalMkId T)
    let adjPro := constantSheafAdj (Scheme.ProEt.topology T) CommRingCat.{u + 1}
      ((Scheme.Etale.isTerminalMkId T).isTerminalObj (Scheme.toProEt T))
    let e := (adjEt.comp adj).leftAdjointUniq adjPro
    refine ⟨e.app (CommRingCat.of Λ), ?_, ?_⟩
    · apply (adj.homEquiv _ _).injective
      dsimp only [comparisonConstantRingMap]
      rw [Equiv.apply_symm_apply]
      apply (adjEt.homEquiv _ _).injective
      change (adjEt.comp adj).homEquiv _ _ (e.hom.app (CommRingCat.of Λ)) = _
      rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
      rw [Equiv.apply_symm_apply]
      rfl
    · intro M
      let c := e.app (CommRingCat.of Λ)
      let P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c.hom M
      let Q := (SheafOfModules.toSheaf _).obj M
      let p := tensorPresheafIso c M
      let a := CategoryTheory.sheafificationAdjunction (Scheme.ProEt.topology T)
        AddCommGrpCat.{u + 1}
      refine ⟨(presheafToSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).mapIso p ≪≫
        asIso (a.counit.app Q), ?_⟩
      intro W b m
      let z : P.obj W := b ⊗ₜ[_, (c.hom.hom.app W).hom] m
      have hn := congrArg (fun f ↦ f.app W z) (a.unit_naturality p.hom)
      have hc (y : Q.obj.obj W) :=
        congrArg (fun f ↦ f.app W y) (a.right_triangle_components Q)
      change (a.counit.app Q).hom.app W
        (((presheafToSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).map p.hom).hom.app W
          ((toSheafify (Scheme.ProEt.topology T) P.presheaf).app W z)) =
            c.inv.hom.app W b • m
      exact (congrArg ((a.counit.app Q).hom.app W) hn).trans
        ((hc (p.hom.app W z)).trans (tensorSectionMap_tmul c M W b m))
  · intro i
    exact ⟨NatIso.ofComponents (fun K ↦ (K.sc i).mapHomologyIso F)
      (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ i).map f) F)⟩
  · intro K L f hf
    have : QuasiIso f := hf
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f F
  · intro a K hK i hi
    exact (F.map_isZero (hK i hi)).of_iso ((K.sc i).mapHomologyIso F)

end AlgebraicGeometry
