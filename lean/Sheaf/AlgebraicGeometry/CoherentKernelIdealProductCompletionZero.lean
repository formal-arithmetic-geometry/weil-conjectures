/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import all Sheaf.AlgebraicGeometry.CoherentFormalModule
import all Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import all Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.FormalCompletionAffineSections
import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # Vanishing of the completion of a coherent kernel's ideal product

Source: Stacks Project, Tags 088A, 087W and 00MB.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private noncomputable def completionSectionsUnit {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) (U : X.affineOpens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U.1)).obj M ⟶
      limit (formalCompletionSystem I M ⋙
        SheafOfModules.evaluation X.ringCatSheaf (op U.1)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  refine limit.lift (formalCompletionSystem I M ⋙ E) { pt := E.obj M, π :=
    { app := fun n : ℕᵒᵖ ↦ E.map (formalModuleQuotientπ I (n.unop + 1) M)
      naturality := ?_ } }
  intro n m f
  symm
  change E.map (formalModuleQuotientπ I (n.unop + 1) M) ≫
    E.map (formalModuleQuotientMap I (𝟙 M) (Nat.succ_le_succ (leOfHom f.unop))) = _
  rw [← E.map_comp]
  simp [formalModuleQuotientMap, formalModuleQuotientπ]

set_option backward.isDefEq.respectTransparency false in
private theorem completionSectionsUnit_π {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) (U : X.affineOpens) (n : ℕᵒᵖ) :
    completionSectionsUnit I M U ≫ limit.π _ n =
      (SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map
        (formalModuleQuotientπ I (n.unop + 1) M) := by
  simpa only [completionSectionsUnit] using
    (limit.lift_π (F := formalCompletionSystem I M ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op U.1)) _ n)

set_option backward.isDefEq.respectTransparency false in
private theorem completionSectionsUnit_naturality {X : Scheme.{u}}
    (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) (U : X.affineOpens) :
    completionSectionsUnit I M U ≫ lim.map (Functor.whiskerRight
        (formalCompletionMap I f) (SheafOfModules.evaluation X.ringCatSheaf (op U.1))) =
      (SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map f ≫
        completionSectionsUnit I N U := by
  apply limit.hom_ext
  intro n
  change (completionSectionsUnit I M U ≫ limMap _) ≫ _ = _
  rw [Category.assoc]
  erw [limMap_π]
  rw [ ← Category.assoc, completionSectionsUnit_π,
    Category.assoc, completionSectionsUnit_π]
  change _ ≫ (SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map
    (formalModuleQuotientMap I f (Nat.le_refl _)) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp [formalModuleQuotientMap, formalModuleQuotientπ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completionSections_dictionary {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) :
    let A := Γ(X, U.1)
    let J := I.ideal U
    let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
    ∃ (q : ∀ n : ℕ, ModuleCat.of A
        (Γ(M, U.1) ⧸ (J ^ (n + 1) • (⊤ : Submodule A Γ(M, U.1)))) ≅
          E.obj (formalModuleQuotient I (n + 1) M))
      (e : ModuleCat.of A (AdicCompletion J Γ(M, U.1)) ≅
        limit (formalCompletionSystem I M ⋙ E)),
      (∀ n, ModuleCat.ofHom (Submodule.mkQ (J ^ (n + 1) • ⊤)) ≫ (q n).hom =
        E.map (formalModuleQuotientπ I (n + 1) M)) ∧
      (∀ n, e.hom ≫ limit.π _ (op n) =
        ModuleCat.ofHom (AdicCompletion.eval J Γ(M, U.1) (n + 1)) ≫ (q n).hom) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let S := formalCompletionSystem I M
  obtain ⟨q, hq, e, he⟩ := formalCompletion_affine_sections I M U.1 U.2
  let e' := e ≪≫ preservesLimitIso E S
  have he' (n : ℕ) : e'.hom ≫ limit.π _ (op n) =
      ModuleCat.ofHom (AdicCompletion.eval (I.ideal U) Γ(M, U.1) (n + 1)) ≫
        (q n).hom := by
    dsimp only [e', Iso.trans_hom]
    rw [Category.assoc, preservesLimitIso_hom_π, he]
  exact ⟨q, e', hq, he'⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
-- Comparing the evaluated quotient maps unfolds several layers of sheaf functors.
private theorem completionSections_map_injective {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Mono f]
    (U : X.affineOpens) [Module.Finite Γ(X, U.1) Γ(N, U.1)] :
    Function.Injective (lim.map (Functor.whiskerRight (formalCompletionMap I f)
      (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))) := by
  let A := Γ(X, U.1)
  let J := I.ideal U
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let L := (E.map f).hom
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite A (E.obj N) := ‹Module.Finite Γ(X, U.1) Γ(N, U.1)›
  have hinj : Function.Injective L :=
    (ModuleCat.mono_iff_injective _).mp (E.map_mono f)
  obtain ⟨qM, eM, hqM, heM⟩ := completionSections_dictionary I M U
  obtain ⟨qN, eN, hqN, heN⟩ := completionSections_dictionary I N U
  let α := Functor.whiskerRight (formalCompletionMap I f) E
  have hn : eM.hom ≫ lim.map α =
      ModuleCat.ofHom ((AdicCompletion.map J L).restrictScalars A) ≫ eN.hom := by
    apply limit.hom_ext
    intro n
    change (eM.hom ≫ limMap α) ≫ _ = _
    rw [Category.assoc]
    erw [limMap_π]
    rw [← Category.assoc, heM]
    simp only [Category.assoc]
    erw [heN n.unop]
    rw [← Category.assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (E.map (formalModuleQuotientMap I f (Nat.le_refl _)))
      ((qM n.unop).hom (AdicCompletion.eval J Γ(M, U.1) (n.unop + 1) x)) =
      (qN n.unop).hom (AdicCompletion.eval J Γ(N, U.1) (n.unop + 1)
        (AdicCompletion.map J L x))
    obtain ⟨y, hy⟩ := (J ^ (n.unop + 1) • (⊤ : Submodule A Γ(M, U.1))).mkQ_surjective
      (AdicCompletion.eval J Γ(M, U.1) (n.unop + 1) x)
    have hqm := ConcreteCategory.congr_hom (hqM n.unop) y
    have hqn := ConcreteCategory.congr_hom (hqN n.unop) (L y)
    change (qM n.unop).hom ((J ^ (n.unop + 1) • (⊤ : Submodule A Γ(M, U.1))).mkQ y) =
      (E.map (formalModuleQuotientπ I (n.unop + 1) M)) y at hqm
    change (qN n.unop).hom ((J ^ (n.unop + 1) • (⊤ : Submodule A Γ(N, U.1))).mkQ (L y)) =
      (E.map (formalModuleQuotientπ I (n.unop + 1) N)) (L y) at hqn
    change (J ^ (n.unop + 1) • (⊤ : Submodule A Γ(M, U.1))).mkQ y = x.val (n.unop + 1) at hy
    simp only [AdicCompletion.eval_apply]
    rw [AdicCompletion.map_val_apply, ← hy, hqm]
    change (E.map (formalModuleQuotientMap I f (Nat.le_refl _)))
      ((E.map (formalModuleQuotientπ I (n.unop + 1) M)) y) =
        (qN n.unop).hom ((J ^ (n.unop + 1) •
          (⊤ : Submodule A Γ(N, U.1))).mkQ (L y))
    rw [hqn]
    have hnatu := ConcreteCategory.congr_hom
      (congrArg (fun g ↦ E.map g)
        (show formalModuleQuotientπ I (n.unop + 1) M ≫
          formalModuleQuotientMap I f (Nat.le_refl _) =
          f ≫ formalModuleQuotientπ I (n.unop + 1) N by
            simp [formalModuleQuotientMap, formalModuleQuotientπ])) y
    exact hnatu
  intro x y hxy
  obtain ⟨x', rfl⟩ := eM.toLinearEquiv.surjective x
  obtain ⟨y', rfl⟩ := eM.toLinearEquiv.surjective y
  apply congrArg eM.hom
  apply AdicCompletion.map_injective J hinj
  apply eN.toLinearEquiv.injective
  have hn' := fun z ↦ ConcreteCategory.congr_hom hn z
  exact (hn' x').symm.trans (hxy.trans (hn' y'))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
-- The affine-limit comparison and sheaf separatedness require extra elaboration steps.
/-- An affine limit-kernel annihilator makes every reduction of the coherent
ideal product with the original kernel zero.
Source: Stacks Project, Tag 088A, second application of Remark 0888;
Tag 087W and Algebra, Tag 00MB (exactness of finite-module completion).
(blueprint: lem-weil-pbc-coherent-kernel-ideal-product-completion-zero).

Proof:
1. The kernel of a map between coherent modules on a Noetherian scheme is coherent.
The ideal power is quasi-coherent and locally finitely generated. Its product with
this kernel is quasi-coherent and a submodule of a coherent module, hence coherent.
2. On an affine open U, exact affine sections identify the sheaf kernel with the
kernel of the section map and the ideal product with K(U)^t times that kernel.
Finite-module completion is tensoring with the flat completed ring. It therefore
identifies the completion of this kernel with the kernel of the completed map,
and the completion of its ideal product with the image of the completed ideal action.
3. The natural quotient and inverse-limit comparisons identify the completed map
with the inverse limit of the section maps of the quotient system. The stated
annihilator bound makes the image from step 2 zero. Thus the completion of the
ideal product is zero on every affine open.
4. Each positive quotient is a quotient of that finite-module completion, so it
is zero on each affine open. The affine opens form a basis, and sheaf separatedness
makes each quotient zero globally. This includes t = 0, the empty affine, and the
unit completion ideal; no faithfulness of affine completion is used.
-/
theorem coherentKernel_idealProduct_completion_zero
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (F G : CoherentModules X) (a : F ⟶ G) (t : ℕ)
    (h : ∀ U : X.affineOpens,
      K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight ((completion X I).map a).hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom)) :
    RingedSpace.IsCoherent X.toRingedSpace
      (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel a.hom)) ∧
    ∀ n : ℕ, IsZero (formalModuleQuotient I (n + 1)
      (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel a.hom))) := by
  sorry

end AlgebraicGeometry
