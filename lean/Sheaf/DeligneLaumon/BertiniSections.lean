module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections
import Sheaf.DeligneLaumon.BertiniImmersionAux
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

@[expose] public section

/-!
# Sections vanishing on a closed subscheme

Source: Stacks Project, varieties.tex, Tag 0FD5, lemma-generate-over-complement
(blueprint: lem-zl-bertini-sections).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open Scheme.Modules MonoidalCategory Opposite

-- Cache the site instances used repeatedly by free sheaves in this proof.
private theorem cachedSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := by
  infer_instance

private theorem cachedWEquals (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective
      AddCommGrpCat.{u} := by
  infer_instance

attribute [local instance] cachedSheafify cachedWEquals

private noncomputable def sectionOfTop {X : Scheme.{u}} (M : X.Modules)
    (v : Γ(M, ⊤)) : M.sections :=
  SheafOfModules.unitHomEquiv M (homOfGlobalSection M v)

private lemma sectionOfTop_eval {X : Scheme.{u}} (M : X.Modules) (v : Γ(M, ⊤)) :
    (sectionOfTop M v).val (op ⊤) = v := by
  exact (homOfGlobalSection_app_one M v ⊤).trans (presheaf_map_id_apply _ _)

private theorem unit_hom_ext_top {X : Scheme.{u}} {M : X.Modules}
    {f g : 𝟙_ X.Modules ⟶ M}
    (h : f.app ⊤ (1 : Γ(X, ⊤)) = g.app ⊤ (1 : Γ(X, ⊤))) : f = g := by
  apply (SheafOfModules.unitHomEquiv M).injective
  apply Subtype.ext
  funext U
  change f.app U.unop (1 : Γ(X, U.unop)) = g.app U.unop (1 : Γ(X, U.unop))
  have hh := congrArg (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) h
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map] at hh
  change f.app U.unop (X.presheaf.map _ (1 : Γ(X, ⊤))) =
    g.app U.unop (X.presheaf.map _ (1 : Γ(X, ⊤))) at hh
  simpa only [map_one] using hh

private theorem finite_sections (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (M : X.Modules) [M.IsInvertible] :
    letI : Module k Γ(M, ⊤) := Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
    FiniteDimensional k Γ(M, ⊤) := by
  let : Module k Γ(M, ⊤) := Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
  have := IsInvertible.sheafOfModules_isInvertible M
  have := finiteDimensional_H_of_isProper M 0 (k := k)
  let e : M.H 0 ≃ₗ[k] Γ(M, ⊤) :=
    { H.zeroLinearEquiv M with
      map_smul' a x := (H.zeroLinearEquiv M).map_smul
        (Scheme.globalSectionsRingHom (X := X) k a) x }
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def vanishingSubmodule (k : Type u) [Field k]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] (i : Z ⟶ X) (M : X.Modules) :
    letI : Module k Γ(M, ⊤) := Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
    Submodule k Γ(M, ⊤) := by
  letI : Module k Γ(M, ⊤) := Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
  exact
    { carrier := {v | pullbackΓ i M v = 0}
      zero_mem' := map_zero _
      add_mem' := fun ha hb ↦ by
        change pullbackΓ i M (_ + _) = 0
        rw [map_add, ha, hb, add_zero]
      smul_mem' := fun a v hv ↦ by
        change pullbackΓ i M (Scheme.globalSectionsRingHom (X := X) k a • v) = 0
        have hsmul : pullbackΓ i M (Scheme.globalSectionsRingHom (X := X) k a • v) =
            i.appTop (Scheme.globalSectionsRingHom (X := X) k a) • pullbackΓ i M v := by
          rw [pullbackΓ_apply, pullbackΓ_apply]
          exact Hom.app_smul _ _ _
        rw [hsmul, hv, smul_zero] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem factors_basis (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] (M : X.Modules) :
    letI : Module k Γ(M, ⊤) := Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
    ∀ (V : Submodule k Γ(M, ⊤)) (I : Type u) [Finite I]
      (b : Module.Basis I k V) (A : Type u)
      (f : SheafOfModules.free (R := X.ringCatSheaf) A ⟶ M),
      (∀ a, (M.freeHomEquiv f a).val (op ⊤) ∈ V) →
      ∃ q : SheafOfModules.free (R := X.ringCatSheaf) A ⟶
          SheafOfModules.free (R := X.ringCatSheaf) I,
        q ≫ M.freeHomEquiv.symm (fun j ↦ sectionOfTop M (b j).val) = f := by
  classical
  let : Module k Γ(M, ⊤) := Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
  intro V I _ b A f hf
  let := Fintype.ofFinite I
  let v (a : A) : V := ⟨(M.freeHomEquiv f a).val (op ⊤), hf a⟩
  let c (a : A) (j : I) : Γ(X, ⊤) := Scheme.globalSectionsRingHom (X := X) k (b.repr (v a) j)
  let q₀ (a : A) : 𝟙_ X.Modules ⟶ SheafOfModules.free (R := X.ringCatSheaf) I :=
    ∑ j : I, homOfGlobalSection (𝟙_ X.Modules) (unitSectionsEquiv ⊤ (c a j)) ≫
      SheafOfModules.ιFree j
  let q := (SheafOfModules.freeHomEquiv _).symm
    (fun a ↦ SheafOfModules.unitHomEquiv _ (q₀ a))
  refine ⟨q, ?_⟩
  apply SheafOfModules.free_hom_ext
  intro a
  have hq : SheafOfModules.ιFree a ≫ q = q₀ a := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp only [q, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  rw [← Category.assoc, hq]
  apply unit_hom_ext_top
  rw [Preadditive.sum_comp, Hom.sum_app_apply]
  have heval (j : I) :
      ((homOfGlobalSection (𝟙_ X.Modules) (unitSectionsEquiv ⊤ (c a j)) ≫
        SheafOfModules.ιFree j) ≫
        M.freeHomEquiv.symm (fun j ↦ sectionOfTop M (b j).val)).app ⊤
          (1 : Γ(X, ⊤)) = c a j • (b j).val := by
    rw [Category.assoc, ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp only [Equiv.apply_symm_apply, sectionOfTop, Equiv.symm_apply_apply]
    rw [Hom.comp_app, ConcreteCategory.comp_apply, homOfGlobalSection_app_one,
      presheaf_map_id_apply]
    change (homOfGlobalSection M (b j).val).app ⊤ (c a j) = c a j • (b j).val
    rw [homOfGlobalSection_app, presheaf_map_id_apply]
  trans ∑ j : I, c a j • (b j).val
  · exact Finset.sum_congr rfl (fun j _ ↦ heval j)
  change ∑ j : I, b.repr (v a) j • (b j).val = (v a).val
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using
    congrArg Subtype.val (b.sum_repr (v a))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_unit_one {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackObjUnitIso f).inv.app ⊤ (1 : Γ(Y, ⊤)) =
      pullbackΓ f (𝟙_ X.Modules) (1 : Γ(X, ⊤)) := by
  rw [pullbackΓ_apply]
  exact (pullbackSection_one_eq f).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_free_eval {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    {I : Type u} (s : I → M.sections) (j : I) :
    (((Scheme.Modules.pullback f).obj M).freeHomEquiv
      ((pullbackFreeIso f I).inv ≫ (Scheme.Modules.pullback f).map (M.freeHomEquiv.symm s)) j).val
      (op ⊤) = pullbackΓ f M ((s j).val (op ⊤)) := by
  change Hom.app (SheafOfModules.ιFree j ≫ (pullbackFreeIso f I).inv ≫
    (Scheme.Modules.pullback f).map (M.freeHomEquiv.symm s)) ⊤ (1 : Γ(Y, ⊤)) = _
  rw [← Category.assoc, ιFree_pullbackFreeIso_inv, Category.assoc, ← Functor.map_comp]
  rw [Hom.comp_app, ConcreteCategory.comp_apply, pullback_unit_one]
  erw [pullbackΓ_naturality]
  congr 1
  exact congrArg (fun t : I → M.sections ↦ (t j).val (op ⊤))
    (M.freeHomEquiv.apply_symm_apply s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem vanishing_range {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (L : X.Modules) [L.IsInvertible] (n : ℕ)
    (v : Γ(L.tensorPow n, ⊤)) :
    pullbackΓ i (L.tensorPow n) v = 0 ↔
      ∃ w, (i.ker.toModulesι ▷ L.tensorPow n ≫ (λ_ _).hom).app ⊤ w = v := by
  classical
  let M := L.tensorPow n
  let adj := Classical.choose (exists_tensorPullbackAdjunction i)
  let c := (adj.leftAdjointUniq (pullbackPushforwardAdjunction i)).app M
  have hc : c.hom.app ⊤ ((adj.unit.app M).app ⊤ v) = pullbackΓ i M v := by
    rw [pullbackΓ_apply]
    exact congrArg (fun t ↦ t.app ⊤ v)
      (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction i) M)
  have hinj : Function.Injective (c.hom.app ⊤) :=
    (ConcreteCategory.bijective_of_isIso (c.hom.app ⊤)).1
  have hz : pullbackΓ i M v = 0 ↔ (adj.unit.app M).app ⊤ v = 0 := by
    rw [← hc]
    exact ⟨fun h ↦ hinj (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
  exact hz.trans ((closedImmersion_ideal_tensor_sections i L n).2 v)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ideal_twist_generates {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (L : X.Modules) [L.IsInvertible] (n : ℕ)
    (σ : SheafOfModules.GeneratingSections ((i.ker.toModules : X.Modules) ⊗ₘ L.tensorPow n)) :
    Epi ((restrictFunctor (show X.Opens from i.ker.support.compl).ι).map
      (σ.π ≫ i.ker.toModulesι ▷ L.tensorPow n ≫ (λ_ _).hom)) := by
  let U : X.Opens := i.ker.support.compl
  have : IsIso ((restrictFunctor U.ι).map i.ker.toModulesι) :=
    i.ker.isIso_restrictFunctor_map_toModulesι (U := U) fun _ h ↦ h
  have := isIso_restrictFunctor_map_whiskerRight i.ker.toModulesι
    (L.tensorPow n) (U := U)
  have : Epi σ.π := σ.epi
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem epi_pullback_of_epi_restrict {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N)
    [Epi ((restrictFunctor j).map f)] : Epi ((Scheme.Modules.pullback j).map f) := by
  let e := restrictFunctorIsoPullback j
  have h : (restrictFunctor j).map f ≫ e.hom.app N =
      e.hom.app M ≫ (Scheme.Modules.pullback j).map f := e.hom.naturality f
  exact epi_of_epi_fac h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kernel_basis_generates (k : Type u) [Field k]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] (i : Z ⟶ X)
    [IsClosedImmersion i] (L : X.Modules) [L.IsInvertible] (n : ℕ)
    (σ : SheafOfModules.GeneratingSections (i.ker.toModules ⊗ₘ L.tensorPow n)) :
    letI : Module k Γ(L.tensorPow n, ⊤) :=
      Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
    ∀ (I : Type u) [Finite I] (b : Module.Basis I k (vanishingSubmodule k i (L.tensorPow n))),
      Epi ((Scheme.Modules.pullback
        (show X.Opens from i.ker.support.compl).ι).map
          ((L.tensorPow n).freeHomEquiv.symm
            (fun j ↦ sectionOfTop (L.tensorPow n) (b j).val))) := by
  classical
  let : Module k Γ(L.tensorPow n, ⊤) :=
    Module.compHom _ (Scheme.globalSectionsRingHom (X := X) k)
  intro I _ b
  let M := L.tensorPow n
  let U : X.Opens := i.ker.support.compl
  let μ : i.ker.toModules ⊗ₘ M ⟶ M := i.ker.toModulesι ▷ M ≫ (λ_ M).hom
  let f := σ.π ≫ μ
  have hf (a : σ.I) : (M.freeHomEquiv f a).val (op ⊤) ∈ vanishingSubmodule k i M := by
    change pullbackΓ i M (Hom.app (SheafOfModules.ιFree a ≫ f) ⊤ (1 : Γ(X, ⊤))) = 0
    apply (vanishing_range i L n _).mpr
    exact ⟨Hom.app (SheafOfModules.ιFree a ≫ σ.π) ⊤ (1 : Γ(X, ⊤)), rfl⟩
  obtain ⟨q, hq⟩ := factors_basis k M (vanishingSubmodule k i M) I b σ.I f hf
  have : Epi ((restrictFunctor U.ι).map f) := ideal_twist_generates i L n σ
  have : Epi ((Scheme.Modules.pullback U.ι).map f) := epi_pullback_of_epi_restrict U.ι f
  have hfac : (Scheme.Modules.pullback U.ι).map q ≫
      (Scheme.Modules.pullback U.ι).map
        (M.freeHomEquiv.symm (fun j ↦ sectionOfTop M (b j).val)) =
      (Scheme.Modules.pullback U.ι).map f := by
    rw [← Functor.map_comp, hq]
  exact epi_of_epi_fac hfac

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/--
For a proper scheme over a field and an ample invertible module, sections vanishing on a
closed subscheme eventually generate on its complement and define an immersion into projective
space. The kernel is represented as a `k`-submodule, and a finite basis of it supplies the
homogeneous coordinates.

Source: Stacks Project, varieties.tex, Tag 0FD5, lemma-generate-over-complement
(blueprint: lem-zl-bertini-sections).

Proof: Let `U` be the open complement of the closed subscheme. Coherence of its ideal sheaf and
Serre's global-generation theorem identify the kernel of restriction with sections generating the
restriction of the tensor powers to `U`. Finite-dimensionality of global sections supplies a
finite basis. The morphism classified by the restricted basis sections is an immersion on each
standard affine chart, by the projective embedding argument of Tag 0FD5; the charts cover `U`,
so the morphism is an immersion.
-/
theorem exists_eventual_immersion_vanishingSections
    (k : Type u) [Field k] {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))]
    [IsProper (Y ↘ Spec (.of k))]
    (L : Y.Modules) [L.IsInvertible]
    (hL : IsAmple (Y ↘ Spec (.of k)) L)
    {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    ∃ (n₀ : ℕ) (U : Y.Opens),
      (∀ y : Y, y ∈ U ↔ y ∉ Set.range i.base) ∧
      ∀ (n : ℕ), n₀ ≤ n →
        letI : Module k Γ(L.tensorPow n, ⊤) :=
          Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (Y ↘ Spec (CommRingCat.of k)).appTop).hom
        ∃ (V : Submodule k Γ(L.tensorPow n, ⊤))
          (I : Type u) (_hI : Finite I) (s : I → (L.tensorPow n).sections)
          (t : I → ((Scheme.Modules.pullback U.ι).obj (L.tensorPow n)).sections),
          (∀ v : Γ(L.tensorPow n, ⊤),
            v ∈ V ↔ (AlgebraicGeometry.pullbackΓ i (L.tensorPow n)) v = 0) ∧
          Submodule.span k (Set.range (fun j : I ↦
            (s j).val (Opposite.op ⊤)) : Set Γ(L.tensorPow n, ⊤)) = V ∧
          LinearIndependent (M := Γ(L.tensorPow n, ⊤)) k
            (fun j : I ↦ (s j).val (Opposite.op ⊤)) ∧
          (∀ j : I, (t j).val (Opposite.op ⊤) =
            (AlgebraicGeometry.pullbackΓ U.ι (L.tensorPow n))
              ((s j).val (Opposite.op ⊤))) ∧
          ∃ (ht : Epi ((SheafOfModules.freeHomEquiv
            ((Scheme.Modules.pullback U.ι).obj (L.tensorPow n))).symm t)),
            IsImmersion (@ProjectiveSpace.homOfGeneratingSections I _ U.toScheme
              (Spec (.of k)) (U.ι ≫ (Y ↘ Spec (.of k)))
              ((Scheme.Modules.pullback U.ι).obj (L.tensorPow n)) inferInstance t ht)
    := by
  classical
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have := isQuasicoherent_toModules i.ker
  have := isFinitePresentation_toModules i.ker
  obtain ⟨a, ha⟩ := exists_generatingSections_tensorObj_tensorPow
    (Y ↘ Spec (.of k)) hL i.ker.toModules
  obtain ⟨r, hr, hvery⟩ := hL.2
  let U : Y.Opens := i.ker.support.compl
  refine ⟨a + r, U, ?_, ?_⟩
  · intro y
    change y ∉ (i.ker.support : Set Y) ↔ y ∉ Set.range i.base
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  intro n hn
  let M := L.tensorPow n
  let : Module k Γ(M, ⊤) :=
    Module.compHom _ (Scheme.globalSectionsRingHom (X := Y) k)
  have : FiniteDimensional k Γ(M, ⊤) := finite_sections k M
  let V := vanishingSubmodule k i M
  let I := Module.Free.ChooseBasisIndex k V
  let b : Module.Basis I k V := Module.Free.chooseBasis k V
  have : Finite I := inferInstance
  let s : I → M.sections := fun j ↦ sectionOfTop M (b j).val
  let f : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ M := M.freeHomEquiv.symm s
  let t : I → ((Scheme.Modules.pullback U.ι).obj M).sections :=
    ((Scheme.Modules.pullback U.ι).obj M).freeHomEquiv
      ((pullbackFreeIso U.ι I).inv ≫ (Scheme.Modules.pullback U.ι).map f)
  obtain ⟨σ⟩ := ha n (by omega)
  have : Epi ((Scheme.Modules.pullback U.ι).map f) :=
    kernel_basis_generates k i L n σ I b
  have ht : Epi (((Scheme.Modules.pullback U.ι).obj M).freeHomEquiv.symm t) := by
    dsimp only [t]
    rw [Equiv.symm_apply_apply]
    infer_instance
  refine ⟨V, I, inferInstance, s, t, ?_, ?_, ?_, ?_, ht, ?_⟩
  · intro v
    rfl
  · change Submodule.span k (Set.range (fun j : I ↦
        (sectionOfTop M (b j).val).val (op ⊤)) : Set Γ(M, ⊤)) = V
    simp only [sectionOfTop_eval]
    rw [show (fun j ↦ (b j).val) = V.subtype ∘ b from rfl,
      Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  · have hb := b.linearIndependent.map' V.subtype
      (LinearMap.ker_eq_bot.mpr V.injective_subtype)
    convert hb using 1
    · funext j
      exact sectionOfTop_eval M (b j).val
    all_goals rfl
  · intro j
    exact pullback_free_eval U.ι M s j
  · obtain ⟨τ⟩ := ha (n - r) (by omega)
    apply vanishing_linear_system_isImmersion k i L n r (by omega) hvery τ I s t
    · intro v hv
      change v ∈ Submodule.span k (Set.range (fun j ↦
        (sectionOfTop M (b j).val).val (op ⊤)) : Set Γ(M, ⊤))
      simp only [sectionOfTop_eval]
      rw [show (fun j ↦ (b j).val) = V.subtype ∘ b from rfl,
        Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
      exact hv
    · intro j
      exact pullback_free_eval U.ι M s j

end AlgebraicGeometry
