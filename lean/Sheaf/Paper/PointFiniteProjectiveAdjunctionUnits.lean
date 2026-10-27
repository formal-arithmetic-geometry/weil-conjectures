/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.PointDerivedHomModels
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The actual adjunction unit on finite-projective point modules

Source: blueprint point comparison, third paragraph, and Stacks Tag 00NX.
(blueprint: lem-pod-point-finite-projective-adjunction-units).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace WeilConjectures.PointDerivedHom

variable (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)
  (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
  (hobj : ∀ M : ModuleCat.{max u (t + 1)} R, L.obj M = extensionObject k B α M)
  (adj : L ⊣ sections k B α)

private def regularHom : L.obj (ModuleCat.of R R) ⟶ SheafOfModules.unit (ring k B) :=
  (adj.homEquiv _ _).symm (coefficientSections k B α)

private theorem unitHom_final_bijective
    (V : Modules.{t, u} k B) :
    Function.Bijective (fun f : SheafOfModules.unit (ring.{t, u} k B) ⟶ V ↦
      f.val.app (op (finalObject k)) (1 : B.obj.obj (op (finalObject k)))) := by
  constructor
  · intro f g h
    apply V.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    have hf := (V.unitHomEquiv f).property (toFinal k U.unop).op
    have hg := (V.unitHomEquiv g).property (toFinal k U.unop).op
    exact hf.symm.trans ((congrArg (V.val.map (toFinal k U.unop).op) h).trans hg)
  · intro x
    let t : V.sections := PresheafOfModules.sectionsMk
      (fun U ↦ V.val.map (toFinal k U.unop).op x) (by
        intro U W i
        change V.val.presheaf.map i
          (V.val.presheaf.map (toFinal k U.unop).op x) =
            V.val.presheaf.map (toFinal k W.unop).op x
        have hw : (toFinal k U.unop).op ≫ i = (toFinal k W.unop).op := by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          change i.unop.left ≫ (unop U).hom = (unop W).hom
          exact MorphismProperty.Over.w i.unop
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hw])
    refine ⟨V.unitHomEquiv.symm t, ?_⟩
    have ht := congrArg (fun z : V.sections ↦ z.val (op (finalObject k)))
      (V.unitHomEquiv.apply_symm_apply t)
    have hid : toFinal k (finalObject k) = 𝟙 _ := by
      apply MorphismProperty.Over.Hom.ext
      rfl
    change ((V.unitHomEquiv.symm t).val.app (op (finalObject k)))
      (1 : B.obj.obj (op (finalObject k))) = x
    change ((V.unitHomEquiv.symm t).val.app (op (finalObject k)))
      (1 : B.obj.obj (op (finalObject k))) =
        V.val.map (toFinal k (finalObject k)).op x at ht
    change ((V.unitHomEquiv.symm t).val.app (op (finalObject k)))
      (1 : B.obj.obj (op (finalObject k))) =
        V.val.presheaf.map (toFinal k (finalObject k)).op x at ht
    rw [hid, op_id] at ht
    exact ht.trans (congrArg (fun f ↦ f x) (V.val.presheaf.map_id _))

set_option linter.checkUnivs false in
private theorem moduleHom_one_bijective
    (M : ModuleCat.{max u (t + 1)} R) :
    Function.Bijective (fun f : ModuleCat.of R R ⟶ M ↦ f.hom 1) := by
  constructor
  · intro f g h
    apply ModuleCat.hom_ext
    exact (LinearMap.ringLmapEquivSelf R R M).injective h
  · intro x
    exact ⟨ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R R M).symm x), by simp⟩

private theorem adjunction_rankOne_iso
    : IsIso (regularHom k B α L adj) := by
  let f := coefficientSections.{t, u} k B α
  let h := (adj.homEquiv (ModuleCat.of R R) _).symm f
  have hh : IsIso h := by
    apply isIso_of_coyoneda_map_bijective
    intro V
    let ev := fun g : ModuleCat.of R R ⟶ (sections.{t, u} k B α).obj V ↦ g.hom 1
    have he (t : SheafOfModules.unit (ring.{t, u} k B) ⟶ V) :
        ev (adj.homEquiv _ V (h ≫ t)) =
          t.val.app (op (finalObject k)) (1 : B.obj.obj (op (finalObject k))) := by
      rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
      change t.val.app (op (finalObject k))
        (scalar.{t, u} k B α (op (finalObject k)) 1) = _
      rw [map_one]
    constructor
    · intro t t' htt
      apply (unitHom_final_bijective k B V).1
      exact (he t).symm.trans
        ((congrArg (fun q ↦ ev (adj.homEquiv _ V q)) htt).trans (he t'))
    · intro q
      obtain ⟨t, ht⟩ := (unitHom_final_bijective k B V).2 (ev (adj.homEquiv _ V q))
      refine ⟨t, (adj.homEquiv _ V).injective ?_⟩
      apply (moduleHom_one_bijective.{t, u} (R := R) ((sections.{t, u} k B α).obj V)).1
      exact (he t).trans ht
  exact hh

private lemma regularHom_unit (r : R) :
    (regularHom k B α L adj).val.app (op (finalObject k))
      ((adj.unit.app (ModuleCat.of R R)).hom r) = scalar k B α (op (finalObject k)) r := by
  have h := (adj.homEquiv _ _).apply_symm_apply (coefficientSections k B α)
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun f ↦ f.hom r) h

private def regularIso : L.obj (ModuleCat.of R R) ≅ SheafOfModules.unit (ring k B) :=
  letI := adjunction_rankOne_iso k B α L adj
  asIso (regularHom k B α L adj)

private lemma regularIso_hom : (regularIso k B α L adj).hom = regularHom k B α L adj :=
  rfl

private theorem unit_regular_isIso
    (hscalar : Function.Bijective (scalar k B α (op (finalObject k)))) :
    IsIso (adj.unit.app (ModuleCat.of R R)) := by
  have h : IsIso (coefficientSections k B α) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hscalar
  have he : adj.unit.app (ModuleCat.of R R) ≫
      (sections k B α).map (regularIso k B α L adj).hom = coefficientSections k B α :=
    (adj.homEquiv _ _).apply_symm_apply _
  have : IsIso (adj.unit.app (ModuleCat.of R R) ≫
      (sections k B α).map (regularIso k B α L adj).hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((sections k B α).map (regularIso k B α L adj).hom)

private theorem unit_power_isIso
    [PreservesFiniteLimits L]
    [PreservesFiniteLimits (sections k B α)]
    [PreservesFiniteColimits L] [PreservesFiniteColimits (sections k B α)]
    (hscalar : Function.Bijective (scalar k B α (op (finalObject k)))) (n : ℕ) :
    IsIso (adj.unit.app (ModuleCat.of R (Fin n → R))) := by
  let F := L ⋙ sections k B α
  let V := fun _ : Fin n ↦ ModuleCat.of R R
  have h := unit_regular_isIso k B α L adj hscalar
  have : ∀ j : Discrete (Fin n),
      IsIso ((Functor.whiskerLeft (Discrete.functor V) adj.unit).app j) := fun _ ↦ h
  have : IsIso (Functor.whiskerLeft (Discrete.functor V) adj.unit) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (adj.unit.app (⨁ V)) :=
    isIso_app_coconePt_of_preservesColimit (Discrete.functor V) adj.unit
      (biproduct.bicone V).toCocone (biproduct.isColimit V)
  exact IsIso.of_isIso_fac_left
    (adj.unit.naturality (ModuleCat.biproductIsoPi V).hom)

private theorem unit_projective_isIso
    [PreservesFiniteLimits L]
    [PreservesFiniteLimits (sections k B α)]
    [PreservesFiniteColimits L] [PreservesFiniteColimits (sections k B α)]
    (hscalar : Function.Bijective (scalar k B α (op (finalObject k))))
    (M : ModuleCat.{max u (t + 1)} R) [Module.Finite R M] [Module.Projective R M] :
    IsIso (adj.unit.app M) := by
  obtain ⟨n, p, i, _, _, hip⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let s : M ⟶ ModuleCat.of R (Fin n → R) := ModuleCat.ofHom i
  let r : ModuleCat.of R (Fin n → R) ⟶ M := ModuleCat.ofHom p
  have hsr : s ≫ r = 𝟙 M := ModuleCat.hom_ext hip
  have := unit_power_isIso k B α L adj hscalar n
  refine ⟨(L ⋙ sections k B α).map s ≫ inv (adj.unit.app _) ≫ r, ?_, ?_⟩
  · rw [← Category.assoc, ← adj.unit.naturality, Category.assoc,
      IsIso.hom_inv_id_assoc]
    exact hsr
  · simp only [Category.assoc]
    have hr : r ≫ adj.unit.app M = adj.unit.app _ ≫
        (L ⋙ sections k B α).map r := adj.unit.naturality r
    rw [hr, ← Category.assoc (inv _) _,
      IsIso.inv_hom_id, Category.id_comp, ← Functor.map_comp, hsr]
    exact (L ⋙ sections k B α).map_id M

/-- The actual unit is invertible on every finite projective module, and its
rank-one comparison with B is normalized by multiplication of local scalars.
Source: blueprint point comparison, third paragraph; Stacks Tag 00NX
(blueprint: lem-pod-point-finite-projective-adjunction-units).

Proof: the adjunction sends the scalar section map to the rank-one comparison.
Its inverse is the B-linear map taking one to the global section determined by
eta_R(1); restriction from the final object defines that section. Adjunction
injectivity and linearity show the first inverse identity, and evaluation at one
shows the second. Bijectivity of the scalar map therefore makes eta_R invertible.
Finite-coproduct preservation gives the assertion for finite powers, including the
empty power. Every finite projective module is a retract of one of these powers;
naturality of eta transports the inverse along the splitting. Finally the explicit
adjunction formulas give the claimed generator and unit normalizations. -/
theorem point_finiteProjective_adjunction_units
    [PreservesFiniteLimits L] [PreservesFiniteLimits (sections k B α)]
    [PreservesFiniteColimits L] [PreservesFiniteColimits (sections k B α)]
    (hex : ExplicitAdjunction k B α L hobj adj)
    (hscalar : Function.Bijective (scalar k B α (op (finalObject k)))) :
    (∀ (M : ModuleCat.{max u (t + 1)} R)
      [Module.Finite R M] [Module.Projective R M], IsIso (adj.unit.app M)) ∧
    (∀ (M : ModuleCat.{max u (t + 1)} R) (x : M),
      (adj.unit.app M).hom x = generator k B α L hobj M (op (finalObject k)) 1 x) ∧
    ∃ κ : L.obj (ModuleCat.of R R) ≅ SheafOfModules.unit (ring k B),
      (∀ (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (b : B.obj.obj U) (r : R),
        κ.hom.val.app U (generator k B α L hobj (ModuleCat.of R R) U b r) =
          b * scalar k B α U r) ∧
      ∀ r : R, κ.hom.val.app (op (finalObject k))
        ((adj.unit.app (ModuleCat.of R R)).hom r) =
          scalar k B α (op (finalObject k)) r := by
  refine ⟨fun M _ _ ↦ unit_projective_isIso k B α L adj hscalar M, ?_,
    regularIso k B α L adj, ?_, regularHom_unit k B α L adj⟩
  · intro M x
    have h := hex.1 M (L.obj M) (𝟙 _) x
    rw [adj.homEquiv_id] at h
    exact h
  · intro U b r
    have h := hex.2 (ModuleCat.of R R) (SheafOfModules.unit (ring k B))
      (coefficientSections k B α) U b r
    change (regularHom k B α L adj).val.app U
      (generator k B α L hobj (ModuleCat.of R R) U b r) = _
    dsimp only [regularHom]
    calc
      _ = b • (SheafOfModules.unit (ring k B)).val.map (toFinal k U.unop).op
          ((coefficientSections k B α).hom r) := h
      _ = _ := ?_
    change b * (B.obj.map (toFinal k U.unop).op).hom
      (scalar k B α (op (finalObject k)) r) = _
    congr 1
    exact (NatTrans.naturality_apply
      ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
        ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj R)) ≫ α.hom)
      (toFinal k U.unop).op r).symm

end WeilConjectures.PointDerivedHom
