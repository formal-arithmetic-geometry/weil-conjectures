/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import WeilConjectures.AlgebraicGeometry.FieldEquivariantGermFamilySection
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-! Fullness of the canonical Galois stalk functor.
Source: Stacks Project, Tags 03QT and 04JM (blueprint: lem-exc-galois-stalk-action-full).
-/

@[expose] public section

attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

private theorem field_section_germ_ext (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v)))
    (U : (Spec (.of K)).Etale) (a b : F.obj.obj (op U))
    (h : ∀ x : (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj U,
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        U x F.obj a =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        U x F.obj b) : a = b := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let p := pointSmallEtale s
  let R := Presheaf.equalizerSieve (F := F.obj) (X := op U) a b
  have hR : R ∈ (Spec (.of K)).smallEtaleTopology U := by
    obtain ⟨ι, Y, f, hf⟩ := R.exists_eq_ofArrows
    rw [hf, ofArrows_mem_smallEtaleTopology_iff]
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    have : AlgebraicGeometry.Etale U.hom := U.prop
    obtain ⟨l, hl, hy⟩ := exists_fac_of_etale_of_isSepClosed U.hom s y
      (Subsingleton.elim (α := Spec (.of K)) _ _)
    let x : p.fiber.obj U := Over.homMk l hl
    obtain ⟨Z, g, t, ht, he⟩ := (p.toPresheafFiber_eq_iff' _ _ _ _).mp (h x)
    have hg : R g := he
    rw [hf] at hg
    obtain ⟨W, c, d, ⟨i⟩, hcd⟩ := hg
    refine ⟨i, c.left (t.left (default : Spec (.of Ω))), ?_⟩
    have hfac : g.left = c.left ≫ (f i).left := by
      exact congrArg (fun q ↦ q.left) hcd.symm
    have ht' : t.left ≫ g.left = x.left := congrArg (fun q ↦ q.left) ht
    rw [hfac] at ht'
    have := congrArg (fun q : Spec (.of Ω) ⟶ U.left ↦ q default) ht'
    change (f i).left (c.left (t.left (default : Spec (.of Ω)))) = l default at this
    exact this.trans hy
  exact Sheaf.isSeparated F U R hR _ _ (fun Y f hf ↦ hf)

-- Preserve the original named proof binders in the canonical-formula hypothesis.
set_option linter.unusedVariables false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tags 03QT and 04JM.
(blueprint: lem-exc-galois-stalk-action-full).

Proof: Let A be the subfield of Omega algebraic over K. It is algebraically closed and every
pointed etale neighbourhood factors uniquely through Spec A by finite separability of its
residue field. The resulting natural identifications of germs transport the invariant-section
bijections to Omega. The canonical germ formula identifies the action transported by j with this
action: extend each automorphism of Ks to A, then to Omega by fixing a transcendence
basis and extending across the remaining algebraic extension. Every germ has a representative,
so the formula determines the transported action. Over every finite separable intermediate
field, an equivariant map restricts to a map of invariant sets, hence to a map of sections.
Embedding compatibility makes these maps natural.
Every etale scheme is a disjoint union of finite separable components; the sheaf condition
extends these maps uniquely to the product of their section sets. These section maps constitute
a sheaf morphism. Every germ has a representative on a component, so the stalk map is the
specified equivariant map. Naturality of j then identifies its T image with that map, giving
fullness. Empty schemes use the empty product. -/
theorem galoisStalkActionFunctor_full
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K); let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω)); let p := pointSmallEtale s
    let G := Gal(Ks/K); let V := ObjectProperty.ι (ContAction.IsDiscrete
      (V := Type (max u v)) (G := G)) ⋙ ObjectProperty.ι (Action.IsContinuous
      (V := Type (max u v)) (G := G))
    ∀ (T : Sheaf J (Type (max u v)) ⥤ DiscreteContAction (Type (max u v)) G)
      (j : T ⋙ V ⋙ Action.forget (Type (max u v)) G ≅ p.sheafFiber),
      (∀ (F : Sheaf J (Type (max u v))) (g : G) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((T.obj F).obj.obj.ρ g ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
          p.toPresheafFiber X x' F.obj z) → T.Full := by
  classical
  intro S J s p G V T j hj
  refine ⟨fun {F F'} a ↦ ?_⟩
  let q : p.sheafFiber.obj F → p.sheafFiber.obj F' :=
    fun m ↦ (j.hom.app F') (a.hom.hom.hom ((j.inv.app F) m))
  have local_section (X : (Spec (.of K)).Etale) (z : F.obj.obj (op X)) :
      ∃ z' : F'.obj.obj (op X), ∀ x : p.fiber.obj X,
        p.toPresheafFiber X x F'.obj z' = q (p.toPresheafFiber X x F.obj z) := by
    let liftFunctor := uliftFunctor.{u + 1, max u v}
    let H := (sheafCompose (Spec (.of K)).smallEtaleTopology liftFunctor).obj F'
    let e := ((p.presheafFiberCompIso liftFunctor).app F'.obj).toEquiv.trans Equiv.ulift
    have he (Y : (Spec (.of K)).Etale) (y : p.fiber.obj Y)
        (t : H.obj.obj (op Y)) :
        e (p.toPresheafFiber Y y H.obj t) =
          p.toPresheafFiber Y y F'.obj t.down :=
      congrArg ULift.down (ConcreteCategory.congr_hom
        (p.toPresheafFiber_presheafFiberCompIso_hom_app liftFunctor Y y F'.obj) t)
    let ρ (g : G) (m : p.sheafFiber.obj F') :=
      (j.hom.app F') ((T.obj F').obj.obj.ρ g ((j.inv.app F') m))
    let ρ' (g : G) (m : p.sheafFiber.obj H) := e.symm (ρ g (e m))
    have hρ' (g : G) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (t : H.obj.obj (op Y)) :
        ρ' g (p.toPresheafFiber Y y H.obj t) =
          p.toPresheafFiber Y y' H.obj t := by
      apply e.injective
      change e (e.symm (ρ g (e (p.toPresheafFiber Y y H.obj t)))) = _
      rw [e.apply_symm_apply, he, he]
      exact hj F' g τ hτ Y y y' hy t.down
    obtain ⟨t, ht⟩ := field_equivariant_germ_family_section K Ks Ω H ρ' hρ' X
      (fun x ↦ e.symm (q (p.toPresheafFiber X x F.obj z))) (by
        intro g τ hτ x x' hx
        change e.symm (q (p.toPresheafFiber X x' F.obj z)) =
          e.symm (ρ g (e (e.symm (q (p.toPresheafFiber X x F.obj z)))))
        rw [e.apply_symm_apply]
        apply congrArg e.symm
        dsimp [q, ρ]
        rw [← hj F g τ hτ X x x' hx z]
        simp only [← ConcreteCategory.comp_apply, j.hom_inv_id_app]
        have hc := ConcreteCategory.congr_hom (a.hom.hom.comm g) ((j.inv.app F)
          (p.toPresheafFiber X x F.obj z))
        exact congrArg (fun m ↦ (j.hom.app F') m) hc)
    refine ⟨t.down, fun x ↦ ?_⟩
    exact (he X x t).symm.trans ((congrArg e (ht x)).trans (e.apply_symm_apply _))
  have unique_section (X : (Spec (.of K)).Etale) (z : F.obj.obj (op X)) :
      ∃! z' : F'.obj.obj (op X), ∀ x : p.fiber.obj X,
        p.toPresheafFiber X x F'.obj z' = q (p.toPresheafFiber X x F.obj z) := by
    obtain ⟨z', hz'⟩ := local_section X z
    refine ⟨z', hz', fun z'' hz'' ↦ ?_⟩
    exact field_section_germ_ext K Ω F' X z'' z' (fun x ↦ (hz'' x).trans (hz' x).symm)
  choose b hb using fun X z ↦ (unique_section X z).exists
  let φ : F ⟶ F' := ⟨{
    app := fun X ↦ ↾(b X.unop)
    naturality := by
      intro X Y f
      ext z
      apply field_section_germ_ext K Ω F' Y.unop
      intro y
      change p.toPresheafFiber Y.unop y F'.obj (b Y.unop (F.obj.map f z)) =
        p.toPresheafFiber Y.unop y F'.obj (F'.obj.map f (b X.unop z))
      rw [hb]
      have h₁ := p.toPresheafFiber_w_apply f.unop y F.obj z
      have h₂ := p.toPresheafFiber_w_apply f.unop y F'.obj (b X.unop z)
      exact (congrArg q h₁).trans ((hb X.unop z (p.fiber.map f.unop y)).symm.trans
        h₂.symm)
  }⟩
  refine ⟨φ, ?_⟩
  apply (V ⋙ Action.forget (Type (max u v)) G).map_injective
  have hp : p.sheafFiber.map φ = ↾q := by
    apply p.presheafFiber_hom_ext
    intro X x
    ext z
    change p.presheafFiber.map φ.hom (p.toPresheafFiber X x F.obj z) =
      q (p.toPresheafFiber X x F.obj z)
    exact (p.toPresheafFiber_naturality_apply φ.hom X x z).trans (hb X z x)
  ext m
  have hn := ConcreteCategory.congr_hom (j.hom.naturality φ) m
  change (j.hom.app F') ((T.map φ).hom.hom.hom m) =
    p.sheafFiber.map φ ((j.hom.app F) m) at hn
  rw [hp] at hn
  dsimp [q] at hn
  simp only [← ConcreteCategory.comp_apply, j.hom_inv_id_app] at hn
  exact (injective_of_mono (j.hom.app F')) hn

end AlgebraicGeometry.Scheme
