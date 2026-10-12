/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Sheaf.AlgebraicGeometry.ArtinSchreierKernelSections
import Mathlib.Algebra.Field.ULift

/-!
# The kernel of a specified Artin--Schreier morphism

Source: Stacks Project, Tag 0A3J, opening exact sequence.
(blueprint: lem-sc-artin-schreier-section-kernel)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The specified constant-sheaf map is a kernel of Frobenius minus identity.
Source: Stacks Project, Tag 0A3J, exactness at the constant sheaf and the function sheaf.
(blueprint: lem-sc-artin-schreier-section-kernel)

Proof: If X is nonempty, a germ of its global functions gives nontriviality of
Γ(X, ⊤). The characteristic hypothesis therefore defines the prime-field ring map.
Compose X → Spec Γ(X, ⊤) with this map to make X a scheme over ULift (ZMod p).
Apply `artinSchreier_kernel_sections`: iota is injective on every section group,
and every section fixed by Frobenius has a preimage. For an arrow g killed by wp,
the formula hwp says each g(x) is fixed by Frobenius. Choose its unique preimage.
Injectivity proves that these choices preserve zero and addition and commute with
restriction. They form a sheaf morphism lifting g. Sectionwise injectivity also
proves that iota is monic, so the kernel fork satisfies its universal property.
If X is empty, every etale sheaf is zero. Thus wp is monic and the source of iota
is zero, which also makes its fork limiting. No surjectivity of wp is used. -/
theorem artinSchreier_section_data_isKernel (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G) (iota : X.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0)
    (hrestr : ∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hwp : ∀ (U : X.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x)
    (hiota : ∀ (U : X.Etaleᵒᵖ) (c : ZMod p),
      a U (iota.hom.app U
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤))) :
    Nonempty (Limits.IsLimit (Limits.KernelFork.ofι iota hzero)) := by
  classical
  by_cases hX : Nonempty X
  · let _ := hX
    obtain ⟨z⟩ := hX
    have : Nontrivial Γ(X, ⊤) :=
      (X.presheaf.germ ⊤ z (by trivial)).hom.domain_nontrivial
    have : CharP Γ(X, ⊤) p :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    let k := ULift.{u} (ZMod p)
    let _ : Field k := inferInstanceAs (Field (ULift.{u} (ZMod p)))
    let f : X ⟶ Spec (.of k) := X.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom
        ((ZMod.castHom (dvd_refl p) Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom))
    have hsec := AlgebraicGeometry.artinSchreier_kernel_sections f p
      (Fact.out : p.Prime) G a iota hrestr hiota
    have hlift : ∀ {W : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
        (g : W ⟶ G) (_ : g ≫ wp = 0), ∃ l : W ⟶ X.constantZMod p, l ≫ iota = g := by
      intro W g hg
      have he (U : X.Etaleᵒᵖ) (x : W.obj.obj U) :
          ∃ y, iota.hom.app U y = g.hom.app U x := by
        apply (hsec U).2
        apply sub_eq_zero.mp
        rw [← hwp]
        have hh := congrArg (fun m : W ⟶ G => m.hom.app U x) hg
        simpa using congrArg (a U) hh
      let lapp (U : X.Etaleᵒᵖ) : W.obj.obj U →+ (X.constantZMod p).obj.obj U :=
        { toFun := fun x => (he U x).choose
          map_zero' := by
            apply (hsec U).1
            rw [(he U 0).choose_spec, map_zero, map_zero]
          map_add' := by
            intro x y
            apply (hsec U).1
            rw [(he U (x + y)).choose_spec, map_add, map_add,
              (he U x).choose_spec, (he U y).choose_spec] }
      let l : W ⟶ X.constantZMod p :=
        ⟨{ app := fun U => AddCommGrpCat.ofHom (lapp U)
           naturality := by
             intro U V t
             ext x
             apply (hsec V).1
             change iota.hom.app V (lapp V (W.obj.map t x)) =
               iota.hom.app V ((X.constantZMod p).obj.map t (lapp U x))
             dsimp only [lapp, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
             rw [(he V _).choose_spec, iota.hom.naturality_apply,
               (he U x).choose_spec, g.hom.naturality_apply] }⟩
      refine ⟨l, ?_⟩
      ext U x
      exact (he U x).choose_spec
    have : Mono iota := by
      constructor
      intro W g h hgh
      ext U x
      apply (hsec U).1
      exact congrArg (fun m : W ⟶ G => m.hom.app U x) hgh
    refine ⟨Limits.KernelFork.IsLimit.ofι' iota hzero ?_⟩
    intro W g hg
    exact ⟨(hlift g hg).choose, (hlift g hg).choose_spec⟩
  · have : IsEmpty X := not_nonempty_iff.mp hX
    have hz := Etale.isZero_sheaf_of_isEmpty (X.constantZMod p)
    have : Mono wp := by
      constructor
      intro W f g h
      exact (Etale.isZero_sheaf_of_isEmpty G).eq_of_tgt f g
    exact ⟨Limits.KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance hz⟩
end AlgebraicGeometry.Scheme
