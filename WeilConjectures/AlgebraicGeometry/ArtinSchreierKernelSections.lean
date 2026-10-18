/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.RingTheory.LocalRing.ArtinSchreierKernel
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Sections of the Artin–Schreier kernel

Source: blueprint `sec-curve-estimates/sk-prop-h2/lem-sc-as-sequence.md`,
first sentence of the proof: the kernel is the constant prime-field sheaf.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- Local preimages of an injective sheaf map glue uniquely, and their image is the
original section by separatedness of the target sheaf. -/
private theorem lift_of_imageSieve_mem
    {D : Type*} [Category D] (J : GrothendieckTopology D)
    {F G : Sheaf J (Type u)} (φ : F ⟶ G)
    (hinj : ∀ U, Function.Injective (φ.hom.app U))
    {U : Dᵒᵖ} (x : G.obj.obj U) (hx : Presheaf.imageSieve φ.hom x ∈ J U.unop) :
    ∃ y, φ.hom.app U y = x := by
  classical
  let t := Presieve.FamilyOfElements.localPreimage φ.hom x
  have ht : (t.map φ.hom).IsAmalgamation x :=
    Presieve.FamilyOfElements.isAmalgamation_map_localPreimage φ.hom x
  have hc : t.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ heq
    apply hinj (.op Z)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    change G.obj.map g₁.op ((t.map φ.hom) f₁ h₁) =
      G.obj.map g₂.op ((t.map φ.hom) f₂ h₂)
    rw [← ht f₁ h₁, ← ht f₂ h₂, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, heq]
  have hF := (isSheaf_iff_isSheaf_of_type J F.obj).mp F.property
  have hG := (isSheaf_iff_isSheaf_of_type J G.obj).mp G.property
  let y := (hF _ hx).amalgamate t hc
  refine ⟨y, ?_⟩
  exact (hG _ hx).isSeparatedFor (t.map φ.hom) _ x
    (((hF _ hx).isAmalgamation hc).map φ.hom) ht

/-- The constant-sheaf inclusion is injective on sections and every section satisfying
`a ^ p = a` is in its image. This allows locally varying prime-field constants; it does
not assert that a root over a disconnected scheme is a single constant.
Source: blueprint `lem-sc-as-sequence`, first sentence of its proof; Stacks Tag 0A3J.
(blueprint: lem-sc-as-kernel-sections)

Proof:
1. The structural map to `Spec k` makes `p` vanish in each section ring and in every
   local ring of every etale object. At each underlying point the local-ring theorem
   `IsLocalRing.pow_eq_self_iff_existsUnique_zmod` identifies a root with a unique
   prime-field constant. Equality of germs gives equality with that constant on an
   open neighborhood. These neighborhoods are also etale objects over the base.
2. Sections of the constant sheaf are locally images of constants under the
   sheafification unit. If two sections have the same image under `iota`, refine their
   two covering sieves to a common cover where both are constants. At every point of
   this cover their constants agree, by the uniqueness part of the local-ring theorem
   and `hiota`. Further restrict to the open neighborhoods from step 1. Thus the two
   constant-sheaf sections agree locally, and sheaf separatedness makes them equal.
   On an empty object both sheaves have their unique section. This proves injectivity.
3. For a root `x`, use the open cover from step 1. On each member take the image under
   the sheafification unit of its prime-field constant. The formulas `hrestr` and
   `hiota` identify its image under `iota` with the restriction of `x`. On overlaps
   these sections agree by step 2. The sheaf condition glues them to a section `y`,
   and separatedness in the target shows `iota(y) = x`. The empty covering gives the
   same conclusion for the empty object. -/
theorem artinSchreier_kernel_sections
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    (p : ℕ) [CharP k p] (hp : p.Prime)
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (iota : C.constantZMod p ⟶ G)
    (hrestr : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hiota : ∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
      a U (iota.hom.app U
        ((toSheafify C.smallEtaleTopology
          ((Functor.const C.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤))) :
    ∀ U : C.Etaleᵒᵖ, Function.Injective (iota.hom.app U) ∧
      ∀ x : G.obj.obj U, (a U x) ^ p = a U x → ∃ y, iota.hom.app U y = x := by
  have hconstants : Presheaf.IsLocallyInjective C.smallEtaleTopology
      (toSheafify C.smallEtaleTopology
        ((Functor.const C.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))) ≫ iota.hom) := by
    classical
    let _ : Fact p.Prime := ⟨hp⟩
    let η := toSheafify C.smallEtaleTopology
      ((Functor.const C.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))
    constructor
    intro U x y h
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    by_cases hU : Nonempty U.unop.left
    · let _ := hU
      obtain ⟨z⟩ := hU
      let _ : Nontrivial Γ(U.unop.left, ⊤) :=
        (U.unop.left.presheaf.germ ⊤ z (by trivial)).hom.domain_nontrivial
      let ρ : k →+* Γ(U.unop.left, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ U.unop.hom.appTop).hom
      have hchar : (p : Γ(U.unop.left, ⊤)) = 0 := by
        rw [← map_natCast ρ, CharP.cast_eq_zero k p, map_zero]
      let _ : CharP Γ(U.unop.left, ⊤) p :=
        (CharP.charP_iff_prime_eq_zero hp).mpr hchar
      have he : ULift.up x = (ULift.up y : ULift.{u + 1} (ZMod p)) := by
        apply ULift.ext
        apply ZMod.castHom_injective Γ(U.unop.left, ⊤)
        have he := congrArg (a U) h
        change a U (iota.hom.app U (η.app U (ULift.up x))) =
          a U (iota.hom.app U (η.app U (ULift.up y))) at he
        rw [hiota U x, hiota U y] at he
        simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using he
      have hxy : x = y := congrArg ULift.down he
      subst y
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact C.smallEtaleTopology.top_mem _
    · let _ : IsEmpty U.unop.left := not_nonempty_iff.mp hU
      exact C.smallEtaleTopology.superset_covering bot_le
        (Scheme.Etale.bot_mem_smallEtaleTopology U.unop)
  let _ := hconstants
  let η := toSheafify C.smallEtaleTopology
    ((Functor.const C.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))
  have hlocal : Sheaf.IsLocallyInjective iota :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
      C.smallEtaleTopology η iota.hom
  have hinj := (Sheaf.isLocallyInjective_iff_injective iota).mp hlocal
  intro U
  refine ⟨hinj U, ?_⟩
  intro x hx
  let φ := (sheafCompose C.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map iota
  have hs : Presheaf.imageSieve iota.hom x ∈ C.smallEtaleTopology U.unop := by
    classical
    let _ : NeZero p := ⟨hp.ne_zero⟩
    apply (Scheme.mem_smallEtaleTopology_iff _).mpr
    intro z
    let γ := (U.unop.left.presheaf.germ ⊤ z (by trivial)).hom
    let ρ : k →+* Γ(U.unop.left, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ U.unop.hom.appTop).hom
    have hchar : (p : U.unop.left.presheaf.stalk z) = 0 := by
      rw [← map_natCast (γ.comp ρ), CharP.cast_eq_zero k p, map_zero]
    have hroot : γ (a U x) ^ p = γ (a U x) := by
      rw [← map_pow, hx]
    obtain ⟨c, hc, _⟩ :=
      (IsLocalRing.pow_eq_self_iff_existsUnique_zmod p hp hchar (γ (a U x))).mp hroot
    have hgerm : γ (a U x) = γ (c.val : Γ(U.unop.left, ⊤)) := by
      rw [map_natCast, ← ZMod.cast_eq_val]
      exact hc.symm
    obtain ⟨W, hzW, i₁, i₂, heq⟩ :=
      U.unop.left.presheaf.germ_eq z (by trivial) (by trivial) _ _ hgerm
    change U.unop.left.Opens at W
    let V : C.Etale := Scheme.Etale.mk (W.ι ≫ U.unop.hom)
    let g : V ⟶ U.unop := MorphismProperty.Over.homMk W.ι rfl
    refine ⟨V, g, ?_, ⟨⟨z, hzW⟩, rfl⟩⟩
    refine ⟨(toSheafify C.smallEtaleTopology
      ((Functor.const C.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app (.op V) (ULift.up c), ?_⟩
    apply (a (.op V)).injective
    rw [hiota, hrestr]
    change (c.val : Γ(W, ⊤)) = W.ι.appTop (a U x)
    have hres : W.ι.appTop (a U x) = W.ι.appTop (c.val : Γ(U.unop.left, ⊤)) := by
      apply (ConcreteCategory.bijective_of_isIso W.topIso.hom).injective
      rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
        ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp]
      convert heq using 1 <;> congr 1
    rw [hres, map_natCast]
  exact lift_of_imageSieve_mem C.smallEtaleTopology φ hinj x hs

end AlgebraicGeometry
