/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.ULift

/-!
# Abelian sheaves killed by n are sheaves of Z/n-modules

Source: literature/stacks-project/etale-cohomology.tex, Definition 03RW and
Theorem 03SC (blueprint: lem-weil-pbc-sheaves-killed-by-n-zmod-modules).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private lemma ring_map_int_smul {R : Type*} [Ring R]
    (n : ℕ) (f : ULift.{u + 1} (ZMod n) →+* R)
    {M : Type*} [AddCommGroup M] [Module R M] (a : ℤ) (s : M) :
    f (ULift.up (a : ZMod n)) • s = a • s := by
  change f (a : ULift.{u + 1} (ZMod n)) • s = a • s
  rw [map_intCast, Int.cast_smul_eq_zsmul]

private lemma constant_module_killed {R : Type*} [Ring R]
    (n : ℕ) (f : ULift.{u + 1} (ZMod n) →+* R)
    {M : Type*} [AddCommGroup M] [Module R M] (s : M) : n • s = 0 := by
  have h := ring_map_int_smul n f (n : ℤ) s
  have hz : ULift.up ((n : ℤ) : ZMod n) = (0 : ULift.{u + 1} (ZMod n)) := by
    apply ULift.ext
    simp
  rw [hz, map_zero, zero_smul] at h
  simpa using h.symm

set_option backward.isDefEq.respectTransparency false in
private lemma constant_restrict_linear {C : Type*} [Category C]
    (J : GrothendieckTopology C) (n : ℕ)
    (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod n))) ⟶ R.obj)
    (M N : SheafOfModules.{u + 1} R)
    (f : (SheafOfModules.toSheaf R).obj M ⟶ (SheafOfModules.toSheaf R).obj N) :
    ∃ g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
      (PresheafOfModules.restrictScalars α).obj N.val,
      (PresheafOfModules.toPresheaf _).map g = f.hom := by
  refine ⟨PresheafOfModules.homMk f.hom ?_, ?_⟩
  · intro X r s
    obtain ⟨r⟩ := r
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective r
    change M.val.obj X at s
    let f' : M.val.obj X →+ N.val.obj X := (f.hom.app X).hom
    change f' (α.app X (ULift.up (a : ZMod n)) • s) =
      α.app X (ULift.up (a : ZMod n)) • f' s
    exact (congrArg f' (ring_map_int_smul n (α.app X).hom a s)).trans
      ((map_zsmul f' a s).trans (ring_map_int_smul n (α.app X).hom a (f' s)).symm)
  · rfl

private lemma moduleCat_eq_of_identity {R : Type*} [Ring R]
    (M N : ModuleCat.{u + 1} R)
    (h : (forget₂ (ModuleCat R) AddCommGrpCat).obj M =
      (forget₂ (ModuleCat R) AddCommGrpCat).obj N)
    (f : M ⟶ N)
    (hf : (forget₂ (ModuleCat R) AddCommGrpCat).map f = eqToHom h) : M = N := by
  rcases M with @⟨A, iA, mA⟩
  rcases N with @⟨B, iB, mB⟩
  change AddCommGrpCat.of A = AddCommGrpCat.of B at h
  injection h with hAB hi
  cases hAB
  have hi' : iA = iB := eq_of_heq hi
  cases hi'
  have hid (x : A) : f x = x := by
    exact ConcreteCategory.congr_hom hf x
  have hm : mA = mB := Module.ext' _ _ fun r x ↦ by
    have hl := @LinearMap.map_smul R A A _ _ _ mA mB
      (@ModuleCat.Hom.hom R _ (@ModuleCat.of R _ A iA mA)
        (@ModuleCat.of R _ A iA mB) f) r x
    change f (letI := mA; r • x) = (letI := mB; r • f x) at hl
    simpa only [hid] using hl
  cases hm
  rfl

private lemma presheaf_eq_of_identity {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u + 1}} (M N : PresheafOfModules.{u + 1} R)
    (h : M.obj = N.obj) (f : M ⟶ N)
    (hf : ∀ X, f.app X = eqToHom (congrFun h X)) : M = N := by
  cases M with
  | mk obj map hi hc =>
    cases N with
    | mk obj' map' hi' hc' =>
      dsimp at h
      cases h
      have hm : @map = @map' := by
        funext X Y g
        have hh := f.naturality g
        simpa [hf] using hh
      cases hm
      rfl

private lemma sheaf_eqToHom_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G : Sheaf J AddCommGrpCat.{u + 1}}
    (h : F = G) (X : Cᵒᵖ) :
    (eqToHom h).hom.app X = eqToHom (congrArg (fun F ↦ F.obj.obj X) h) := by
  cases h
  rfl

private lemma sheaf_eq_of_identity {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    (M N : SheafOfModules.{u + 1} R)
    (h : (SheafOfModules.toSheaf R).obj M = (SheafOfModules.toSheaf R).obj N)
    (f : M ⟶ N) (hf : (SheafOfModules.toSheaf R).map f = eqToHom h) : M = N := by
  have hh (X : Cᵒᵖ) : (forget₂ (ModuleCat (R.obj.obj X)) AddCommGrpCat).map
      (f.val.app X) = eqToHom (congrArg (fun F ↦ F.obj.obj X) h) :=
    (congrArg (fun g ↦ g.hom.app X) hf).trans (sheaf_eqToHom_app h X)
  have ho (X : Cᵒᵖ) : M.val.obj X = N.val.obj X :=
    moduleCat_eq_of_identity _ _ _ (f.val.app X) (hh X)
  have ha (X : Cᵒᵖ) : f.val.app X = eqToHom (ho X) := by
    apply (forget₂ (ModuleCat _) AddCommGrpCat).map_injective
    rw [eqToHom_map]
    exact hh X
  have hp := presheaf_eq_of_identity M.val N.val (funext ho) f.val ha
  cases M
  cases N
  cases hp
  rfl

/-- The identification of sheaves of `(Z/n)_T`-modules with abelian sheaves killed by `n`.
Source: Stacks, etale-cohomology.tex, Definition 03RW (2), (3), and the proof of
Theorem 03SC; sites-modules.tex, definition-sheaf-modules
(blueprint: lem-weil-pbc-sheaves-killed-by-n-zmod-modules).
This identification is used implicitly by Stacks; its proof is the node's agent-written proof.

1. A module sheaf is an abelian sheaf with sectionwise module actions compatible with
restriction (def-weil-sheaf-of-modules-category). Its action is a morphism of presheaves of
sets. Underlying sets of abelian and ring sheaves are sheaves; their finite products are
sheaves (lem-weil-pbc-presheaf-finite-limits-objectwise).
2. Write `P` for the constant ring presheaf and `η : P → 𝒪` for sheafification. Underlying
sets preserve this sheafification (lem-weil-pbc-ring-sheafification-underlying-sets).
Sheafification preserves finite products (lem-weil-pbc-sheafification-sets-exact), so
`η^m × id` on any finite product with sheaves of sets is a sheafification. Maps from that
product into a sheaf extend uniquely from constants (def-weil-pbc-sheafification).
3. The ring map `η_U` sends the residue of an integer `a` to `a • 1`; hence its action in
any module sheaf is `a • s` (lem-weil-pbc-zmod-module-structure-killed-by-n).
4. Apply step 3 with `a = n`: the residue is zero, so every section is killed by `n`.
5. Conversely, on an `n`-killed abelian sheaf the constant action `ā • s = a • s` is
well defined and commutes with restriction (lem-weil-pbc-zmod-module-structure-killed-by-n).
Extend it uniquely by step 2. Check the unit, the two distributive laws, and associativity
on constants using step 2 and the integer action; this gives the required module sheaf.
6. Any other action agrees on constants by step 3, hence everywhere by step 2, proving
uniqueness while keeping the underlying abelian sheaf fixed.
7. For an additive sheaf map compare `φ(r • s)` and `r • φ(s)`. They agree on constants
because additive maps commute with integer multiplication, and thus everywhere by step 2.
This makes every abelian sheaf map linear (lem-weil-pbc-zmod-module-structure-killed-by-n).
8. Forgetting is faithful since module morphisms are additive morphisms with a property;
step 7 makes it full. Steps 4 and 5 characterize its image, and annihilation is invariant
under isomorphism, characterizing the essential image. Both an abelian isomorphism and
its inverse are linear by step 7, so it lifts to a module-sheaf isomorphism.
-/
theorem sheaves_killed_by_n_zmod_modules
    (T : Scheme.{u}) (n : ℕ) (hn : 1 ≤ n) :
    (∀ (G : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} (ZMod n))))) (U : T.Etaleᵒᵖ)
        (s : G.val.obj U), n • s = 0) ∧
      (∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
        (∀ (U : T.Etaleᵒᵖ) (s : F.1.obj U), n • s = 0) →
          ∃! G : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1} (ZMod n)))), (SheafOfModules.toSheaf ((constantSheaf
              T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of (ULift.{u + 1} (ZMod n))))).obj
              G = F) ∧
      (∀ (G : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1} (ZMod n))))) (U : T.Etaleᵒᵖ)
        (a : ℤ) (s : G.val.obj U),
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod n))))).app U)
            (ULift.up (a : ZMod n)) • s = a • s) ∧
      (∀ (G G' : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1} (ZMod n))))),
        Function.Bijective
          ((SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1} (ZMod n))))).map : (G ⟶ G') →
            ((SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
                (RingCat.of (ULift.{u + 1} (ZMod n))))).obj G ⟶
              (SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
                  (RingCat.of (ULift.{u + 1} (ZMod n))))).obj G'))) ∧
      (∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
        (SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
            (RingCat.of (ULift.{u + 1} (ZMod n))))).essImage F ↔
          ∀ (U : T.Etaleᵒᵖ) (s : F.1.obj U), n • s = 0) ∧
      (∀ (G G' : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1} (ZMod n)))))
        (i : (SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
            (RingCat.of (ULift.{u + 1} (ZMod n))))).obj G ≅
          (SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1} (ZMod n))))).obj G'),
        ∃ j : G ≅ G',
          (SheafOfModules.toSheaf
            ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1} (ZMod n))))).mapIso j = i) := by
  have _hn := hn
  let R := (constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
    (RingCat.of (ULift.{u + 1} (ZMod n)))
  let α := toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod n))))
  have hkill (G : SheafOfModules.{u + 1} R) (U : T.Etaleᵒᵖ) (s : G.val.obj U) :
      n • s = 0 := constant_module_killed n (α.app U).hom s
  have hfull (G G' : SheafOfModules.{u + 1} R) :
      Function.Bijective ((SheafOfModules.toSheaf R).map : (G ⟶ G') → _) := by
    refine ⟨(SheafOfModules.toSheaf R).map_injective, ?_⟩
    intro f
    obtain ⟨g, hg⟩ := constant_restrict_linear T.smallEtaleTopology n R α G G' f
    let j := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α G'.isSheaf).symm g
    refine ⟨⟨j⟩, ?_⟩
    apply ObjectProperty.hom_ext
    exact (congrArg (fun k ↦ (PresheafOfModules.toPresheaf _).map k)
      ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective
        α G'.isSheaf).apply_symm_apply g)).trans hg
  refine ⟨hkill, ?_, ?_, hfull, ?_, ?_⟩
  · intro F hF
    let (U : T.Etaleᵒᵖ) : Module (ZMod n) (F.obj.obj U) :=
      AddCommGroup.zmodModule (hF U)
    let : ∀ U, Module
        (((Functor.const T.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod n)))).obj U)
        (F.obj.obj U) := fun U ↦ ULift.module
    let P : PresheafOfModules.{u + 1}
        ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod n)))) :=
      PresheafOfModules.ofPresheaf F.obj (fun {_ _} f r s ↦
        ZMod.map_smul (F.obj.map f).hom r.down s)
    let φ : P.presheaf ⟶ F.obj := eqToHom (by rfl)
    let : IsIso φ := by dsimp [φ]; infer_instance
    let G : SheafOfModules.{u + 1} R :=
      PresheafOfModules.sheafify (M₀ := P) (A := F) α φ
    refine ⟨G, rfl, ?_⟩
    intro G' hG'
    obtain ⟨f, hf⟩ := (hfull G' G).surjective (eqToHom hG')
    exact sheaf_eq_of_identity G' G hG' f hf
  · intro G U a s
    exact ring_map_int_smul n (α.app U).hom a s
  · intro F
    constructor
    · rintro ⟨G, ⟨i⟩⟩ U s
      let e := (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat ⋙
        (evaluation _ _).obj U).mapIso i
      have h := congrArg (fun x ↦ e.hom x) (hkill G U (e.inv s))
      have he : e.hom (e.inv s) = s := by
        rw [← ConcreteCategory.comp_apply, e.inv_hom_id]
        rfl
      simpa only [map_nsmul, map_zero, he] using h
    · intro hF
      let (U : T.Etaleᵒᵖ) : Module (ZMod n) (F.obj.obj U) :=
        AddCommGroup.zmodModule (hF U)
      let : ∀ U, Module
          (((Functor.const T.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod n)))).obj U)
          (F.obj.obj U) := fun U ↦ ULift.module
      let P : PresheafOfModules.{u + 1}
          ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod n)))) :=
        PresheafOfModules.ofPresheaf F.obj (fun {_ _} f r s ↦
          ZMod.map_smul (F.obj.map f).hom r.down s)
      let φ : P.presheaf ⟶ F.obj := eqToHom (by rfl)
      let : IsIso φ := by dsimp [φ]; infer_instance
      exact ⟨PresheafOfModules.sheafify (M₀ := P) (A := F) α φ, ⟨Iso.refl F⟩⟩
  · intro G G' i
    let : (SheafOfModules.toSheaf.{u + 1} R).Full :=
      ⟨fun {G G'} f ↦ (hfull G G').surjective f⟩
    refine ⟨(SheafOfModules.toSheaf R).preimageIso i, ?_⟩
    apply Iso.ext
    exact (SheafOfModules.toSheaf R).map_preimage i.hom

end AlgebraicGeometry
