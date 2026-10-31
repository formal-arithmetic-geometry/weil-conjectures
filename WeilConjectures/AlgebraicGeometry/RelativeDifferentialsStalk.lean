/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Stalks of relative differentials

Source: Stacks Project, modules.tex, Tag 08TE, lemma-stalk-module-differentials;
morphisms.tex, Tag 01UQ, definition-sheaf-differentials
(blueprint: lem-sfb-relative-differentials-stalk).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory.Limits TopologicalSpace

-- Take the stalk of the additive sheaf derivation, preserving its germ formula.
private noncomputable def stalkDerivationAdd {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    X.presheaf.stalk x →+
      f.relativeDifferentials.presheaf.stalk x :=
  let d : X.presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶
      f.relativeDifferentials.presheaf :=
    { app := fun U ↦ AddCommGrpCat.ofHom f.relativeDifferentialsDerivation.d
      naturality := fun U V g ↦ by
        ext a
        exact f.relativeDifferentialsDerivation.d_map g a }
  ((preservesColimitIso ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map d).hom

private theorem stalkDerivationAdd_germ {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    stalkDerivationAdd f x (X.presheaf.germ U x hx a) =
      f.relativeDifferentials.presheaf.germ U x hx (f.relativeDifferentialsDerivation.d a) := by
  unfold stalkDerivationAdd
  change (((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map
      (X.presheaf.germ U x hx) ≫
    (preservesColimitIso ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
      ((OpenNhds.inclusion x).op ⋙ X.presheaf)).hom ≫ _) a = _
  rw [← Category.assoc]
  erw [ι_preservesColimitIso_hom]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply
    (F := X.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (G := f.relativeDifferentials.presheaf) U x hx _ a

private theorem stalkDerivationAdd_mul {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (a b : X.presheaf.stalk x) :
    stalkDerivationAdd f x (a * b) =
      a • stalkDerivationAdd f x b + b • stalkDerivationAdd f x a := by
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, b, rfl⟩ := X.presheaf.exists_germ_eq b
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx a,
    ← X.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx b,
    ← map_mul, stalkDerivationAdd_germ, f.relativeDifferentialsDerivation.d_mul, map_add,
    stalkDerivationAdd_germ, stalkDerivationAdd_germ]
  exact congrArg₂ (· + ·)
    (PresheafOfModules.germ_smul (R := X.presheaf) f.relativeDifferentials.val x _ hx _ _)
    (PresheafOfModules.germ_smul (R := X.presheaf) f.relativeDifferentials.val x _ hx _ _)

private theorem stalkDerivationAdd_stalkMap {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (a : S.presheaf.stalk (f x)) : stalkDerivationAdd f x (f.stalkMap x a) = 0 := by
  obtain ⟨U, hx, a, rfl⟩ := S.presheaf.exists_germ_eq a
  rw [← ConcreteCategory.comp_apply, f.germ_stalkMap, ConcreteCategory.comp_apply,
    stalkDerivationAdd_germ]
  exact (congrArg (f.relativeDifferentials.presheaf.germ _ x hx)
    (f.relativeDifferentialsDerivation.d_app_app U a)).trans (map_zero _)

-- Bundle the stalk of the sheaf derivation relative to the actual base stalk map.
private noncomputable def relativeStalkDerivation {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    (ModuleCat.of (X.presheaf.stalk x)
      (f.relativeDifferentials.presheaf.stalk x)).Derivation (f.stalkMap x) :=
  ModuleCat.Derivation.mk (stalkDerivationAdd f x)
    (stalkDerivationAdd f x).map_add (stalkDerivationAdd_mul f x)
    (stalkDerivationAdd_stalkMap f x)

-- A derivation of the local ring gives a sheaf derivation into a skyscraper module.
private noncomputable def relativeStalkSheafDerivation {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (D : N.Derivation (f.stalkMap x)) :
    (Scheme.Modules.skyscraper x N).val.Derivation' f.pullbackPresheafToPresheaf := by
  apply f.derivationMk
    (fun {U} ↦ {
      toFun := fun a hx ↦ D.d (X.presheaf.germ U.unop x hx.down a)
      map_zero' := by
        apply Scheme.Modules.SkyscraperSections.ext
        intro hx
        change D.d (X.presheaf.germ _ x hx 0) = 0
        rw [map_zero]
        have h := D.d_add 0 0
        rw [add_zero] at h
        exact add_eq_left.mp h.symm
      map_add' := by
        intro a b
        apply Scheme.Modules.SkyscraperSections.ext
        intro hx
        change D.d (X.presheaf.germ _ x hx (a + b)) =
          D.d (X.presheaf.germ _ x hx a) + D.d (X.presheaf.germ _ x hx b)
        rw [map_add, D.d_add] })
  · intro U a b
    apply Scheme.Modules.SkyscraperSections.ext
    intro hx
    change D.d (X.presheaf.germ U.unop x hx (a * b)) = _
    exact (congrArg D.d (map_mul (X.presheaf.germ U.unop x hx).hom a b)).trans
      (D.d_mul _ _)
  · intro U V g a
    apply Scheme.Modules.SkyscraperSections.ext
    intro hx
    change D.d (X.presheaf.germ V.unop x hx (X.presheaf.map g a)) = _
    exact congrArg D.d (X.presheaf.germ_res_apply' g x hx a)
  · intro V a
    apply Scheme.Modules.SkyscraperSections.ext
    intro hx
    change D.d (X.presheaf.germ (f ⁻¹ᵁ V) x hx (f.app V a)) = 0
    rw [← ConcreteCategory.comp_apply, ← f.germ_stalkMap, ConcreteCategory.comp_apply]
    exact D.d_map _

private theorem stalkLinearMap_ext_d {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    {N : Type u} [AddCommGroup N] [Module (X.presheaf.stalk x) N]
    (l₁ l₂ : f.relativeDifferentials.presheaf.stalk x →ₗ[X.presheaf.stalk x] N)
    (h : ∀ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)),
      l₁ (f.relativeDifferentials.presheaf.germ U x hx
        (f.relativeDifferentialsDerivation.d a)) =
      l₂ (f.relativeDifferentials.presheaf.germ U x hx
        (f.relativeDifferentialsDerivation.d a))) : l₁ = l₂ := by
  apply (Scheme.Modules.skyscraperHomEquiv x N f.relativeDifferentials).injective
  apply (f.relativeDifferentialsHomEquiv _).injective
  ext U a
  apply Scheme.Modules.SkyscraperSections.ext
  intro hx
  exact h U.unop hx a

private noncomputable def relativeDifferentialsStalkToKaehler {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    f.relativeDifferentials.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      CommRingCat.KaehlerDifferential (f.stalkMap x) :=
  (Scheme.Modules.skyscraperHomEquiv x _ _).symm
    ((f.relativeDifferentialsHomEquiv _).symm
      (relativeStalkSheafDerivation f x _ (CommRingCat.KaehlerDifferential.D _)))

private theorem relativeDifferentialsStalkToKaehler_germ {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    relativeDifferentialsStalkToKaehler f x
      (f.relativeDifferentials.presheaf.germ U x hx (f.relativeDifferentialsDerivation.d a)) =
      CommRingCat.KaehlerDifferential.d (f := f.stalkMap x)
        (X.presheaf.germ U x hx a) := by
  dsimp only [relativeDifferentialsStalkToKaehler, Scheme.Modules.skyscraperHomEquiv,
    Equiv.coe_fn_symm_mk, LinearMap.comp_apply]
  rw [Scheme.Modules.Hom.stalkLinearMap_germ, Scheme.Modules.skyscraperStalkEval_germ]
  erw [relativeDifferentialsHomEquiv_symm_app_d]
  rfl

private theorem relativeDifferentialsStalkToKaehler_bijective {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    Function.Bijective (relativeDifferentialsStalkToKaehler f x) := by
  let l := relativeDifferentialsStalkToKaehler f x
  let r := (relativeStalkDerivation f x).desc.hom
  have hrl : r.comp l = LinearMap.id := by
    apply stalkLinearMap_ext_d f x
    intro U hx a
    change r (l _) = _
    rw [relativeDifferentialsStalkToKaehler_germ]
    change (relativeStalkDerivation f x).desc (CommRingCat.KaehlerDifferential.d _) = _
    rw [ModuleCat.Derivation.desc_d]
    exact stalkDerivationAdd_germ f x U hx a
  have hlr : l.comp r = LinearMap.id := by
    change (ModuleCat.ofHom (l.comp r)).hom =
      ModuleCat.Hom.hom (𝟙 (CommRingCat.KaehlerDifferential (f.stalkMap x)))
    apply congrArg ModuleCat.Hom.hom
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq a
    change l ((relativeStalkDerivation f x).desc (CommRingCat.KaehlerDifferential.d _)) = _
    rw [ModuleCat.Derivation.desc_d]
    change l (stalkDerivationAdd f x _) = _
    rw [stalkDerivationAdd_germ, relativeDifferentialsStalkToKaehler_germ]
    rfl
  exact ⟨Function.LeftInverse.injective (g := r) (fun a ↦ LinearMap.congr_fun hrl a),
    Function.RightInverse.surjective (g := r) (fun a ↦ LinearMap.congr_fun hlr a)⟩

/-- The stalk of relative differentials is canonically the differential module of the
local ring map. The unique linear equivalence is characterized by its value on germs
of universal differentials of local sections.

Source: Stacks Project, modules.tex, Tag 08TE, lemma-stalk-module-differentials,
applied to the relative differential sheaf of morphisms.tex, Tag 01UQ.
(blueprint: lem-sfb-relative-differentials-stalk).

Proof:
1. Take the stalk of the additive sheaf derivation. On germs it sends `a_z` to
   `(d a)_z`. The sheaf Leibniz rule and the germ scalar action give Leibniz on
   stalks. The compatibility of the scheme stalk map with germs shows that this
   derivation kills the image of the base stalk ring.
2. A derivation of the local ring relative to the base stalk gives a sheaf
   derivation into its skyscraper module by `a ↦ D(a_z)` on neighbourhoods of `z`.
   Compatibility with restriction follows from the germ restriction formula;
   relativity follows from the same stalk-map formula.
3. Apply the universal property of the sheaf of differentials and the
   stalk–skyscraper adjunction to the universal derivation of the local ring.
   This constructs a linear map from the differential stalk to the ring
   differentials, with exactly the required formula on differential germs.
4. The stalk derivation from step 1 induces a linear map in the reverse direction
   by the universal property of ring differentials. The composites are identities:
   one is checked on differential germs using the sheaf universal property and
   the stalk–skyscraper adjunction, the other on universal ring differentials.
5. The same extensionality on differential germs proves uniqueness. -/
theorem existsUnique_relativeDifferentialsStalkEquiv {X S : Scheme.{u}}
    (f : X ⟶ S) (z : X) :
    ∃! e : ((RingedSpace.moduleStalkFunctor X.toRingedSpace z).obj
        f.relativeDifferentials) ≃ₗ[X.presheaf.stalk z]
        CommRingCat.KaehlerDifferential (f.stalkMap z),
      ∀ (U : X.Opens) (hz : z ∈ U) (a : Γ(X, U)),
        e (f.relativeDifferentials.presheaf.germ U z hz
          (f.relativeDifferentialsDerivation.d (X := op U) a)) =
        CommRingCat.KaehlerDifferential.d (f := f.stalkMap z)
          (X.presheaf.germ U z hz a) := by
  let e := LinearEquiv.ofBijective (relativeDifferentialsStalkToKaehler f z)
    (relativeDifferentialsStalkToKaehler_bijective f z)
  refine ⟨e, relativeDifferentialsStalkToKaehler_germ f z, ?_⟩
  intro e' he'
  apply LinearEquiv.toLinearMap_injective
  apply stalkLinearMap_ext_d f z
  intro U hz a
  exact (he' U hz a).trans (relativeDifferentialsStalkToKaehler_germ f z U hz a).symm

end AlgebraicGeometry.Scheme.Hom
