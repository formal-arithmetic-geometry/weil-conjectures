/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationExtension
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Lifting germs from globally finitely presented modules

Source: Stacks Project, Properties of Schemes, Tag 01PJ,
`lemma-directed-colimit-diagram-finite-presentation`, final surjectivity paragraph
(blueprint: lem-weil-pbc-finite-presentation-stalk-germ-lifting).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Every germ of a quasi-coherent module on a qcqs scheme comes from a globally
finitely presented module mapping to it.

Source: Stacks Project, Properties of Schemes, Tag 01PJ,
`lemma-directed-colimit-diagram-finite-presentation`, final surjectivity paragraph
(blueprint: lem-weil-pbc-finite-presentation-stalk-germ-lifting).

Proof:
1. Represent the given germ by a section on a neighbourhood of x, using
   def-weil-pbc-module-stalk. Shrink to an affine neighbourhood U using
   lem-weil-pbc-affine-opens-basis. By lem-weil-pbc-affine-scheme-qcqs, U is compact.
2. Multiplication by the section defines an O_U-linear morphism O_U to F restricted
   to U: restriction respects scalar multiplication. The source O_U has finite
   presentation with one generator and no relations, by
   def-weil-pbc-module-finite-type-presentation.
3. Apply lem-weil-pbc-module-finite-presentation-extension to obtain a globally
   finitely presented G, a map psi to F, and an isomorphism e from G restricted to U
   to O_U, identifying the restricted map with multiplication by the section.
4. Take the section b of G on U which e sends to 1, and let t be its germ at x.
   By def-weil-pbc-module-stalk, psi_x(t) is the germ of psi(b), hence the germ of
   1 times the chosen section, which is the original s.
-/
theorem exists_finitePresentation_stalk_germ_lift
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (s : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) :
    ∃ (G : X.Modules), G.IsFinitePresentation ∧
      ∃ (ψ : G ⟶ F) (t : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G),
        (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ψ t = s := by
  classical
  obtain ⟨W, hxW, a₀, ha₀⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf s
  obtain ⟨U, hU, hxU, hUW⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxW
  let a := F.val.map (homOfLE hUW).op a₀
  have ha : TopCat.Presheaf.germ F.val.presheaf U x hxU a = s :=
    (TopCat.Presheaf.germ_res_apply F.val.presheaf
      (homOfLE hUW) x hxU a₀).trans ha₀
  let σ : (F.over U).sections :=
    (F.over U).val.sectionsMk (fun V ↦ F.val.map V.unop.hom.op a) (by
      intro V V' f
      change F.val.presheaf.map f.unop.left.op
        (F.val.presheaf.map V.unop.hom.op a) =
          F.val.presheaf.map V'.unop.hom.op a
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl)
  let φ : SheafOfModules.unit ((moduleRings X.toRingedSpace).over U) ⟶ F.over U :=
    (F.over U).unitHomEquiv.symm σ
  have : (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)).IsFinitePresentation := by
    let R := (moduleRings X.toRingedSpace).over U
    let P := SheafOfModules.presentationOfIsCokernelFree (ι := PEmpty.{u + 1})
      (0 : SheafOfModules.free _ ⟶ SheafOfModules.free (R := R) PUnit.{u + 1})
      (𝟙 _) (by simp) (Limits.CokernelCofork.IsColimit.ofId _ rfl)
    have : P.IsFinite :=
      ⟨⟨inferInstanceAs (Finite PUnit)⟩, ⟨inferInstanceAs (Finite PEmpty)⟩⟩
    exact (SheafOfModules.isFinitePresentation R).prop_of_iso
      (SheafOfModules.freeUniqueIso PUnit.{u + 1}) P.isFinitePresentation
  obtain ⟨G, hG, ψ, e, he⟩ :=
    exists_finitePresentation_extension X U hU.isCompact F _ φ
  let V : Over U := Over.mk (𝟙 U)
  let b : G.val.obj (.op U) := e.inv.val.app (.op V) (1 : Γ(X, U))
  refine ⟨G, hG, ψ, TopCat.Presheaf.germ G.val.presheaf U x hxU b, ?_⟩
  change RingedSpace.stalkAddMap X.toRingedSpace x ψ _ = s
  dsimp only [RingedSpace.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ F.val.presheaf U x hxU (ψ.val.app (.op U) b) = s
  have hb : ψ.val.app (.op U) b = a := by
    have h := congrArg (fun f ↦ f.val.app (.op V) b) he
    change ψ.val.app (.op U) b = φ.val.app (.op V) (e.hom.val.app (.op V) b) at h
    rw [h]
    have hi : e.hom.val.app (.op V) b = (1 : Γ(X, U)) := by
      exact congrArg (fun f ↦ f.val.app (.op V) (1 : Γ(X, U))) e.inv_hom_id
    rw [hi]
    have hφ := congrArg (fun t : (F.over U).sections ↦ t.val (.op V))
      ((F.over U).unitHomEquiv.apply_symm_apply σ)
    change φ.val.app (.op V) (1 : Γ(X, U)) =
      F.val.presheaf.map (𝟙 (Opposite.op U)) a at hφ
    exact hφ.trans (CategoryTheory.congr_fun (F.val.presheaf.map_id _) a)
  rw [hb]
  exact ha

end AlgebraicGeometry.Scheme.Modules
