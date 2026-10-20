/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.DeterminantDualPairing
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairingLocal
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison

/-! Intermediate determinant facts for the ordinary determinant evaluation.
Source: Stacks Project, Tag 0BRT. -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Exterior powers commute with the internal dual in top degree.
Source: Stacks Project, Tag 0BRT, determinant pairing; Mathlib
`exteriorPower.pairingDual` on each trivializing open.
(blueprint: lem-sc-determinant-dual-evaluation-dual-identification).

Proof: choose an open cover trivializing `M` with a basis of `d` sections.
On each subopen of a trivializing open, sections of `M` form a free module of
rank `d`, and internal dual sections identify with its ring-linear dual: evaluate
at that subopen and reconstruct the internal map using the basis coordinates.
Exterior sheafification commutes with restriction because the localized site's
covers are exactly the covers of the corresponding opens. The finite free exterior
power has the basis of increasing wedges (Mathlib `Basis.exteriorPower`), so its
presheaf on this open is already a sheaf, with rank-one generator the top wedge.
Mathlib `exteriorPower.pairingDual` sends the wedge of the dual basis to the
functional taking the top basis wedge to one, and is bijective by
`exteriorPower.bijective_pairingDual`. The determinant formula is compatible with
ring restriction and restriction of internal Hom sections. Therefore these local
maps to the internal dual of the exterior sheaf agree on overlaps and glue.
Their inverses agree by uniqueness of inverses, proving the glued map is an
isomorphism. Changing the local basis scales the top wedge and its dual by inverse
determinants, so the construction is independent of the cover. For `d = 0`, empty
wedges identify both sides with the structure sheaf. The empty scheme has no
points to check and its module category is trivial. No nontriviality assumption
on the section rings is needed. -/
theorem exteriorSheaf_dual_iso (X : Scheme.{u}) (M : X.Modules) (d : ℕ)
    (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((Scheme.Modules.exteriorSheaf
      (SheafOfModules.homObj (R := X.sheaf) M
        (SheafOfModules.unit X.ringCatSheaf)) d) ≅
      Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M d)) := by
  obtain ⟨f, hf⟩ := exterior_dual_pairing_exists X M d
  obtain ⟨I, U, hU, e⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}
      (M := M) (r := d)).mp hfree
  let a := Scheme.Modules.exteriorSheafPowerIso (Scheme.Modules.dual M) d
  let b := (Scheme.Modules.dualFunctor X).mapIso
    (Scheme.Modules.exteriorSheafPowerIso M d).symm.op
  let f' := a.inv ≫ f ≫ b.hom
  have hf' (W : X.Opens) (x : Fin d → M.val.obj (Opposite.op W))
      (φ : Fin d → (Scheme.Modules.dual M).val.obj (Opposite.op W)) :
      (f'.app W (Scheme.Modules.wedge φ)).app
          (Opposite.op (Over.mk (𝟙 W))) (Scheme.Modules.wedge x) =
        (Matrix.of fun i j ↦ (show X.presheaf.obj (Opposite.op W) from
          (φ j).app (Opposite.op (Over.mk (𝟙 W))) (x i))).det := by
    change (f.app W (a.inv.app W (Scheme.Modules.wedge φ))).app
      (Opposite.op (Over.mk (𝟙 W)))
        ((Scheme.Modules.exteriorSheafPowerIso M d).inv.app W (Scheme.Modules.wedge x)) = _
    rw [Scheme.Modules.exteriorSheafPowerIso_inv_wedge,
      Scheme.Modules.exteriorSheafPowerIso_inv_wedge]
    exact hf W x φ
  have hb (V : X.Opens) (i : I) (g : V ⟶ U i) :
      Function.Bijective (f.val.app (Opposite.op V)) := by
    have h := exterior_dual_pairing_app_bijective X M d f' hf' (U i) d (e i).some V g
    change Function.Bijective
      ((b.hom.app V) ∘ (f.app V) ∘ (a.inv.app V)) at h
    exact ((Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso
      (b.hom.app V)) (f.app V)).mp
        ((Function.Bijective.of_comp_iff _
          (ConcreteCategory.bijective_of_isIso (a.inv.app V))).mp h))
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1
      ⟨Presheaf.isLocallyInjective_of_coversTop hU _ fun V i g ↦ (hb V i g).1,
        Presheaf.isLocallySurjective_of_coversTop hU _ fun V i g ↦ (hb V i g).2⟩
  let : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  have : IsIso f :=
    isIso_of_reflects_iso f (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  exact ⟨asIso f⟩

end AlgebraicGeometry
