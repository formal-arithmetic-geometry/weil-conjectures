/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeGroupoidModule
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.Descent

/-!
# Coinduction for quasi-coherent groupoid modules

Source: Stacks Project, groupoids.tex, Tags 07TR (lemma-construct-quasi-coherent)
and 0GNF (remark-adjunction-map) (blueprint: lem-sfb-groupoid-coinduction-adjunction).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Coinduction has underlying functor `s_* t^*` and the specified ordinary-adjunction unit.
Source: Stacks Project, Tags 07TR and 0GNF
(blueprint: lem-sfb-groupoid-coinduction-adjunction).

Proof:
1. Form the pair groupoid on `R ×[t,U,t] R`, with source the second projection and
   target the first. The difference `(a,b) ↦ a⁻¹b`, together with object map `s`,
   defines a groupoid morphism. Its target square is Cartesian: its inverse coordinate
   change is `(a,r) ↦ (a,ar)`. This uses def-a1-scheme-groupoid-laws and
   def-pc-fibre-product.
2. The section `e` makes `t` surjective; flatness and quasi-compactness make `{t}` an
   fpqc cover (def-weil-pbc-fpqc-covering). By lem-pc-fpqc-descent, pullback along `t`
   identifies quasi-coherent modules on `U` with modules on the pair groupoid.
3. Pull the cocycle for `beta` back along `(a,b) ↦ (a,a⁻¹b)`. It identifies the
   pullback of an equivariant module along the difference morphism with the descent
   datum of its underlying module, through `beta`. Equivariance of morphisms gives
   naturality (def-pc-module-pullback).
4. Apply lem-sfb-cartesian-groupoid-pushforward-adjunction to the difference morphism.
   Composing its direct image with the descent equivalence gives `G` with underlying
   object and map `s_*t^*`. The three natural Hom bijections give `forget ⊣ G`.
   The inverse bijection sends `h : M → H` to the ordinary transpose of
   `t^*h ∘ beta⁻¹`; the equivariant structures are natural because `G` is a functor.
5. Set `h = 1` in that inverse bijection. The ordinary transpose of `beta⁻¹` is
   `eta^s ≫ s_*(beta⁻¹)`, giving exactly the unit of Tag 0GNF. -/
theorem exists_groupoid_coinduction_adjunction
    (S : Scheme.{u}) {U R : Scheme.{u}} (p : U ⟶ S) (q : R ⟶ S)
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (_hs : s ≫ p = q) (_ht : t ≫ p = q) (hG : IsGroupoid s t e i c)
    [Flat s] [Flat t] [QuasiCompact s] [QuasiCompact t]
    [QuasiSeparated s] [QuasiSeparated t] :
    ∃ (G : (SheafOfModules.isQuasicoherent U.ringCatSheaf).FullSubcategory ⥤
        GroupoidModule s t e i c hG)
      (adj : GroupoidModule.forgetToQuasiCoherent (hG := hG) ⊣ G)
      (h : G ⋙ GroupoidModule.forgetToQuasiCoherent (hG := hG) ⋙
          (SheafOfModules.isQuasicoherent U.ringCatSheaf).ι =
        (SheafOfModules.isQuasicoherent U.ringCatSheaf).ι ⋙
          Modules.tensorPullback t ⋙ Modules.pushforward s),
      ∀ M : GroupoidModule s t e i c hG,
        (SheafOfModules.isQuasicoherent U.ringCatSheaf).ι.map
            ((GroupoidModule.forgetToQuasiCoherent (hG := hG)).map (adj.unit.app M)) ≫
          eqToHom (congrArg
            (fun F : (SheafOfModules.isQuasicoherent U.ringCatSheaf).FullSubcategory ⥤ U.Modules ↦
              F.obj ((GroupoidModule.forgetToQuasiCoherent (hG := hG)).obj M)) h) =
        (Modules.tensorPullbackSectionAdjunction s).unit.app M.moduleObj ≫
          (Modules.pushforward s).map
            (by simpa only [groupoidModulePullback, GroupoidModule.forgetToQuasiCoherent,
              ObjectProperty.ι_obj] using M.beta.inv) := by
  sorry

end AlgebraicGeometry.Scheme
