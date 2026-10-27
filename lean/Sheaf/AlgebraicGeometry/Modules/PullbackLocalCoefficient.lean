/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Local coefficients of pullback morphisms on affine opens

Source: `WeilConjectures/AlgebraicGeometry/Modules/ZeroLocus.lean`,
`IsFreeGenerator.exists_pullback` and its restriction in `Hom.comap_zeroLocus`
(blueprint: lem-pc-zero-scheme-pullback-local-coefficient).

The pullback of modules is the recorded `Scheme.Modules.tensorPullback`
of `def-pc-module-pullback`, not Mathlib's abstract left adjoint `Scheme.Modules.pullback`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

private theorem isFreeGenerator_iso {X : Scheme.{u}} {M N : X.Modules}
    (i : M ≅ N) {U : X.Opens} {e : Γ(M, U)} (he : IsFreeGenerator e) :
    IsFreeGenerator (i.hom.app U e) := by
  intro W hW
  have hi := ConcreteCategory.bijective_of_isIso
    ((toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (.op W)).map i.hom)
  change Function.Bijective (i.hom.app W) at hi
  simpa only [Function.comp_def, Hom.app_smul, Hom.app_presheaf_map] using
    hi.comp (he W hW)

/-- On an affine open contained in the inverse image of a trivializing affine open, the
pulled-back morphism has free generators with coefficient `g.appLE U V hVU b`.
The pullback is `AlgebraicGeometry.Scheme.Modules.tensorPullback`, recorded by
`def-pc-module-pullback`.

Source: `WeilConjectures/AlgebraicGeometry/Modules/ZeroLocus.lean`,
`IsFreeGenerator.exists_pullback` (lines 388–446) and `Hom.comap_zeroLocus` (lines 521–530).
(blueprint: lem-pc-zero-scheme-pullback-local-coefficient).

Proof: apply `lem-pc-zero-scheme-pullback-full-local-coefficient`, namely
`IsFreeGenerator.exists_pullback`, to the generators on `U`. It gives free generators on
`g ⁻¹ᵁ U` with coefficient `g.app U b` for Mathlib's pullback. Transport them to
`tensorPullback g` along the natural isomorphism given by uniqueness of left adjoints of
`pushforward g` (`nonempty_tensorPullbackAdjunction`); an isomorphism of modules preserves free
generators and scalar multiplication, and its naturality transports the image of `φ`.
Restrict both generators to `V` using `IsFreeGenerator.map hVU`.
Finally, morphisms commute with restriction (`Hom.app_presheaf_map`), restrictions preserve
scalar multiplication, and `g.appLE U V hVU` is `g.app U` followed by restriction to `V`.
Thus the restricted generators satisfy the displayed equation. -/
theorem IsFreeGenerator.exists_tensorPullback_affine
    {X Y : Scheme.{u}} (g : Y ⟶ X) {M N : X.Modules}
    [M.IsInvertible] [N.IsInvertible] (φ : M ⟶ N) (U : X.affineOpens)
    {eM : Γ(M, U.1)} {eN : Γ(N, U.1)} (hM : IsFreeGenerator eM)
    (hN : IsFreeGenerator eN) {b : Γ(X, U.1)} (hb : φ.app U.1 eM = b • eN)
    (V : Y.affineOpens) (hVU : V.1 ≤ g ⁻¹ᵁ U.1) :
    ∃ (eM' : Γ((tensorPullback g).obj M, V.1))
      (eN' : Γ((tensorPullback g).obj N, V.1)),
      IsFreeGenerator eM' ∧ IsFreeGenerator eN' ∧
        ((tensorPullback g).map φ).app V.1 eM' = g.appLE U.1 V.1 hVU b • eN' := by
  classical
  obtain ⟨eM', eN', hM', hN', hb'⟩ := hM.exists_pullback g φ hN hb
  let i : pullback g ≅ tensorPullback g :=
    (pullbackPushforwardAdjunction g).leftAdjointUniq
      (nonempty_tensorPullbackAdjunction g).some
  let sM := ((pullback g).obj M).presheaf.map (homOfLE hVU).op eM'
  let sN := ((pullback g).obj N).presheaf.map (homOfLE hVU).op eN'
  refine ⟨(i.app M).hom.app V.1 sM, (i.app N).hom.app V.1 sN,
    isFreeGenerator_iso (i.app M) (hM'.map hVU),
    isFreeGenerator_iso (i.app N) (hN'.map hVU), ?_⟩
  have hcoeff : ((pullback g).map φ).app V.1 sM = g.appLE U.1 V.1 hVU b • sN := by
    dsimp [sM, sN]
    rw [Hom.app_presheaf_map, hb', map_smul]
    rfl
  have hnat := congrArg (fun f ↦ f.app V.1 sM) (i.hom.naturality φ)
  change (i.app N).hom.app V.1 (((pullback g).map φ).app V.1 sM) =
    ((tensorPullback g).map φ).app V.1 ((i.app M).hom.app V.1 sM) at hnat
  rw [← hnat, hcoeff, Hom.app_smul]

end AlgebraicGeometry.Scheme.Modules
