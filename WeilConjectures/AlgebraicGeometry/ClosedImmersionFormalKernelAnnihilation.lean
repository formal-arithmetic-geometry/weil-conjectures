/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.ClosedImmersionFormalKernelComparison
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealPowerAnnihilation
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Annihilation of a transported formal kernel

Source: Stacks Project, Cohomology of Schemes, Theorem 088E and Tags 087T, 087W, 087X.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A commuting pushforward square transports annihilation of a formal kernel by
an ideal power to annihilation by the inverse image ideal.

Source: Stacks Project, Theorem 088E, paragraphs 2--4, and Tags 087T, 087W, 087X. -/
theorem closedImmersion_formalKernel_annihilated
    {X Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]
    (j : Z ⟶ X) [IsClosedImmersion j] (Q : X.IdealSheafData)
    [Abelian (CoherentFormalModule X Q)]
    (M N : CoherentFormalModule X Q)
    (G D : CoherentFormalModule Z (Q.comap j))
    (a : M ⟶ N) (α : G ⟶ D)
    (e : M.obj ≅ G.obj ⋙ Scheme.Modules.pushforward j)
    (d : N.obj ≅ D.obj ⋙ Scheme.Modules.pushforward j)
    (hsquare : a.hom ≫ d.hom =
      e.hom ≫ Functor.whiskerRight α.hom (Scheme.Modules.pushforward j))
    (L : Z.IdealSheafData) (t : ℕ) (k : KernelFork α) (hk : IsLimit k)
    (hkill : ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower L.toModulesι t).2 (k.pt.obj.obj (op n)))) :
    AnnihilatedBy Q ((L ^ t).map j) (kernel a) := by
  obtain ⟨q⟩ := closedImmersion_formalKernel_comparison j Q M N G D a α e d hsquare k hk
  intro n
  have hF := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z
    (k.pt.obj.obj (op n))).mp (k.pt.property.1 n)
  have hH := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X
    ((kernel a).obj.obj (op n))).mp ((kernel a).property.1 n)
  let := hF.1
  let := hH.1
  exact Scheme.closedImmersion_idealPower_annihilation j L t (k.pt.obj.obj (op n))
    ((kernel a).obj.obj (op n)) (q.app (op n)) (hkill n)

end AlgebraicGeometry
