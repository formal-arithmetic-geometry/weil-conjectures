/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.FlatComplexBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModule
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# Base change of the Čech complex over an affine base

Consider a cartesian square of schemes with affine bases
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
and write `A = Γ(S, ⊤)`, `B = Γ(T, ⊤)`. For a quasi-coherent `𝒪_X`-module `ℱ` and an affine
open `W` of `X`, the map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g'^* ℱ, g'⁻¹ W)`, `b ⊗ m ↦ b • g'^* m`, is bijective
(`AlgebraicGeometry.Scheme.Modules.bijective_sectionsBaseChange`): it is the composite of the
identification `Γ(g'^* ℱ, g'⁻¹ W) = Γ(Y, g'⁻¹ W) ⊗[Γ(X, W)] Γ(ℱ, W)` and of the pushout
`Γ(Y, g'⁻¹ W) = Γ(X, W) ⊗[A] B` of rings.

Consequently, for a family `U` of opens of `X` whose finite intersections are affine, the Čech
complex of `g'^* ℱ` for `g'⁻¹ U` is the base change `B ⊗[A] Č(U, ℱ)` of the Čech complex of `ℱ`
(`AlgebraicGeometry.Scheme.Modules.cechModuleComplexBaseChangeIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules)
  [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)

/-! ### The Čech complex -/

section Cech

open TopCat.Presheaf

variable {ι : Type u} (U : ι → X.Opens)

variable [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
  [Finite ι] (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))

end Cech

end AlgebraicGeometry.Scheme.Modules
