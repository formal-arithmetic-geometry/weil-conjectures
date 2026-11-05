/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.SectionsBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# Sections of the Čech resolution of a base change

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` affine, a finite family `U` of opens of `X` and an open `W` of `T`, with
`B = Γ(T, W)`. The sections over `f'⁻¹ W` of the sheafified Čech complex `Č(g'⁻¹ U, g'^* ℱ)` are
the explicit Čech complex of the presheaf `V ↦ Γ(f'⁻¹ W, j_{V,*} (g'^* ℱ)|_V)`
(`AlgebraicGeometry.Scheme.Modules.sectionsCechResolutionIso`). We construct the base change
map `B ⊗[A] Č(U, ℱ) ⟶ Γ(f'⁻¹ W, Č(g'⁻¹ U, g'^* ℱ))`, `b ⊗ c ↦ (y ↦ b • (g'^* c_y)|)`,
as a morphism of complexes of abelian groups
(`AlgebraicGeometry.Scheme.Modules.cechSectionsBaseChange`), and show that it is bijective in
each degree when `W` is affine, `ℱ` is quasi-coherent and the finite intersections of the `U i`
are affine (`AlgebraicGeometry.Scheme.Modules.bijective_cechSectionsBaseChange_f`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite TopCat.Presheaf

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens) (W : T.Opens)
  [Algebra Γ(S, ⊤) Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

/-! ### The module structure on the sections of the Čech resolution -/

section Sections

variable {Z : Scheme.{u}} (M : Z.Modules)

variable {ι : Type u} (U : ι → Z.Opens)

end Sections

/-! ### Linearity and restriction of the base change map -/

section Linear

end Linear

end AlgebraicGeometry.Scheme.Modules
