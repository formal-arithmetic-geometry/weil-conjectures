/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-!
# The product-of-sections immersion criterion

The geometric chart argument in Stacks Project, Varieties, Tag 0FD5.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

/-- Suppose the ideal twist in degree `n-r` is globally generated, and the power in degree
`r` is very ample. Any finite linear system in degree `n` containing the restriction kernel
and generating on the complement defines an immersion there.

Source: Stacks Project, varieties.tex, Tag 0FD5, proof of lemma-generate-over-complement,
from “Say L to the power n₂ is very ample” through the final affine-chart argument.
(blueprint: lem-zl-bertini-product-system-immersion).

Proof: Write U for the complement of Z. At x in U choose an ideal-twist generator a nonzero
at x, and a coordinate t_j of the very ample embedding nonzero at x. Multiplication under
L^(n-r) tensor L^r = L^n gives products a*t_l vanishing on Z; they are therefore constant
linear combinations of the chosen system. The product a*t_j is nonzero at x. On the target
open where its corresponding linear form is nonzero, the ratios (a*t_l)/(a*t_j) define a
morphism to the j-th affine chart of the fixed very ample projective space. Pulling back
these ratios cancels a, so the composite is the restriction of the fixed closed immersion.
Immersion cancellation proves the original morphism an immersion over this target open.
The opens so obtained cover its image, so target locality for immersions finishes. This
argument also handles an empty complement: the family covers its empty image. -/
theorem vanishing_linear_system_isImmersion
    (k : Type u) [Field k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (L : Y.Modules) [L.IsInvertible] (n r : ℕ) (hrn : r ≤ n)
    (hvery : IsVeryAmple (Y ↘ Spec (.of k)) (L.tensorPow r))
    (σ : SheafOfModules.GeneratingSections
      (i.ker.toModules ⊗ₘ L.tensorPow (n - r))) :
    letI : Module k Γ(L.tensorPow n, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Y ↘ Spec (CommRingCat.of k)).appTop).hom
    ∀ (I : Type u) [Finite I] (s : I → (L.tensorPow n).sections)
      (t : I → ((Scheme.Modules.pullback
        (show Y.Opens from i.ker.support.compl).ι).obj (L.tensorPow n)).sections)
      (hspan : ∀ v : Γ(L.tensorPow n, ⊤), pullbackΓ i (L.tensorPow n) v = 0 →
        v ∈ Submodule.span k
          (Set.range (fun j ↦ (s j).val (op ⊤)) : Set Γ(L.tensorPow n, ⊤)))
      (hvalue : ∀ j, (t j).val (op ⊤) = pullbackΓ
        (show Y.Opens from i.ker.support.compl).ι (L.tensorPow n) ((s j).val (op ⊤)))
      (ht : Epi ((SheafOfModules.freeHomEquiv ((Scheme.Modules.pullback
        (show Y.Opens from i.ker.support.compl).ι).obj (L.tensorPow n))).symm t)),
      IsImmersion (@ProjectiveSpace.homOfGeneratingSections I _
        (show Y.Opens from i.ker.support.compl).toScheme (Spec (.of k))
        ((show Y.Opens from i.ker.support.compl).ι ≫ (Y ↘ Spec (.of k)))
        ((Scheme.Modules.pullback
          (show Y.Opens from i.ker.support.compl).ι).obj (L.tensorPow n))
        inferInstance t ht) := by
  sorry

end AlgebraicGeometry
