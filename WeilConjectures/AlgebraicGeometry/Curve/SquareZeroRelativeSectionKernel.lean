/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroRelativeSectionKernelIdeal

/-! # Square-zero kernels of relative restriction on functions
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Products of functions vanishing on the smaller subscheme are zero. -/
theorem squareZeroRelativeSectionKernel (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) (hII : I * I ≤ J)
    (V : J.subscheme.Etaleᵒᵖ) (a b : J.subscheme.etaleStructurePresheaf.obj V)
    (ha : (etaleStructurePresheafToPullback (IdealSheafData.inclusion hJI)).app V a = 0)
    (hb : (etaleStructurePresheafToPullback (IdealSheafData.inclusion hJI)).app V b = 0) :
    a * b = 0 := by
  let f := (etaleStructurePresheafToPullback
    (IdealSheafData.inclusion hJI)).app V
  have ha' : a ∈ RingHom.ker f.hom := (RingHom.mem_ker).2 ha
  have hb' : b ∈ RingHom.ker f.hom := (RingHom.mem_ker).2 hb
  have hker := relativeSectionKernel_ker_mul_le_bot X I J hJI hII V
  have hab : a * b ∈ (⊥ : Ideal (J.subscheme.etaleStructurePresheaf.obj V)) :=
    (Ideal.mul_le.mp hker) a ha' b hb'
  simpa using hab

end AlgebraicGeometry.Scheme
