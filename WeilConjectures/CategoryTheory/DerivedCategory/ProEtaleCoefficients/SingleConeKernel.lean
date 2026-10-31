/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # The negative cohomology of a cone between degree-zero objects

Source: the cone calculation in the proof of `det-def-sfb-bounded-constructible`.
(blueprint: lem-sfb-single-cone-kernel)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- Complete a morphism between degree-zero objects to a distinguished triangle.
Its negative-first cohomology is the kernel of the original morphism.
Source: blueprint `det-def-sfb-bounded-constructible`, cone calculation.
(blueprint: lem-sfb-single-cone-kernel).

Proof: use the distinguished-cocone axiom on the single-functor image of the map.
In the long exact homology sequence, the preceding term is zero because the second
vertex is concentrated in degree zero.  Thus the connecting map is monic and exactness
identifies it with the kernel of the degree-zero homology map.  The natural isomorphism
from homology of a single object to that object identifies this map with the given map. -/
theorem exists_single_cone_kernel {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] {M N : A} (f : M ⟶ N) :
    ∃ T : Triangle (DerivedCategory A),
      T ∈ distTriang _ ∧ T.obj₁ = (singleFunctor A 0).obj M ∧
        T.obj₂ = (singleFunctor A 0).obj N ∧
          Nonempty ((homologyFunctor A (-1)).obj T.obj₃ ≅ kernel f) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle ((singleFunctor A 0).map f)
  let T := Triangle.mk ((singleFunctor A 0).map f) g h
  let δ := HomologySequence.δ T (-1) 0
  have hzero : (homologyFunctor A (-1)).map T.mor₂ = 0 :=
    (isZero_of_isGE ((singleFunctor A 0).obj N) 0 (-1) (by omega)).eq_of_src _ _
  have hδ : Mono δ :=
    (HomologySequence.exact₃ T hT (-1) 0).mono_g_iff.mpr hzero
  let S := ShortComplex.mk δ ((homologyFunctor A 0).map T.mor₁)
    (HomologySequence.δ_comp T hT (-1) 0)
  have hS : S.Exact := HomologySequence.exact₁ T hT (-1) 0
  let e : (homologyFunctor A (-1)).obj Z ≅
      kernel ((homologyFunctor A 0).map T.mor₁) :=
    hS.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  refine ⟨T, hT, rfl, rfl, ⟨e ≪≫ ?_⟩⟩
  exact kernel.mapIso _ f ((singleFunctorCompHomologyFunctorIso A 0).app M)
    ((singleFunctorCompHomologyFunctorIso A 0).app N)
    ((singleFunctorCompHomologyFunctorIso A 0).hom.naturality f)

end DerivedCategory
