/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic

import WeilConjectures.RingTheory.FlatModuleTensorModel
import WeilConjectures.RingTheory.FpModuleTensorModelComparison

/-!
# Eventual flatness for finitely presented modules over affine inverse limits

## References

* Stacks Project, Tag 02JO
-/

@[expose] public section

universe v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A finitely presented module whose base change to the limit ring is flat is already flat
after base change to every sufficiently late stage (Stacks, Tag 02JO). -/
theorem exists_eventually_flat_of_finitePresentation
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    (F : I ⥤ CommRingCat.{v}) (c : Cocone F) (hc : IsColimit c)
    {i : I} {Ai Bi Ni : Type w}
    [CommRing Ai] [CommRing Bi] [AddCommMonoid Ni]
    [Algebra (F.obj i : Type v) Ai] [Algebra (F.obj i : Type v) Bi]
    [Module Bi Ni] [Module.FinitePresentation Bi Ni]
    [Algebra.FinitePresentation (F.obj i : Type v) Ai]
    [Algebra.FinitePresentation (F.obj i : Type v) Bi]
    (f : Ai →ₐ[(F.obj i : Type v)] Bi)
    (hflat : letI : Module Ai Ni := Module.compHom Ni f.toRingHom
      letI : Algebra (F.obj i : Type v) (c.pt : Type v) :=
        (c.ι.app i).hom.toAlgebra
      letI : Algebra Ai ((c.pt : Type v) ⊗[(F.obj i : Type v)] Ai) :=
        Algebra.TensorProduct.rightAlgebra
      Module.Flat ((c.pt : Type v) ⊗[(F.obj i : Type v)] Ai)
        (((c.pt : Type v) ⊗[(F.obj i : Type v)] Ai) ⊗[Ai] Ni)) :
    (letI : Module Ai Ni := Module.compHom Ni f.toRingHom;
    ∃ j₀ : I, i ≤ j₀ ∧
      ∀ (j : I) (h₀ : i ≤ j₀) (h₁ : j₀ ≤ j),
        (letI : Algebra (F.obj i : Type v) (F.obj j : Type v) :=
        (F.map (homOfLE (h₀.trans h₁))).hom.toAlgebra;
          letI : Algebra Ai ((F.obj j : Type v) ⊗[(F.obj i : Type v)] Ai) :=
            Algebra.TensorProduct.rightAlgebra;
          Module.Flat ((F.obj j : Type v) ⊗[(F.obj i : Type v)] Ai)
            (((F.obj j : Type v) ⊗[(F.obj i : Type v)] Ai) ⊗[Ai] Ni))) := by
  let : Algebra (F.obj i : Type v) (c.pt : Type v) :=
    (c.ι.app i).hom.toAlgebra
  obtain ⟨P, Q, L, cP, cQ, aPQ, cL, mQL, aP, hP, hQ, hL, hPL, e, he, eM⟩ :=
    exists_flat_module_tensor_model (C := (c.pt : Type v)) f hflat
  let : CommRing P := cP
  let : CommRing Q := cQ
  let : Algebra P Q := aPQ
  let : AddCommMonoid L := cL
  let : Module Q L := mQL
  let : Algebra.FinitePresentation ℤ P := hP
  let : Algebra.FinitePresentation P Q := hQ
  let : Module.FinitePresentation Q L := hL
  obtain ⟨j₀, hi, hmodel⟩ :=
    exists_eventually_tensor_model_equiv F c hc f P Q L aP e he eM
  let : Module Ai Ni := Module.compHom Ni f.toRingHom
  let : Module P L := Module.compHom L (algebraMap P Q)
  have : Module.Flat P L := hPL
  refine ⟨j₀, hi, ?_⟩
  intro j h₀ h₁
  let : Algebra (F.obj i : Type v) (F.obj j : Type v) :=
    (F.map (homOfLE (h₀.trans h₁))).hom.toAlgebra
  let : Algebra Ai ((F.obj j : Type v) ⊗[F.obj i] Ai) :=
    Algebra.TensorProduct.rightAlgebra
  obtain ⟨aPj, ⟨ej⟩⟩ := hmodel j h₀ h₁
  let := aPj
  exact Module.Flat.of_linearEquiv ej.symm

end AlgebraicGeometry
