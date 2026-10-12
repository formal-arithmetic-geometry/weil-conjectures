/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Etale.Field
import Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise

/-! # Separable images of filtered etale fibres
Source: Stacks Project, More on Algebra, Tag 0AH1, final sentence.
(blueprint: lem-weil-pbc-filtered-etale-fiber-separable-image). -/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CommAlgCat

/-- Every element of a filtered etale fibre has separable image under a compatible
map to a field over the base residue field.
Source: Stacks Project, More on Algebra, Lemma Tag 0AH1, proof, final sentence.
(blueprint: lem-weil-pbc-filtered-etale-fiber-separable-image).

Proof:
1. Lift the given fibre element to a stage by the elementwise tensor-colimit lemma
   (Tags 00DD, 00D6, 00D7).
2. The stage fibre is a finite product of finite separable extensions of the base
   residue field: etaleness is preserved under base change and use Tag 00U3.
3. The composite stage map to the field has prime kernel. A prime of a finite
   product of fields is the kernel of exactly one projection, so the map factors
   through that factor as an injective field homomorphism.
4. Compatibility with the scalar map makes this embedding an algebra homomorphism.
   The lifted element is separable in its finite separable factor. The embedding
   preserves its minimal polynomial, so its image is separable too.
For an empty stage product there is no unital homomorphism to a field; this case
cannot supply a lift whose image lies in the specified target field. -/
theorem filteredEtale_fiber_image_isSeparable
    (A : Type u) [CommRing A]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommAlgCat.{v} A) [HasColimit D]
    (hD : ∀ i : I, Algebra.Etale A (D.obj i))
    (p : PrimeSpectrum A)
    (K : Type w) [Field K] [Algebra p.asIdeal.ResidueField K]
    (f : p.asIdeal.Fiber ↥(colimit D) →+* K)
    (hf : ∀ r : p.asIdeal.ResidueField,
      f (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber ↥(colimit D)) r) =
        algebraMap p.asIdeal.ResidueField K r)
    (x : p.asIdeal.Fiber ↥(colimit D)) :
    IsSeparable p.asIdeal.ResidueField (f x)  := by
  let κ := p.asIdeal.ResidueField
  let B := ↥(colimit D)
  let C := p.asIdeal.Fiber B
  let Ci (i : I) := p.asIdeal.Fiber ↥(D.obj i)
  let γ (i : I) : Ci i →ₐ[κ] C :=
    Algebra.TensorProduct.lTensor κ (colimit.ι D i).hom
  obtain ⟨hlift, _⟩ := filteredColimit_tensorProduct_elementwise A D κ
  have hlift' (x : C) : ∃ i : I, ∃ y : Ci i, γ i y = x := by
    obtain ⟨i, y, hy⟩ := hlift (Algebra.TensorProduct.comm A κ B x)
    refine ⟨i, Algebra.TensorProduct.comm A ↥(D.obj i) κ y, ?_⟩
    change LinearMap.lTensor κ (colimit.ι D i).hom.toLinearMap
      (_root_.TensorProduct.comm A ↥(D.obj i) κ y) = x
    rw [LinearMap.lTensor_comm, hy]
    exact (Algebra.TensorProduct.comm A κ B).symm_apply_apply x
  obtain ⟨i, y, rfl⟩ := hlift' x
  let fκ : C →ₐ[κ] K := { f with commutes' := hf }
  let g := fκ.comp (γ i)
  let P := RingHom.ker g.toRingHom
  let : P.IsPrime := RingHom.ker_isPrime g.toRingHom
  let : Algebra.Etale A ↥(D.obj i) := hD i
  let : Algebra.Etale κ (Ci i) := inferInstance
  let : Algebra.IsSeparable κ (Ci i ⧸ P) := inferInstance
  have hy := (Algebra.IsSeparable.isSeparable κ (Ideal.Quotient.mk P y)).map
    (Ideal.kerLiftAlg g) (Ideal.kerLiftAlg_injective g)
  change IsSeparable κ (g y) at hy
  exact hy

end CommAlgCat
