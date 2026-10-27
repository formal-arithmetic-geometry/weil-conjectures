/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Closure kernels of products of distinct parameters

Source: ILO, Travaux de Gabber, VIII 4.1.8 and 4.2.9, pp. 118 and 121;
Stacks Project, Tags 080D, 01R8, 081I, 0AG0 and 00HD
(blueprint: lem-trf-parameter-product-closure-kernel).

The helper is the actual quotient-then-localization ring map. The geometric clauses
compare kernel ideal sheaves, so identify closed subschemes with their full scheme
structures: `Scheme.Hom.image` is the subscheme of this kernel ideal sheaf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.ParameterProductClosure

/-- The canonical map `R → (R/(f))[1/a]`, using the image of `a` in the quotient.
Source: Stacks Project, Section 00CM and Tag 080D
(blueprint: lem-trf-parameter-product-closure-kernel). -/
noncomputable def quotientAwayMap {R : Type u} [CommRing R] (a f : R) :
    R →+* Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) a) :=
  (algebraMap (R ⧸ Ideal.span {f})
    (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) a))).comp
      (Ideal.Quotient.mk (Ideal.span {f}))

/-- Parameter-product saturation, its local versions, and its preservation under every
flat extension. The indexed nonunits of `(a,z₁,…,zᵣ)` inject into positions of a regular
system of parameters at each prime. The equalities of kernel ideal sheaves state that
both scheme-theoretic closures are `V(P)`, respectively `V(P_E)`; they do not take radicals.
Source: ILO VIII 4.1.8 and 4.2.9; Stacks, Tags 080D, 01R8, 081I, 0AG0 and 00HD
(blueprint: lem-trf-parameter-product-closure-kernel).

Proof plan:
1. The fraction equivalence for the localization of `C/(f)` says that the class of `h`
   vanishes precisely when some `a^n*h` belongs to `(f)`. The quotient map has kernel `(f)`.
   This also gives the saturation formula over each prime localization; use
   def-weil-pbc-module-localization and def-weil-pbc-algebra-hom-quotient.
2. At a prime, move the selected nonunit parameters to the beginning of a parameter
   system. By lem-sfb-transverse-prime-ideal-parameters(b), the product ideal is the
   intersection of the distinct coordinate prime ideals `(z_j)`. The element `a` belongs
   to none of them: it is either a unit or a different coordinate parameter. Thus
   `a^n*h ∈ (f) ⊆ (P)` forces `h` into every `(z_j)`, hence into `(P)`. Conversely
   `h=P*v` gives `a^e*h=f*v`. An empty collection gives the unit ideal.
3. Apply lem-weil-pbc-ideal-membership-at-maximal-localizations to `(P)` to descend
   membership from all localizations. This gives `K=(P)`; extending it gives `KS=PS`,
   and step 2 identifies this with the saturation in `S`.
4. Tensor the exact sequence `0 → K → C → (C/(f))[1/a]` with the flat `C`-module `E`
   using lem-weil-pbc-flat-tensor-exact. The image of `E ⊗ K` in `E` is `KE`. Identify
   the tensor target with `(E/(f_E))[1/a_E]` by lem-weil-pbc-tensor-quotient-base-change
   and lem-weil-pbc-localization-base-change. On pure tensors the map sends `u ⊗ 1`
   to the class of `u`, so this is the specified canonical map. Now `KE=(P_E)`.
5. Maps of affine spectra are quasi-compact: inverse images of basic opens are affine,
   hence quasi-compact by lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact.
   Lem-weil-pbc-scheme-image-qc-kernel therefore identifies each scheme-theoretic image
   ideal with the computed ring kernel. By lem-weil-pbc-fibre-product-affine-spectra
   and the comparison in step 4, this also computes the ideal of the actual pullback
   immersion. Def-nagata-scheme-theoretic-image identifies these images with closures.
6. For `E=C ⊗[A] B₀`, lem-weil-pbc-flat-module-base-change supplies the flatness needed
   in step 4. Apply the result through the map `c ↦ c ⊗ 1`, as in the next clause.
-/
theorem parameter_product_closure_kernel
    {C : Type u} [CommRing C] [IsRegularRing C]
    (r : ℕ) (a : C) (z : Fin r → C) (e : ℕ) (he : 1 ≤ e)
    (P f : C) (hP : P = ∏ j, z j) (hf : f = a ^ e * P)
    (hparameters : ∀ (p : Ideal C) [p.IsPrime],
      ∃ t : List (Localization.AtPrime p),
        IsLocalRing.IsRegularSystemOfParameters t ∧
        ∃ ι : {i : Fin (r + 1) //
            ¬ IsUnit (algebraMap C (Localization.AtPrime p) (Fin.cases a z i))} ↪ Fin t.length,
          ∀ i, t.get (ι i) =
            algebraMap C (Localization.AtPrime p) (Fin.cases a z i.val)) :
    (RingHom.ker (quotientAwayMap a f) : Set C) =
      {h : C | ∃ n : ℕ, a ^ n * h ∈ Ideal.span {f}} ∧
    RingHom.ker (quotientAwayMap a f) = Ideal.span {P} ∧
    (Spec.map (CommRingCat.ofHom (quotientAwayMap a f))).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {P})))).ker ∧
    (∀ (p : Ideal C) [p.IsPrime],
      ((RingHom.ker (quotientAwayMap a f)).map
          (algebraMap C (Localization.AtPrime p)) : Set (Localization.AtPrime p)) =
        {h : Localization.AtPrime p | ∃ n : ℕ,
          (algebraMap C (Localization.AtPrime p) a) ^ n * h ∈
            Ideal.span {algebraMap C (Localization.AtPrime p) f}} ∧
      (RingHom.ker (quotientAwayMap a f)).map (algebraMap C (Localization.AtPrime p)) =
        Ideal.span {algebraMap C (Localization.AtPrime p) P}) ∧
    (∀ (E : Type u) [CommRing E] [Algebra C E] [Module.Flat C E],
      RingHom.ker (quotientAwayMap (algebraMap C E a) (algebraMap C E f)) =
        (RingHom.ker (quotientAwayMap a f)).map (algebraMap C E) ∧
      (RingHom.ker (quotientAwayMap a f)).map (algebraMap C E) =
        Ideal.span {algebraMap C E P} ∧
      (pullback.snd (Spec.map (CommRingCat.ofHom (quotientAwayMap a f)))
        (Spec.map (CommRingCat.ofHom (algebraMap C E)))).ker =
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (Ideal.span {algebraMap C E P})))).ker) ∧
    (∀ (A B₀ : Type u) [CommRing A] [CommRing B₀] [Algebra A C] [Algebra A B₀]
        [Module.Flat A B₀],
      RingHom.ker (quotientAwayMap
        (algebraMap C (C ⊗[A] B₀) a) (algebraMap C (C ⊗[A] B₀) f)) =
          (RingHom.ker (quotientAwayMap a f)).map (algebraMap C (C ⊗[A] B₀)) ∧
      (RingHom.ker (quotientAwayMap a f)).map (algebraMap C (C ⊗[A] B₀)) =
        Ideal.span {algebraMap C (C ⊗[A] B₀) P}) := by
  sorry

end AlgebraicGeometry.ParameterProductClosure
