/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Algebra.Homology.AcyclicKFlatTensor
import Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion
import Mathlib.Algebra.Homology.HomologySequence

/-!
# Flat cycles of an acyclic K-flat complex

Source: Stacks Project, Cohomology on Sites, Tag 0G7C,
Lemma `sites-cohomology-lemma-K-flat-flat-acyclic`
(blueprint: lem-weil-pbc-site-acyclic-kflat-cycles-flat).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex

/-- Cycles of an acyclic K-flat complex with flat terms are flat.
Source: Stacks Project, Cohomology on Sites, Tag 0G7C
(blueprint: lem-weil-pbc-site-acyclic-kflat-cycles-flat).

Proof: Fix n and a sheaf N. The universal tensor acyclicity lemma
`lem-pur-acyclic-kflat-tensor-arbitrary` applied to N concentrated in degree zero
makes the ordinary tensor complex N tensor A acyclic, in particular exact at n - 2.
The total tensor construction `def-pc-tensor-complex-sheaves` identifies its terms
and differentials with N tensor A^i and 1 tensor d^i. The flat-opcycles criterion
`lem-weil-pbc-site-flat-opcycles-tor-criterion` at n - 1 now makes A.opcycles (n - 1)
flat, since all terms of A are flat. Acyclicity identifies this cokernel with
A.cycles n: the kernel of d^(n-1) is the image of d^(n-2), and the image of d^(n-1)
is the kernel of d^n. Tensoring this isomorphism identifies the two tensor functors;
exactness for the opcycles therefore gives flatness of the cycles. -/
theorem isFlat_cycles_of_acyclic_isKFlat
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (A : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hA : A.Acyclic) (hK : A.IsAcyclicTensorKFlat)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (R := R) (A.X i)) (n : ℤ) :
    SheafOfModules.IsFlat (R := R) (A.cycles n) := by
  let := SheafOfModules.monoidalCategory R
  have hop : SheafOfModules.IsFlat (R := R) (A.opcycles (n - 1)) := by
    apply SheafOfModules.isFlat_opcycles_of_universal_tensor_exactAt R A hflat (n - 1)
    intro N
    exact SheafOfModules.tensor_acyclic_of_isKFlat A hK hA
      ((CochainComplex.singleFunctor _ 0).obj N) ((n - 1) - 1)
  -- Exactness in the two adjacent degrees makes the induced differential an isomorphism.
  have hm : Mono (A.fromOpcycles (n - 1) n) := by
    have hm' : Mono (A.fromOpcycles (n - 1) ((ComplexShape.up ℤ).next (n - 1))) := by
      have hf : A.fromOpcycles (n - 1) ((ComplexShape.up ℤ).next (n - 1)) =
          (A.sc (n - 1)).fromOpcycles := by
        apply (cancel_epi (A.pOpcycles (n - 1))).1
        rw [A.p_fromOpcycles]
        exact (A.sc (n - 1)).p_fromOpcycles.symm
      rw [hf]
      exact (hA (n - 1)).mono_fromOpcycles
    have hn : (ComplexShape.up ℤ).next (n - 1) = n := by simp
    exact Eq.mp (congrArg (fun j : ℤ ↦ Mono (A.fromOpcycles (n - 1) j)) hn) hm'
  have he : Epi (A.toCycles (n - 1) n) := by
    have he' : Epi (A.toCycles ((ComplexShape.up ℤ).prev n) n) := by
      have hf : A.toCycles ((ComplexShape.up ℤ).prev n) n = (A.sc n).toCycles := by
        apply (cancel_mono (A.iCycles n)).1
        rw [A.toCycles_i]
        exact (A.sc n).toCycles_i.symm
      rw [hf]
      exact (hA n).epi_toCycles
    have hn : (ComplexShape.up ℤ).prev n = n - 1 := by simp
    exact hn ▸ he'
  have : Mono (A.opcyclesToCycles (n - 1) n) :=
    mono_of_mono_fac (A.opcyclesToCycles_iCycles (n - 1) n)
  have : Epi (A.opcyclesToCycles (n - 1) n) :=
    epi_of_epi_fac (A.pOpcycles_opcyclesToCycles (n - 1) n)
  have : IsIso (A.opcyclesToCycles (n - 1) n) := isIso_of_mono_of_epi _
  exact (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.curriedTensor _).flip.mapIso (asIso (A.opcyclesToCycles (n - 1) n))) hop

end CochainComplex
