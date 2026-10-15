/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.AcyclicKFlatTensor
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse

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
    (hA : A.Acyclic) (hK : A.IsKFlat)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (R := R) (A.X i)) (n : ℤ) :
    SheafOfModules.IsFlat (R := R) (A.cycles n) := by
  sorry

end CochainComplex
