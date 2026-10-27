/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StackPointTopology
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Spectral.Basic

/-! # Closed specializations in finite-type algebraic stacks

Source: Stacks Project, stacks-morphisms.tex, Tags 06R6, 0DQI and 0DQQ;
Alper, Adequate moduli spaces, Lemma 8.3.1, printed p.39
(blueprint: lem-sfb-finite-type-stack-closed-specialization).

The point space is the existing field-object quotient with its smooth-atlas topology.
The diagonal hypothesis tests its actual algebraic-space base changes. No quasi-finiteness
or Deligne--Mumford condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A finite-type algebraic stack over a field with quasi-compact separated diagonal has
Noetherian sober point space, and each nonempty closed subset contains a closed point.
Source: Stacks Project, Tags 06R6, 0DQI and 0DQQ; Alper, Lemma 8.3.1, printed p.39
(blueprint: lem-sfb-finite-type-stack-closed-specialization).

Proof:
1. By def-sfb-stack-qcqs-morphism, choose a smooth surjective atlas U with U quasi-compact.
The chartwise finite-type hypothesis makes U locally of finite type over Spec k.
A field is Noetherian (def-weil-field, def-weil-pbc-noetherian-ring), so Spec k is locally
Noetherian (def-weil-affine-spectrum, pqf-def-locnoeth). Apply pqf-lem-locnoeth-lft to U;
its quasi-compactness now makes it a Noetherian scheme.
2. By lem-sfb-stack-point-topology the atlas point map is surjective and pulls closed sets
back to closed sets. For any nonempty family of closed subsets of the stack, apply
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal to their inverse images in U.
Surjectivity reflects strict inclusion, so a minimal inverse image gives a minimal member
of the original family. Thus the point space is Noetherian.
3. Apply lem-sfb-qc-stack-spectral-point-space over the affine base Spec k, using the
quasi-compactness of the stack and its diagonal. By def-weil-spectral-space a spectral
space is sober: every nonempty irreducible closed subset has a unique generic point.
Separatedness of the diagonal is not needed in this step.
4. In a nonempty closed C choose a minimal nonempty closed subset D by step 2.
For every y in D the closure of its singleton is nonempty, closed, and contained in D,
so equals D. It is irreducible, since y belongs to one member of any two-closed-set cover,
which must then contain its closure. Every point of D is therefore a generic point of D.
Sobriety makes all these points equal. Hence D is a closed singleton contained in C.
For the empty stack the last two quantified assertions are vacuous. -/
theorem finite_type_stack_closed_specialization (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F) (hqc : IsQuasiCompactModuli F)
    (hft : ∀ (U : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a → LocallyOfFiniteType U.hom)
    (hdiag : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T))
        (moduliTwoFiberProduct (moduliBaseStructure F) (moduliBaseStructure F))),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseStructure F)) T t Z p ∧
          AlgebraicSpace.MapIsQuasiCompact p ∧ AlgebraicSpace.MapToSchemeIsSeparated Z T p) :
    TopologicalSpace.NoetherianSpace (ModuliPoints F) ∧
      (∀ C : Set (ModuliPoints F), IsClosed C → IsIrreducible C →
        ∃! x : ModuliPoints F, IsGenericPoint x C) ∧
      (∀ C : Set (ModuliPoints F), IsClosed C → C.Nonempty →
        ∃ x ∈ C, IsClosed ({x} : Set (ModuliPoints F))) := by
  sorry

end CategoryTheory
