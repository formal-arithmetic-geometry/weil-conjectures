/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Topology.Sheaves.Stalks

/-!
# Coherent ideal filtrations on Noetherian algebraic spaces

Source: Stacks Project, Spaces Cohomology, Tag 07UR, lemma-coherent-filter, with zero
factors omitted and the support control from its proof and Tag 07UQ
(blueprint: lem-sfb-space-coherent-ideal-filtration).

On locally Noetherian etale charts, finite presentation is equivalent to coherence
(Tag 07UB). We use Mathlib's existing predicate rather than introduce a second one.
Quasi-separatedness is tested by quasi-compact fibre products of pairs of affine schemes.
The quotients below are cokernels in all module sheaves, specified by their universal
property. This avoids requiring any additional choice of a sheafification functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every coherent module has a finite filtration with nonzero coherent ideal factors
on reduced irreducible closed subspaces, with support control.
Source: Stacks Project, Spaces Cohomology, Tag 07UR, lemma-coherent-filter, and Tag 07UQ
(blueprint: lem-sfb-space-coherent-ideal-filtration).

Proof:
1. Filtrations concatenate across a coherent short exact sequence: use the submodule
   filtration first, then inverse images of the quotient filtration. These inverse
   images are kernels and hence coherent by lem-sfb-space-coherent-abelian; their
   successive quotients are the original quotient factors by exactness.
2. Restrict to etale charts by lem-weil-pbc-site-restriction-exact and use
   lem-sfb-scheme-etale-module-exact-finiteness-comparison and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence. Coherent Zariski kernels
   and cokernels are given by lem-weil-pbc-coherent-kernel-cokernel-locnoeth.
   Exact stalks (lem-weil-pbc-module-stalk-exact) and lem-sfb-space-etale-chart-support
   put subquotient supports inside the original support. Empty support implies zero
   by lem-weil-pbc-module-iso-on-stalks and descent. Coherent supports are closed by
   lem-sfb-space-noetherian-coherent-support.
3. Induct on closed supports using lem-sfb-noetherian-space-topology, simultaneously
   for all coherent modules with the given support. The empty case has length zero.
   For reducible support apply lem-sfb-space-coherent-support-union-sequence and
   concatenate the two filtrations on strictly smaller closed supports.
4. For irreducible support give it its reduced closed structure using
   lem-sfb-space-reduced-closed-support. Its ideal J is quasi-coherent by
   lem-sfb-space-closed-immersion-quasi-coherent-modules. By
   lem-sfb-space-coherent-support-ideal-power, some J^n annihilates the module.
   Its coherent successive J-adic quotients are annihilated by J.
5. Apply induction to layers with smaller support. For a full-support layer use
   lem-sfb-space-reduced-support-generic-ideal-inclusion: a finite positive sum of
   a nonzero full-support coherent ideal embeds with coherent smaller-support cokernel.
6. Filter that ideal sum by coordinate sums. Closed direct image is exact by
   lem-sfb-space-closed-immersion-quasi-coherent-modules; the resulting factors are
   single ideal direct images. Coherence and their exact supports follow from
   lem-sfb-space-closed-coherent-modules. Concatenate with the cokernel filtration.
7. Refine the finite J-adic filtration by these layer filtrations, omitting repeated
   terms. Every resulting factor is nonzero with the asserted support, and all
   supports remain inside the original support by step 2. -/
theorem exists_coherent_ideal_filtration
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (F : X.Modules) (hF : F.IsFinitePresentation) :
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c),
      IsZero (c 0 : X.Modules) ∧ IsIso (c (Fin.last m)).arrow ∧
      (∀ k : Fin (m + 1), SheafOfModules.IsFinitePresentation (c k : X.Modules)) ∧
      (∀ j : Fin m, ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
        (∀ T : Z.EtaleSite, IsReduced (Z.etaleForget.obj T)) ∧
        IrreducibleSpace (Point Z.obj.obj) ∧
        ∃ K : Subobject (SheafOfModules.unit Z.structureSheaf),
          ¬ IsZero (K : Z.Modules) ∧
          SheafOfModules.IsFinitePresentation (K : Z.Modules) ∧
          moduleSupport (K : Z.Modules) = Set.univ ∧
          ∃ (Q : X.Modules) (q : (c j.succ : X.Modules) ⟶ Q)
            (w : Subobject.ofLE (c j.castSucc) (c j.succ)
              (hc j.castSucc_le_succ) ≫ q = 0),
            Nonempty (IsColimit (CokernelCofork.ofπ q w)) ∧
            Nonempty (Q ≅ (moduleDirectImage i).obj (K : Z.Modules)) ∧
            pointImage i.hom.hom = moduleSupport Q ∧
            moduleSupport Q ⊆ moduleSupport F) ∧
      (moduleSupport F = ∅ → m = 0 ∧ IsZero F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
