/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedCoherentModules
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentAbelian
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# An ideal sum inside a coherent module with reduced irreducible support

Source: Stacks Project, Spaces Cohomology, Tag 07UQ, lemma-prepare-filter-irreducible;
Tag 08AM, lemma-i-star-equivalence; Tags 07UB, 07UC, 07UD and 07UH
(blueprint: lem-sfb-space-reduced-support-generic-ideal-inclusion).

Coherence is finite presentation on the small etale ringed site, equivalent on locally
Noetherian spaces to quasi-coherence and coherence on every scheme chart (Tag 07UB).
The kernel ideal annihilates F exactly when each local scalar in the kernel of the
canonical structure map kills every local section of F. A finite direct sum and a
cokernel are specified by their universal properties in all module sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A coherent module annihilated by the ideal of its reduced irreducible support
contains the direct image of a positive finite sum of a nonzero full-support coherent
ideal, with coherent cokernel of strictly smaller support.

Source: Stacks Project, Spaces Cohomology, Tag 07UQ, lemma-prepare-filter-irreducible,
with Tags 08AM, 07UB, 07UC, 07UD and 07UH
(blueprint: lem-sfb-space-reduced-support-generic-ideal-inclusion).

Proof:
1. By lem-sfb-space-closed-coherent-modules, Z is Noetherian. The equivalence
   lem-sfb-space-closed-immersion-quasi-coherent-modules descends F, annihilated by
   the kernel ideal J, to a quasi-coherent G on Z with i_*G isomorphic to F. On affine
   etale charts of X the base-changed closed immersion is Spec(R/J) into Spec R.
   By lem-trf-space-etale-module-pushforward-restriction, the sections of G on
   Spec(R/J) are those of F on Spec R, so they are finite over R and over R/J.
   Use lem-sfb-space-qcoh-affine-chart-calculus, the Zariski/etale equivalence
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, and
   pqf-lem-coherent-ft-locnoeth to deduce coherence of G. The closed direct-image
   support formula and injectivity of the point map give full support on Z.
2. By lem-sfb-space-generic-freeness, G is free of rank r >= 1 on a nonempty open
   U of Z. Irreducibility makes U dense.
3. Give the complement its reduced closed structure by
   lem-sfb-space-reduced-closed-support. Its ideal I is quasi-coherent by
   lem-sfb-space-closed-immersion-quasi-coherent-modules and is the unit ideal on U.
   The structure module is coherent by lem-sfb-space-noetherian-coherent-support;
   its finite sum E is coherent by lem-sfb-space-coherent-abelian. Extend the chosen
   isomorphism E|_U to G|_U to beta : I^n E -> G using lem-sfb-space-homs-over-open.
4. Set K = I^n, including K = O_Z when n = 0. Chartwise powers are those of
   def-sbc-ideal-sheaf-powers and glue through the Zariski/etale equivalence.
   By lem-sfb-space-noetherian-coherent-support, K is coherent with closed support.
   Its restriction to dense nonempty U is O_U, so K is nonzero and has full support.
   Local products in each coordinate identify I^n E with the r-fold sum of K.
5. On an affine etale chart W of reduced Z, the inverse image W_U is dense by
   lem-a1-space-point-open-calculus. It is quasi-compact and quasi-separated since
   W is Noetherian. By lemma-nagata-reduced-dense-image-schematic and the kernel
   description in def-nagata-scheme-theoretic-image, O_W -> j_*O_(W_U) is injective.
   Every coordinate of a section in ker beta belongs to K inside O_W and vanishes
   on W_U, so is zero. The Zariski/etale equivalence and chart descent give Mono beta.
6. The cokernel C of beta is coherent by lem-sfb-space-coherent-abelian, and its
   support is closed by lem-sfb-space-noetherian-coherent-support. It vanishes on U,
   so its support is properly contained in |Z|.
7. The exact closed direct image of
   lem-sfb-space-closed-immersion-quasi-coherent-modules carries beta to the required
   alpha into F, with cokernel i_*C. By lem-sfb-space-closed-coherent-modules this
   cokernel is coherent and its support is the image of Supp C. Injectivity of |i|
   preserves the strict containment. Universal properties give the stated bicone
   and cokernel cofork. -/
theorem exists_reduced_support_generic_ideal_inclusion
    {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (i : Z ⟶ X)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hred : IsReduced Z) (hirr : IrreducibleSpace (Point Z.obj.obj))
    (F : X.Modules) (hF : F.IsFinitePresentation)
    (hJF : ∀ (T : X.EtaleSite) (a : X.structureSheaf.obj.obj (op T)),
      (moduleStructureMap i).val.app (op T) a = 0 →
        ∀ m : F.val.obj (op T), a • m = 0)
    (hsupp : moduleSupport F = pointImage i.hom.hom) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∃ K : Subobject (SheafOfModules.unit Z.structureSheaf),
        ¬ IsZero (K : Z.Modules) ∧
        SheafOfModules.IsFinitePresentation (K : Z.Modules) ∧
        moduleSupport (K : Z.Modules) = Set.univ ∧
        ∃ b : Bicone (fun _ : Fin r ↦ (K : Z.Modules)),
          Nonempty b.IsBilimit ∧
          ∃ α : (moduleDirectImage i).obj b.pt ⟶ F,
            Mono α ∧
            ∃ (Q : X.Modules) (q : F ⟶ Q) (w : α ≫ q = 0),
              Nonempty (IsColimit (CokernelCofork.ofπ q w)) ∧
              Q.IsFinitePresentation ∧ moduleSupport Q ⊂ pointImage i.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
