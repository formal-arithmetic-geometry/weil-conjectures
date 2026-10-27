/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.AlgebraicGeometry.ResidueField

import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedPushforwardStalks
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Global functions separating disjoint closed subsets

Source: Stacks Project, Spaces Cohomology, Tag 07V1
(lemma-vanishing-separate-closed), in Situation 07UY
(blueprint: lem-sfb-space-h1-separate-disjoint-closed).

Global functions are Mathlib's compatible sections of the existing structure presheaf.
The two zero loci are expressed on all etale charts by residue-field evaluation.
The underlying additive sheaf is canonically lifted to universe u+1 before taking
cohomology, so Mathlib's sheafification and standard Ext construction apply without
any additional hypotheses on the space or on choices of cohomology infrastructure.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace
/-- Vanishing first quasi-coherent cohomology separates any two disjoint closed subsets.
Source: Stacks Project, Spaces Cohomology, Tag 07V1, in Situation 07UY
(blueprint: lem-sfb-space-h1-separate-disjoint-closed).

The conditions on every etale chart are exactly Z0 contained in V(a) and Z1 contained
in V(a-1): chart points give residue-field representatives, and all point classes lift
to an etale atlas. Evaluation commutes with field extension, whose injectivity makes
vanishing independent of the representative. The canonical ULift of the additive sheaf
changes only its carrier universe. HasExt.standard fixes the standard Ext realization.

Proof:
1. If Z0 is empty choose a=1; if Z1 is empty choose a=0. This includes empty X.
2. Give each Zj its reduced closed subspace structure
   (lem-sfb-space-reduced-closed-support). Its closed inclusion ij has quasi-coherent
   direct image Qj of the structure module and a surjective quotient qj: O_X -> Qj
   (lem-sfb-space-closed-immersion-quasi-coherent-modules). The structure module itself
   is quasi-coherent, with its one-generator, zero-relations presentation
   (def-trf-space-quasi-coherent-module).
3. Form r=(q0,q1): O_X -> Q0 directSum Q1. At any geometric point at most one target
   stalk is nonzero (lem-sfb-space-closed-pushforward-geometric-stalks). Hence the stalk
   map is surjective. Geometric points preserve finite products and epimorphisms and
   detect epimorphisms (lem-sfb-space-etale-conservative-geometric-points), so r is onto.
4. Its target N and kernel K are quasi-coherent (lem-sfb-space-qcoh-kernels-colimits).
   Kernels are sectionwise (def-weil-sheaf-of-modules-category), so this is also a
   short exact sequence of underlying additive sheaves. The hypothesis gives H1(K)=0.
5. Abelian sheaves have enough injectives (lem-weil-pbc-site-sheaves-enough-injectives).
   Global sections are additive and left exact, as compatible families with
   componentwise operations. The derived long exact sequence
   (lem-weil-pbc-derived-functor-long-exact), with its canonical degree-zero
   identification (lem-weil-pbc-left-exact-injective-resolution-degree-zero), makes
   Gamma(O_X) -> Gamma(N) surjective. Apply it after the same canonical coefficient lift.
6. The compatible zero and unit sections on the two closed subspaces give the section
   (0,1) of N via the chart-limit direct image (def-trf-space-etale-module-functors).
   Lift it to a global function a. Its two restrictions are respectively zero and one.
7. A field-valued representative in Zj factors through its reduced closed subspace:
   its base change is a nonempty closed subscheme of a field spectrum, hence the whole
   spectrum (lem-sfb-space-reduced-closed-support and def-weil-closed-immersion).
   Evaluating the restrictions proves the two displayed conditions. Compatibility
   with extension of fields and injectivity of field embeddings prove independence
   of representatives and the equivalent etale-chart formulation. -/
theorem exists_global_function_separating_closed
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (hH : ∀ (F : X.Modules) (_ : F.IsQuasicoherent),
      Subsingleton (@Sheaf.H _ _ _
        ((sheafCompose X.etaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          ((SheafOfModules.toSheaf X.structureSheaf).obj F))
        inferInstance (HasExt.standard _) 1))
    (Z₀ Z₁ : Set (Point X.obj.obj))
    (hZ₀ : IsClosed Z₀) (hZ₁ : IsClosed Z₁) (hdisj : Disjoint Z₀ Z₁) :
    ∃ a : RingCat.sectionsSubring X.structurePresheaf,
      (∀ (T : X.EtaleSite) (x : X.etaleForget.obj T),
        schemePointMap T.obj.hom x ∈ Z₀ →
          (X.etaleForget.obj T).Γevaluation x (a.val (op T)) = 0) ∧
      (∀ (T : X.EtaleSite) (x : X.etaleForget.obj T),
        schemePointMap T.obj.hom x ∈ Z₁ →
          (X.etaleForget.obj T).Γevaluation x ((a - 1).val (op T)) = 0) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
