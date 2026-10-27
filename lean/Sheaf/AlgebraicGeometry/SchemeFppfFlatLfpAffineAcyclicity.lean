/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.AlgebraicGeometry.SchemeFppfEtaleModuleComparison
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.AffineSchemeFppfQCohAcyclic
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison

/-! # Affine fppf acyclicity under flat locally finitely presented comparisons

Source: Stacks Project, Descent, Tag 0756, with tau = etale and g = id;
Tags 03DW and 01XB for affine quasi-coherent vanishing.
(blueprint: lem-sfb-scheme-fppf-flat-lfp-affine-acyclicity).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A big-fppf structure-module sheaf on an affine scheme is acyclic if its small
etale restriction is associated to a quasi-coherent Zariski module and its canonical
small-etale pullback comparisons are invertible over flat locally finitely presented
schemes. The structure ring has its actual section rings in u, and module values
are in the common universe u+1 containing the site objects. Cohomology is derived
module evaluation, using injective module resolutions.

Source: Stacks Project, Descent, Tag 0756 (lemma-quasi-coherent-and-flat-base-change),
with tau = etale and g = id; Tags 03DW and 01XB
(blueprint: lem-sfb-scheme-fppf-flat-lfp-affine-acyclicity).

Proof:
1. Let A be the associated big-fppf module of M, using
   lem-sfb-scheme-big-fppf-quasicoherent-equivalence. Restrict the given etale
   isomorphism to opens to get M isomorphic to the Zariski restriction of G.
   By lem-sfb-big-fppf-zariski-ringed-comparison, A is its canonical tensor
   extension. The module adjunction lem-weil-pbc-ringed-topoi-module-adjunction
   transposes the open isomorphism to one morphism phi : A to G.
2. For every flat locally finitely presented g, restriction of phi to V_et is
   the composite of the Zariski/etale pullback comparison, pullback of the
   given isomorphism, and sfbFppfEtaleComparison g G. On sections both adjuncts
   send a tensor m to a times the restricted image of m. Thus the three maps
   are isomorphisms, by lem-trf-scheme-zariski-etale-quasi-coherent-equivalence
   and the hypothesis. In particular phi(V) is bijective on this class.
3. Set K = ker phi, I = im phi and C = coker phi. Kernels are sectionwise,
   so K(V) = 0 on the class. For C(V), lift a section locally through the
   quotient G to C. The exact forgetful functor and locally-surjective epi
   criterion give such lifts on an fppf cover. Flatness and local finite
   presentation compose, so each lifted section comes from A. Hence the
   original section is locally zero and therefore zero. Apply
   lem-sfb-fppf-flat-lfp-zero-cohomology to K and C at id U, in all degrees.
4. The common-universe module category has enough injectives by
   prop-pur-kinjective-resolutions-exist and lem-sp-grothendieck-enough-injectives.
   Global sections are additive and left exact because finite limits are
   sectionwise. Apply lem-weil-pbc-derived-functor-long-exact to
   0 to K to A to I to 0 and 0 to I to G to C to 0. Vanishing of K and C
   in all degrees identifies the derived sections of A and G, including degree zero.
5. Affine associated-module acyclicity follows from
   lem-sfb-affine-scheme-fppf-qcoh-acyclic and
   lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison. Therefore
   positive derived module sections of G vanish. No comparison outside the
   flat locally finitely presented class, or finiteness of M, was used. -/
theorem scheme_fppf_flat_lfp_affine_acyclicity (U : Scheme.{u}) [IsAffine U]
    (G : ringedSiteModules.{u + 1} (sfbFppfRings U))
    (M : U.Modules) [M.IsQuasicoherent]
    (_het : Nonempty ((sfbFppfEtaleRestriction U).obj G ≅
      (sfbZariskiEtaleExtension U).obj (sfbModuleULift M)))
    (_hcomp : ∀ (V : Scheme.{u}) (g : V ⟶ U),
      Flat g → LocallyOfFinitePresentation g → IsIso (sfbFppfEtaleComparison g G))
    (q : ℕ) (_hq : 0 < q) :
    IsZero (((sfbFppfModuleGlobalSections U).rightDerived q).obj G) := by
  sorry

end AlgebraicGeometry.Scheme
