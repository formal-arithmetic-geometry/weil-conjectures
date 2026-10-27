/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree
import Sheaf.Topology.ClosedPushforwardBoundaryNaturality
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-! # Linear cohomology sequence for a closed-immersion cokernel

Source: Stacks Project, Tag 0BYD, proof of `lemma-genus-plane-curve`, with the
arbitrary-module comparison of Tags 03FD and 02UV and the module-valued long exact
sequence of Tags 01DZ, 015B and 05TE
(blueprint: lem-sfb-closed-immersion-cokernel-cohomology).

The helpers are the incoming arrow and the specified connecting arrow of this sequence.
All cohomology objects are the recorded right-derived module cohomology with restricted
base-field scalars. The comparison is pinned to the canonical cohomology edge map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

/-- The incoming map `c^q H^q(u)`, as a linear map over the base field.
Source: Stacks, Tag 0BYD, the first map displayed after the long exact sequence
(blueprint: lem-sfb-closed-immersion-cokernel-cohomology). -/
def closedImmersionCokernelArrow (i : Y ⟶ X) {E : X.Modules} {M : Y.Modules}
    (u : E ⟶ (pushforward i).obj M) (q : ℕ)
    (c : scalarCohomology (X ↘ Spec (.of k)) ((pushforward i).obj M) q ≃ₗ[k]
      scalarCohomology (Y ↘ Spec (.of k)) M q) :
    scalarCohomology (X ↘ Spec (.of k)) E q →ₗ[k]
      scalarCohomology (Y ↘ Spec (.of k)) M q :=
  c.toLinearMap.comp
    (((ModuleCat.restrictScalars (scalarMap (X ↘ Spec (.of k)) ⊤)).map
      ((RingedSpace.moduleCohomology X.toRingedSpace q).map u)).hom)

/-- The specified module boundary composed with `(c^q)⁻¹`, restricting its scalars to k.
The standard derived categories fix sizes without an additional mathematical hypothesis.
Source: Stacks, Tags 0BYD and 01DZ
(blueprint: lem-sfb-closed-immersion-cokernel-cohomology). -/
def closedImmersionCokernelBoundary (i : Y ⟶ X) {L E : X.Modules} {M : Y.Modules}
    (f : L ⟶ E) (u : E ⟶ (pushforward i).obj M) (w : f ≫ u = 0)
    (hS : (ShortComplex.mk f u w).ShortExact) (q : ℕ)
    (c : scalarCohomology (X ↘ Spec (.of k)) ((pushforward i).obj M) q ≃ₗ[k]
      scalarCohomology (Y ↘ Spec (.of k)) M q) :
    scalarCohomology (Y ↘ Spec (.of k)) M q →ₗ[k]
      scalarCohomology (X ↘ Spec (.of k)) L (q + 1) :=
  (((ModuleCat.restrictScalars (scalarMap (X ↘ Spec (.of k)) ⊤)).map
    (@RingedSpace.moduleCohomologyBoundary X.toRingedSpace
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      (ShortComplex.mk f u w) hS q)).hom).comp c.symm.toLinearMap

/-- Closed-immersion comparison and its entire linear cokernel cohomology sequence.
The comparison is the canonical edge map, is natural in M, and is normalized on sections.
Exactness is stated at all three positions of each repeated segment, including the
initial injection. The last implication states that the two specified linear arrows
are bijective, equivalently linear isomorphisms.

Source: Stacks, Tag 0BYD, proof of `lemma-genus-plane-curve`; Tags 03FD, 02UV, 01DZ,
015B and 05TE (blueprint: lem-sfb-closed-immersion-cokernel-cohomology).

Proof:
1. Forget the modules to abelian sheaves. The natural comparisons of
   lem-sc-zariski-module-abelian-cohomology-agree on X and Y and the normalized
   closed-pushforward comparison of lem-sc-closed-pushforward-boundary-naturality
   give c, normalized by the identity on sections. This is the canonical edge map.
2. Multiplication by any element of k commutes with pushforward since i is over k.
   Naturality and lem-weil-pbc-module-cohomology-scalar-endomorphism show that c
   commutes with these scalars, so both c and its inverse are k-linear.
3. The module-sheaf category is abelian with enough injectives by
   lem-sc-ringed-space-module-sheaves-enough-injectives. Global sections is additive
   and left exact, since kernels are sectionwise. Apply
   lem-weil-pbc-right-derived-universal-delta-functor to the specified sequence.
   Its boundaries are def-sc-module-cohomology-boundary. Restrict scalars to k;
   this preserves the underlying groups, kernels, images and exactness.
4. Transport each third term through c. The incoming map is c H(u), and the outgoing
   map is the specified boundary composed with c inverse. Isomorphisms preserve
   images and kernels. With the four vanishings, the relevant segments have zero
   outer terms, so the incoming degree-zero map and the degree-one boundary are
   bijective linear maps. -/
theorem closedImmersion_cokernel_cohomology (i : Y ⟶ X)
    [IsClosedImmersion i] [i.IsOver (Spec (.of k))] :
    ∃ c : ∀ (q : ℕ) (M : Y.Modules),
      scalarCohomology (X ↘ Spec (.of k)) ((pushforward i).obj M) q ≃ₗ[k]
        scalarCohomology (Y ↘ Spec (.of k)) M q,
      (∀ (q : ℕ) (M : Y.Modules)
        (x : scalarCohomology (X ↘ Spec (.of k)) ((pushforward i).obj M) q),
        c q M x = moduleCohomologyEdgeMap i M q x) ∧
      (∀ (q : ℕ) (M N : Y.Modules) (a : M ⟶ N)
        (x : scalarCohomology (X ↘ Spec (.of k)) ((pushforward i).obj M) q),
        c q N (scalarCohomologyMap (X ↘ Spec (.of k)) ((pushforward i).map a) q x) =
          scalarCohomologyMap (Y ↘ Spec (.of k)) a q (c q M x)) ∧
      (∀ (M : Y.Modules) (s : ((pushforward i).obj M).val.obj (op ⊤)),
        c 0 M ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
            ((pushforward i).obj M) s) =
          (RingedSpace.globalSectionsFunctor Y.toRingedSpace).toRightDerivedZero.app M
            (M.val.map (homOfLE (by simp : ⊤ ≤ i ⁻¹ᵁ ⊤)).op s)) ∧
      (∀ (L E : X.Modules) (M : Y.Modules) (f : L ⟶ E)
        (u : E ⟶ (pushforward i).obj M) (w : f ≫ u = 0)
        (hS : (ShortComplex.mk f u w).ShortExact),
        Function.Injective (scalarCohomologyMap (X ↘ Spec (.of k)) f 0) ∧
        (∀ q : ℕ,
          Function.Exact (scalarCohomologyMap (X ↘ Spec (.of k)) f q)
            (closedImmersionCokernelArrow i u q (c q M)) ∧
          Function.Exact (closedImmersionCokernelArrow i u q (c q M))
            (closedImmersionCokernelBoundary i f u w hS q (c q M)) ∧
          Function.Exact (closedImmersionCokernelBoundary i f u w hS q (c q M))
            (scalarCohomologyMap (X ↘ Spec (.of k)) f (q + 1))) ∧
        ((IsZero (scalarCohomology (X ↘ Spec (.of k)) L 0) ∧
          IsZero (scalarCohomology (X ↘ Spec (.of k)) L 1) ∧
          IsZero (scalarCohomology (X ↘ Spec (.of k)) E 1) ∧
          IsZero (scalarCohomology (X ↘ Spec (.of k)) E 2)) →
          Function.Bijective (closedImmersionCokernelArrow i u 0 (c 0 M)) ∧
          Function.Bijective (closedImmersionCokernelBoundary i f u w hS 1 (c 1 M)))) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
