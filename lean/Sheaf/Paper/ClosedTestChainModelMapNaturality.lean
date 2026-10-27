/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.ClosedTestScalarModelDiagrams

/-! # Naturality of chain restriction for supplied closed-test models
Source: Stacks Tags 070I and 070Y
(blueprint: lem-sfb-closed-test-chain-model-map-naturality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
open ClosedTestKInjectiveSectionModels
variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ]

/-- The chain-restriction square for two independently supplied resolutions.
Source: Stacks derived.tex Tags 070I and 070Y; parent proof step 8
(blueprint: lem-sfb-closed-test-chain-model-map-naturality).
Proof: rightDerivedPullback_app_Q_obj computes the derived section arrow on M.I
followed by the image of M.j as the section-unit chain map followed by j.
Naturality at M.e.hom and the defining formula for M.pullIso therefore express
chainRestriction as the source computation unit, evaluation of M.e.hom,
derivedSectionArrow at K, evaluation of M.pullIso.inv, and the target inverse
computation unit. The same formula holds for P. Expand modelMap on both sides
of the requested square. Since the supplied complexes are K-injective, their
computation units are inverse computation isomorphisms. Cancel these adjacent
isomorphisms and the adjacent representative isomorphisms. Functoriality combines
the remaining factors into evaluation of alpha and of its exact pullback.
Naturality of derivedSectionArrow at alpha is precisely the remaining equality.
This works for arbitrary unbounded objects and all choices of resolutions; it
uses no exactness of section evaluation and inverts no scalar comparison. -/
theorem closed_test_chain_model_map_naturality
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    {K N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (α : K ⟶ N) (M : TestModel Λ h K) (P : TestModel Λ h N) :
    chainRestriction Λ A a w V M.I M.J M.j ≫
        modelMap Λ (testFibre fZ (closedTest A a V)) M.J P.J M.pullIso P.pullIso
          ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α) =
      modelMap Λ (testFibre f (liftedTest A a V)) M.I P.I M.e P.e α ≫
        chainRestriction Λ A a w V P.I P.J P.j := by sorry

end AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
