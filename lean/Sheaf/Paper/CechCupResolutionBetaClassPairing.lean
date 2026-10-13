/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechCupProduct

/-! # The augmentation axis of the signed total Cech pairing

Source: Stacks Project, Tags 07MB and 0FKV.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The augmentation axis computes the already characterized sheaf cup product.
Source: Stacks Project, Tag 07MB and Tag 0FKV, final comparison diagram.
(blueprint: lem-sc-cech-cup-resolution-beta-class-pairing)

Proof: form the signed Alexander--Whitney total pairing using D.pair on each
resolution/Cech summand, with sign (-1)^(i*s) for Cech degree i of the first
factor and resolution degree s of the second. Restriction compatibility and
D.leibniz give the cochain identity; the Cech differential cancels adjacent
omitted-vertex terms. Bilinearity and this identity give quotient descent to
homology. The alpha components lie in Cech degree zero, so their signs are one;
the resulting product is the D.pair product of global resolution cycles.
A.alpha_quasiIso and B.alpha_quasiIso let every total homology input be lifted
to a global resolution cycle. The alpha_class equations identify its class
with the inverse of A.iso or B.iso. The characterization hcup therefore
identifies the total pairing with cup transported along A.iso, B.iso, C.iso.
The beta components lie in resolution degree zero. Here the signs are also
one, and D.augmentation_pair identifies their product with the augmentation
of cechCupCochain. The beta_f equations identify these components with the
specified beta maps. Apply homology and then C.iso.inv to this beta equality.
This calculation is sectionwise and does not require a covering hypothesis:
the needed global comparison isomorphisms are explicitly part of A and B.
If an index set or an input is empty or zero, bilinearity gives the same formula.
The statement fixes cup by hcup, rather than asserting the formula for an
arbitrary bilinear map. -/
theorem cupCechResolution_beta_class_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (A : CupCechResolutionComparison U D.left)
    (B : CupCechResolutionComparison U D.right)
    (C : CupCechResolutionComparison U D.target) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hcup : IsModuleCupProduct F G p q cup)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
      p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
      q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = cechCupCochain U F G p q a.val b.val) :
    cup ((A.iso p).inv (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a)))
      ((B.iso q).inv (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b))) =
        (C.iso (p + q)).inv
          (HomologicalComplex.homologyMap C.beta (p + q) (cupCycleClass _ (p + q) c)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
