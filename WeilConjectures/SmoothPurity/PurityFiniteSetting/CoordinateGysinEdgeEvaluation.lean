/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData

/-! # Evaluation through the normalized local-class edge

(blueprint: lem-pur-coordinate-gysin-edge-evaluation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The normalized edge takes a global class to the local class of the same morphism.
Source: latest blueprint, lem-pur-gysin-structure.proof.md, second assertion,
evaluation on one and identification of Hom with sections of cohomology.
(blueprint: lem-pur-coordinate-gysin-edge-evaluation).

Proof: put K = gysinClosed and choose a bounded-below injective representative I
of K, using comparison.bounded_closed. Transport m to a map from the constant single
object to Q(I)[2]. K-injective localization represents it by a chain map into I[2].
The single-complex and shift comparisons give its sole component f : constant -> I^2,
with f followed by d^2 equal to zero. Evaluation on the coefficient unit is natural
for postcomposition, so it gives a cycle y of global sections of I in degree two.
The source element used by gysinGlobalClass is the inverse single-object cohomology
comparison applied to toRightDerivedZero of gysinEvaluate(id). The single-object
unit normalization identifies this element with the augmentation's unit cocycle.
Naturality of the derived unit and its K-injective comparison therefore identify
gysinGlobalClass(m) with the class of y, under the displayed derived shift comparison.
By edge_spec, D.edge is comparison.edge. EdgeNormalization on I takes the class of y
to the sheaf-cohomology class of the same cycle: its three cycle/kernel comparison
isomorphisms only change the presentation of that kernel. This local class is
H^0(m) evaluated on one, followed by the canonical H^0(K[2])-to-H^2(K) comparison,
which is the right side by the definition of gysinHomToSections. Degree two is even,
so the differential and cycle comparisons have no extra sign. Chain-map homotopies
change both representatives by boundaries. Naturality of the edge, homology factors
and shift comparisons transports the identity through the representing isomorphism
back to K, independently of the resolution or chain-map lift. -/
theorem coordinateGysin_edge_evaluation
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (D : OrientationSupportData P h T)
    (m : P.derivedSheaf h T false ⟶ P.gysinValue h T) :
    D.edge.hom (P.gysinGlobalClass T 2 m) =
      (globalSectionsFunctor (Modules P) T).map
        (((DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso
          (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h T))
        (P.gysinHomToSections h T m) := by
  sorry

end WeilConjectures.PurityFiniteSetting
