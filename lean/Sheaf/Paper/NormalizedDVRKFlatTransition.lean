/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T6
-/
module

public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.IntegralReductionTower

/-! # Quotient transitions on K-flat representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
/-- Canonical abelian sheafification, registered only in this file. -/
abbrev normalizedDVRKFlatTransitionLocal1 :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
attribute [local instance] normalizedDVRKFlatTransitionLocal1
/-- The canonical locally bijective sheafification criterion, registered locally. -/
abbrev normalizedDVRKFlatTransitionLocal2 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
attribute [local instance] normalizedDVRKFlatTransitionLocal2

/-- The universal derived tensor counit followed by the exact restriction comparison.
Source: Stacks Tag 06YY; blueprint final proof step of DVR effectivity.
This is an actual morphism built from the fixed derived functors. -/
noncomputable def normalizedDVRKFlatComparison (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (scalarReductionDerivedRestriction l E X n).obj
        ((scalarReductionDerivedExtension l E X n).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj (unrestrictedTowerComplex l E X n P) :=
  (scalarReductionDerivedRestriction l E X n).map
      ((scalarReductionCounit l E X n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
    (scalarReductionRestriction l E X n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension l E X n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The canonical quotient chain map is the restriction of the adjoint reduction
transition, expressed through the universal K-flat comparison.
Source: Stacks Tags 03EK, 06YY, 06YL; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-coef-normalized-dvr-kflat-transition).

Proof: first take M=Q(P) and e the identity. The ordinary tensor map sends b tensor x
to rho(b) tensor x. It is linear over the larger finite quotient, because the
completed projections compose with rho. Its adjoint sends x to 1 tensor x and hence
is the smaller scalar-extension unit. Apply the homotopy-category adjunction and
localize. The derived adjunction normalization identifies the resulting adjoint
with the displayed derived transition, after the exact restriction composition
comparison. The universal derived counits give exactly the comparison factors on
both sides. On pure tensors the restricted ordinary map has the formula defining
integralTowerTransition; tensor generation and the universal property of
sheafification prove equality, degree by degree. For general e, naturality of the
two adjunction units, of the counits and of the restriction comparison transports
the equality along e.inv. The argument is valid for n=0 and zero complexes. -/
theorem normalizedDVR_kflat_transition
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P)
    (M : completedIntegralDerivedCategory l E X D hl)
    (e : DerivedCategory.Q.obj P ≅ M) (n : ℕ)
    (am : scalarReductionDerivedExtension l E X (n + 1) ⊣
      scalarReductionDerivedRestriction l E X (n + 1))
    (an : scalarReductionDerivedExtension l E X n ⊣ scalarReductionDerivedRestriction l E X n)
    (hm : am.unit.app (DerivedCategory.Q.obj P) ≫
        normalizedDVRKFlatComparison l E X (n + 1) P =
      DerivedCategory.Q.map (integralTowerUnit l E X D hl P (n + 1)))
    (hn : an.unit.app (DerivedCategory.Q.obj P) ≫
        normalizedDVRKFlatComparison l E X n P =
      DerivedCategory.Q.map (integralTowerUnit l E X D hl P n)) :
    (scalarReductionDerivedRestriction l E X (n + 1)).map
        ((am.homEquiv
          M ((normalizedDVRRes l E X n.le_succ).obj
            ((scalarReductionDerivedExtension l E X n).obj M))).symm
          (an.unit.app M ≫
            (normalizedDVRResCompletedComp l E X D hl n.le_succ).inv.app
              ((scalarReductionDerivedExtension l E X n).obj M))) ≫
      (normalizedDVRResCompletedComp l E X D hl n.le_succ).hom.app
        ((scalarReductionDerivedExtension l E X n).obj M) ≫
      (scalarReductionDerivedRestriction l E X n).map
        ((scalarReductionDerivedExtension l E X n).map e.inv) ≫
      normalizedDVRKFlatComparison l E X n P =
    (scalarReductionDerivedRestriction l E X (n + 1)).map
        ((scalarReductionDerivedExtension l E X (n + 1)).map e.inv) ≫
      normalizedDVRKFlatComparison l E X (n + 1) P ≫
      DerivedCategory.Q.map (integralTowerTransition l E X D hl P n) := by
  sorry

end WeilConjectures
