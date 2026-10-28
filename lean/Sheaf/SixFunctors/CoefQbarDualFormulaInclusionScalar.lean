/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData

/-! Scalar compatibility of duality-pullback-duality inclusion components.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-dual-formula-inclusion-scalar)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Transporting the dual-formula scalar map through the finite-origin duality
comparisons gives the common-stage scalar square. No exceptional functor or exceptional
comparison occurs in this statement.
Source: thm-coef-qbar-verdier, retained proof step 9, substitution of the BX, BY and
pullback scalar squares. (blueprint: lem-coef-qbar-dual-formula-inclusion-scalar)

Proof: write K = pullback_E(DY_E M). Expand the displayed scalar map as beta_X(K)
followed by DX_L of the opposite of pullback_L(beta_Y inverse) followed by the inverse
pullback scalar comparison. Naturality of BX.comparison moves the latter factor through
the BX comparison at L. The scalar equation in BX.properties, with betaNormalized,
replaces the resulting beta_X and BX comparison by inclusionTransition_X followed by
the BX comparison at E; its remaining factor is BX.dual applied to the opposite inverse
inclusionTransition_X at K. In the remaining contravariant argument, naturality and the
scalar square for pullbackInclusion move the inverse pullback scalar comparison through
the two pullback inclusions. The scalar equation in BY.properties, inverted and using
betaNormalized, replaces beta_Y inverse and the BY comparisons by BY.dual of inverse
inclusionTransition_Y. Functoriality of pullback and the contravariant dual combines these
factors; the adjacent inclusionTransition_X inverse and forward factors cancel. The
result is exactly the right side. All comparisons are isomorphisms, so cancellation is
valid on zero objects and for identity or repeated coefficient fields as well. -/
theorem dual_formula_inclusion_scalar
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E) :
    (inclusion L).map
      ((BX.finite.scalar E L h).comparison.hom.app
          (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
            (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
              ((BY.finite.datum E).dual.obj (op M)))) ≫
        (BX.finite.datum L).dual.map
          (((@rationalDerivedPullback l _ (Coefficient.{u} l Ω L) _ _ _ X Y f
              (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).map
              ((BY.finite.scalar E L h).comparison.inv.app (op M)) ≫
            (@rationalPullbackScalarComparison l _ (Coefficient.{u} l Ω E) _ _ _
              (Coefficient.{u} l Ω L) _ _ _
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) X Y f
              (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).inv.app
                ((BY.finite.datum E).dual.obj (op M))).op)) ≫
      (BX.comparison L).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω L) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum L).dual.obj (op ((transition l Ω Y E L h).obj M))))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map
          ((BY.comparison L).inv.app (op ((transition l Ω Y E L h).obj M))) ≫
          (pullbackInclusion D l hl Ω X f L
            ((BY.finite.datum L).dual.obj (op ((transition l Ω Y E L h).obj M)))).inv).op =
    (inclusionTransition l Ω X E L h).hom.app
      ((BX.finite.datum E).dual.obj
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op M))))) ≫
      (BX.comparison E).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op M)))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map ((BY.comparison E).inv.app (op M)) ≫
          (pullbackInclusion D l hl Ω X f E
            ((BY.finite.datum E).dual.obj (op M))).inv).op ≫
      (BY.duality.dual.rightOp ⋙ (CoefQbarPullback D l hl Ω f).op ⋙ BX.duality.dual).map
        ((inclusionTransition l Ω Y E L h).inv.app M) := by sorry

end WeilConjectures.CoefQbarVerdier
