/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.SixFunctors.CoefDualFormulaScalarTranspose
public import Sheaf.SixFunctors.RationalVerdierModels

/-! # The normalized integral dual-formula comparison

Source: lem-sf-rational-dual-formula-adjunction, proof step 2; the evaluation
and absolute-trace transpose in lem-coef-finite-exceptional and its coherent
integral realization (blueprint: lem-sf-integral-dual-formula-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
  (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
  (pX : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E X ((IntegralVerdier.dual l E X wX.omega.obj).obj (op K.obj)))
  (pY : ∀ K : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E Y ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op K.obj)))

/-- The evaluation-normalized components assemble into a natural comparison with the
integral dual formula. Transport of the supplied adjunction along this comparison makes
the identity the normalized formula component. This is entirely an integral assertion:
the ordinary tensor presentations and the initial compact-support adjunction are supplied.

Source: lem-sf-rational-dual-formula-adjunction, step 2; current blueprint
lem-coef-finite-exceptional.proof.md, the displayed natural Hom bijections and its
last paragraph on evaluation and counits; thm-coef-integral-verdier.proof.md, the
internal-Hom reduction and evaluation argument
(blueprint: lem-sf-integral-dual-formula-comparison).

Proof: apply formula_existsUnique to the supplied adjunction and tensor presentations
at every M. The resulting component is the trace transpose of the ordinary projection
map followed by the specified completion augmentation and evaluation into omega_X.
Its inverse is currying followed by inverse Verdier biduality. In these two operations,
precomposition with an arrow M to N commutes with evaluation, ordinary projection,
completion augmentation and structural trace. The tensor-Hom naturality equations
therefore identify G.map with the double-contravariant dual-pullback-dual map; the
components and their inverses assemble into a natural isomorphism e. This calculation
is made in the coherent integral mapping system used by formula_existsUnique; it is
not deduced from separate equalities of finite reductions. Transport the adjunction
along e. Its new counit at M is compact support of e.inv.app M followed by the old
counit. Substitute this expression in FormulaNormalized. Naturality of the ordinary
projection map and the support realization moves e.inv through its first tensor
factor. Naturality of the signed symmetry moves it to the evaluation factor, where
it cancels e.hom.app M. The old normalization is consequently exactly the new
normalization with the identity component. These are functorial tensor and adjunction
identities, so empty schemes, zero objects, and torsion objects need no exception. -/
theorem integralDualFormulaComparison
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adj : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ G) :
    ∃ e : G ≅
        (IntegralVerdier.restrictedDual l E Y wY.omega.obj pY).rightOp ⋙
          (@constructibleIntegralPullback l _ E _ _ _ X Y f
            (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).op ⋙
          IntegralVerdier.restrictedDual l E X wX.omega.obj pX,
      ∀ M : sfIntegralConstructibleCategory l E Y,
        CoefDualFormulaScalarTranspose.FormulaNormalized D l hl E f c wX wY aX aZ aY sX
          _ (adj.ofNatIsoRight e) M (Iso.refl _) := by sorry

end WeilConjectures.RationalOperations
