/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents

/-! # Scalar square for the specified dual-to-Hom comparison

Source: blueprint thm-coef-qbar-verdier, retained proof step 5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier.HomComparison
open AlgebraicallyClosedCoefficients (Index)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The specified comparison commutes with enlarging the field of definition.
Source: the coefficient-transport paragraph of blueprint
sec-six-functors-basics/sk-prop-sf-biduality-general, retained
thm-coef-qbar-verdier step 5, compatibility of finite Hom comparisons with scalars.
(blueprint: lem-coef-qbar-verdier-hom-comparison-extension).

Proof: write K as its literal pair (E,A). At E and L, the comparisons defining
localComparison are the finite HomIdentification followed by inclusion and the
recorded identification of the finite dualizing object with B.omega. Compare
these composites after the transition E to L. The finite duality side is the
recorded beta map, by the scalar equation in DualityProperties; betaNormalized
identifies it with the actual RationalVerdier.Extension comparison. On the Hom
side, the rational Hom scalar comparison is the rationalization of the completed
integral Hom comparison. Its evaluation square, together with integral_evaluation
and evaluation in HomIdentification, identifies both finite dual-to-Hom composites
as the transpose of the same scalar-extended evaluation. Injectivity of the finite
tensor-Hom adjunction therefore equates these maps. The omegaComparison scalar
square identifies their second inputs. The identity and tower equations for the
specified Hom scalar comparisons cancel the self-transition unitors used in
stageHomInclusion. Map this finite square through inclusion L, conjugate by the
canonical inclusion-transition isomorphisms, and use their recorded transition
equality. Their components are precisely isoToStage. This is the displayed square.
Repeated fields are covered by the same scalar unitor equations; no choice of an
unrelated object isomorphism or adjunction is used. -/
theorem component_extension (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (L : Index l Ω) (h : K.stage ≤ L) :
    B.duality.dual.map ((stageSystem l Ω X).isoToStage K h).hom.op ≫
        (component l Ω X D hl B K).hom =
      (component l Ω X D hl B ((inclusion L).obj (K.toStage h))).hom ≫
        (homDual l Ω X B.omega (fun M ↦ allPairs l Ω X D hl B.finite M B.omega)).map
          ((stageSystem l Ω X).isoToStage K h).hom.op := by sorry

end WeilConjectures.CoefQbarVerdier.HomComparison
