/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.SixFunctors.RationalOperationsData

/-! # Scalar-compatible rational exceptional dual formulas

Source: lem-coef-rational-operations, steps 10--20
(blueprint: lem-sf-rational-exceptional-identifications).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f) (S : System l Ω D hl (f := f))
  (F G : FieldStage.{u} l) (ι : F.carrier →ₐ[Padic l] G.carrier)

/-- Transport the existing exceptional adjunction along the compact-support and dual
formula comparisons. The component formulas retain its actual unit and counit.
Source: lem-coef-rational-operations, proof steps 10--11
(blueprint: lem-sf-rational-exceptional-identifications). -/
noncomputable def exceptionalIdentificationOfIso
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl F.carrier)
    (A : RationalVerdier.Datum D l hl X F.carrier wX)
    (B : RationalVerdier.Datum D l hl Y F.carrier wY)
    (e : (S.ring.operation c (.rational F)).G ≅
      dualFormula l X D hl (f := f) F wX wY A B) :
    ExceptionalIdentification l X D hl Ω c S F wX wY A B where
  comparison := e
  adjunction := ((S.ring.operation c (.rational F)).adjunction.ofNatIsoLeft
    (S.ring.rationalLeft c F)).ofNatIsoRight e
  unit K := by
    simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  counit M := by
    simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]

/-- The exceptional dual formula for two coefficient fields, with the actual mate square.
Hom identifications and normalized duality comparisons are inputs; neither a Hom
adjunction nor a structure-map dualizing identification is asserted here.
Source: lem-coef-rational-operations, DAG proof steps 10--20, exceptional clauses
(blueprint: lem-sf-rational-exceptional-identifications).

Proof: on integral constructible categories use the exceptional adjunction with its
normalized dual formula. Localizing its linear Hom bijection gives the rational
adjunction with the localized unit and counit. Compare its compact support and right
adjoint with S through the normalized realization and rationalization comparisons.
Transposing counits gives the unique comparisons respecting those adjunctions. Compose
with the integral dual formula and the given rational duality presentations; this gives
eF and eG, transporting the adjunction along the left and right natural isomorphisms.
For finite scalars choose cofinal levels S/(pi^n)=S/(varpi_L^(en)). The finite-free
compact-support comparison on a compatible basis is finite-sum distributivity; it
commutes with the quotient transition maps and hence defines the strict-tower map alpha.
Extension/restriction adjunction and constructible exceptional adjunction identify
restriction of the target right adjoint with the source right adjoint after restriction.
The scalar exceptional mate is invertible: in the chosen basis its underlying matrix
is identity, by the triangle identity. The finite scalar mate realization identifies
this mate with the specified coefficient-system comparison. The dual-formula scalar
transpose theorem identifies the transpose of the composite duality/pullback comparison
with the same counit composite T(epsilon) alpha inverse. Injectivity of the adjunction
bijection makes the maps equal. The given normalizedX and normalizedY identify their
actual integral duality maps and evaluations, so they yield exactly dualScalar below.
Localize the resulting strict system-map identity; bilinearity preserves the equation
on all rational maps. This argument includes the identity extension and uses the
ramification index only to choose cofinal positive quotient levels. -/
theorem rationalExceptional_identifications
    (wXF : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier)
    (wYF : IntegralFiniteExtension.DualizingDatum l Y D hl F.carrier)
    (wXG : IntegralFiniteExtension.DualizingDatum l X D hl G.carrier)
    (wYG : IntegralFiniteExtension.DualizingDatum l Y D hl G.carrier)
    (DXF : RationalVerdier.Datum D l hl X F.carrier wXF)
    (DYF : RationalVerdier.Datum D l hl Y F.carrier wYF)
    (DXG : RationalVerdier.Datum D l hl X G.carrier wXG)
    (DYG : RationalVerdier.Datum D l hl Y G.carrier wYG)
    (hXF : HomIdentification l F.carrier X D hl wXF DXF)
    (hYF : HomIdentification l F.carrier Y D hl wYF DYF)
    (hXG : HomIdentification l G.carrier X D hl wXG DXG)
    (hYG : HomIdentification l G.carrier Y D hl wYG DYG)
    (eX : RationalVerdier.Extension D l hl X F.carrier G.carrier ι wXF wXG DXF DXG)
    (eY : RationalVerdier.Extension D l hl Y F.carrier G.carrier ι wYF wYG DYF DYG)
    (normalizedX : RationalVerdier.ExtensionProperties D l hl X F.carrier G.carrier ι
      wXF wXG DXF DXG eX)
    (normalizedY : RationalVerdier.ExtensionProperties D l hl Y F.carrier G.carrier ι
      wYF wYG DYF DYG eY) :
    ∃ (qF : (S.ring.operation c (.rational F)).G ≅
        dualFormula l X D hl (f := f) F wXF wYF DXF DYF)
      (qG : (S.ring.operation c (.rational G)).G ≅
        dualFormula l X D hl (f := f) G wXG wYG DXG DYG),
      let eF := exceptionalIdentificationOfIso D l hl X Ω c S F wXF wYF DXF DYF qF
      let eG := exceptionalIdentificationOfIso D l hl X Ω c S G wXG wYG DXG DYG qG
      let I : Identification l X D hl Ω c S F := ⟨wXF, wYF, DXF, DYF, hXF, hYF, eF⟩
      let J : Identification l X D hl Ω c S G := ⟨wXG, wYG, DXG, DYG, hXG, hYG, eG⟩
      ∀ M : sfRationalConstructibleCategory l F.carrier Y,
        (RationalVerdier.scalar l X F.carrier G.carrier ι).map
            (eF.comparison.hom.app M) ≫
          dualScalar l X D hl Ω c S F G ι I J eX eY M =
        (S.fields.rationalComparison c F G ι).b.hom.app M ≫
          eG.comparison.hom.app
            ((RationalVerdier.scalar l Y F.carrier G.carrier ι).obj M) := by sorry

end WeilConjectures.RationalOperations
