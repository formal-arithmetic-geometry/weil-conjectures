/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenUnitTraceCoordinates
public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ComparisonBrownExplicit
public import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenBoundedCounitCoordinates
public import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenScalarOrdinaryCounit
public import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenScalarSourceUnit
public import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenScalarSupportComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!
# Scalar transport of open unit counits

Source: smooth purity transport Steps 2--3, expanded as open normalization
Step 5 (blueprint: lem-pur-open-scalar-unit-counit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormalizedUnitTrace
open Scheme PurityTransport ExplicitSmoothComparison

/-- Scalar compatibility gives an equality with the explicit transport function,
and this same function preserves the ordinary open counit. Neither assertion
assumes the geometric normalization of the integral smooth counit.

Source: smooth purity transport coefficient compatibility and open normalization
Step 5 (blueprint: lem-pur-open-scalar-unit-counit).

Proof: factor the integral coefficient map through the integers of the bottom finite
subfield, then its fraction field, then the closure; the existing coefficient
identification proves that this is a listed map. Apply ScalarCompatible to this
map and the unit. Naturality of the closure adjunction counit moves the scalar
unit isomorphism through the source. The zero-line normalization then rewrites
the scalar equation as T(unitCounit_0) followed by the scalar unit equals the
support comparison followed by F_1 of the source scalar unit and unitCounit_1.
The support comparison in chosen-to-trivial coordinates has an explicit left
inverse W, obtained from the open scalar isomorphism and the two unit comparisons.
Cancel with W to obtain exactly transportIntegralOpenTrace, proving (1).
For (2), substitute the ordinary integral trace in the transport function and
cancel its inverse compactification comparison. The ordinary scalar open-counit
equation leaves the closure ordinary trace. The bounded counit coordinate
comparison identifies this last morphism with boundedOpenUnitTrace. -/
theorem openScalarUnitCounit
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (b : Family ell k) (hscalar : ScalarCompatible ell k b)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (unitCounit ell b .closure j =
      transportIntegralOpenTrace ell j (unitCounit ell b .integers j)) ∧
    (transportIntegralOpenTrace ell j
      (ordinaryUnitTrace ell .integers (integersAdmissible ell) j) =
        boundedOpenUnitTrace ell j) := by
  classical
  let a := integralClosureMap ell
  let F₀ := CondensedRing.rightDerivedLowerShriekOfCompactification
    ((Coefficient.integers : Coefficient ell).obj ell) (compactificationOverField j)
  let F₁ := CondensedRing.rightDerivedLowerShriekOfCompactification
    ((Coefficient.closure : Coefficient ell).obj ell) (compactificationOverField j)
  let H₁ := (Coefficient.closure : Coefficient ell).smoothSource ell j.left 0
  let S := scalarSixChange a X.left
  let T := scalarSixChange a Y.left
  let J := actualOpen ((Coefficient.closure : Coefficient ell).obj ell) j.left
  let C₀ := openUnitComparison ell .integers (integersAdmissible ell) j
  let C₁ := openUnitComparison ell .closure (closureAdmissible ell) j
  let e := CondensedRing.derivedOpenImmersionShriekIso
        (Λ := (Coefficient.integers : Coefficient ell).obj ell)
        (Λ' := (Coefficient.closure : Coefficient ell).obj ell) a.hom.hom j.left
  let uX := scalarUnitIso ell X.left
  let uY := scalarUnitIso ell Y.left
  let β := scalarSupportMap a (compactificationOverField j)
  let W := C₁.hom ≫ J.map uX.inv ≫ e.inv.app (𝟙_ _) ≫ T.map C₀.inv
  have hlisted : IsListedScalarCoefficientMap ell a := integralClosureMap_listed ell
  obtain ⟨ha, hb⟩ := hscalar .integers .closure a hlisted
  obtain ⟨p, hp⟩ := hb (datum j 0)
  let K₀ : (Coefficient.integers : Coefficient ell).ctf ell Y.left :=
    ⟨𝟙_ _, smoothTraceUnit_mem ell .integers Y.left⟩
  obtain ⟨hK, hs⟩ := hp K₀
  let K₁ : (Coefficient.closure : Coefficient ell).ctf ell Y.left := ⟨_, hK⟩
  let U₁ : (Coefficient.closure : Coefficient ell).ctf ell Y.left :=
    ⟨𝟙_ _, smoothTraceUnit_mem ell .closure Y.left⟩
  have hn : F₁.map (H₁.map uY.hom) ≫ (b .closure (datum j 0)).trace U₁ =
      (b .closure (datum j 0)).trace K₁ ≫ uY.hom := by
    exact congrArg (fun f ↦ f.hom)
      ((b .closure (datum j 0)).adjunction.counit.naturality
        (ObjectProperty.homMk uY.hom : K₁ ⟶ U₁))
  have ht := scalar_unit_counit_of_source F₀ F₁ H₁ S T β uY
    (unitSource ell .integers j.left 0 ≪≫ zeroLine ell .integers X.left)
    (unitSource ell .closure j.left 0 ≪≫ zeroLine ell .closure X.left)
    (sourceScalar ell a j.left 0 ha p (𝟙_ _)) uX.hom
    ((b .integers (datum j 0)).trace K₀)
    ((b .closure (datum j 0)).trace K₁)
    ((b .closure (datum j 0)).trace U₁) hs hn
    (openScalarSourceUnit ell j ha p)
  have htrace : T.map (unitCounit ell b .integers j) ≫ uY.hom =
      β.app (𝟙_ _) ≫ F₁.map uX.hom ≫ unitCounit ell b .closure j := by
    simpa only [unitCounit, unitTrace, datum, F₀, F₁, K₀, U₁, Iso.trans_inv,
      Functor.map_comp, Category.assoc] using ht
  have hsupp : T.map C₀.hom ≫ e.hom.app (𝟙_ _) ≫ J.map uX.hom =
      β.app (𝟙_ _) ≫ F₁.map uX.hom ≫ C₁.hom :=
    openScalarSupportComparison ell j
  have hW : W ≫ β.app (𝟙_ _) ≫ F₁.map uX.hom = 𝟙 _ := by
    apply (cancel_mono C₁.hom).1
    simp only [Category.assoc, Category.id_comp]
    rw [← hsupp]
    simp only [W, Category.assoc, ← T.map_comp_assoc, Iso.inv_hom_id,
      T.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    rw [← J.map_comp, Iso.inv_hom_id, J.map_id, Category.comp_id]
  constructor
  · change unitCounit ell b .closure j =
      C₁.hom ≫ J.map uX.inv ≫ e.inv.app (𝟙_ _) ≫
        T.map (C₀.inv ≫ unitCounit ell b .integers j) ≫ uY.hom
    calc
      _ = W ≫ T.map (unitCounit ell b .integers j) ≫ uY.hom := by
        rw [htrace]
        simp only [← Category.assoc, hW, Category.id_comp]
      _ = _ := by simp only [W, T.map_comp, Category.assoc]
  · calc
      _ = ordinaryUnitTrace ell .closure (closureAdmissible ell) j := by
        unfold transportIntegralOpenTrace ordinaryUnitTrace
        simp only [Iso.inv_hom_id_assoc]
        exact congrArg (C₁.hom ≫ ·) (openScalarOrdinaryCounit ell j)
      _ = boundedOpenUnitTrace ell j := openBoundedCounitCoordinates ell j

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
