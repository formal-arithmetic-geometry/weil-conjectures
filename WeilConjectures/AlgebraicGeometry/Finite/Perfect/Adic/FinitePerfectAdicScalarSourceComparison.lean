/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicSourcePresentation
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantChart
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation

/-! # Direct constant presentation of the ordinary chart source

Source: Stacks Project, Tags 093J and 093M.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData completedAdicRing
  directCoefficientMap overDirectMap

attribute [local irreducible] sourceDirectIso
  chartConstantsIso constantAssociatedIso overDirectIso directConstant directCoefficientIso
  finitePerfectAdicAssociatedCoherence

attribute [local irreducible] sourceChartMap

attribute [local irreducible] SourceChartSquare

section PastingFormula
variable
    (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    {B D : Type t} [CommRing B] [CommRing D] (q₀ : B →+* D)
    {R S T : Sheaf ((ProEt.topology X).over W) RingCat.{t + 1}}
    (α : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶ R.obj)
    (β : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} D)) ⟶ S.obj)
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) α]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) α]
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) β]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) β]
    (a : T ⟶ R) (p : R ⟶ S) (c : T ⟶ S)
    (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom (RingHom.ulift q₀) ≫ β.app Z)

end PastingFormula

attribute [local semireducible] directConstant

end AlgebraicGeometry.Scheme
