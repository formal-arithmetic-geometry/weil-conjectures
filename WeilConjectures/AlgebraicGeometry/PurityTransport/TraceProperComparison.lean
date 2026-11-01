/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasicDefs
import all WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedOpenRestrictedCounit

/-! # The canonical proper comparison for the native smooth-trace source

Source: current blueprint smooth-trace properties (3), proper coincidence.
(blueprint: new-det-sp-trace-proper-comparison). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

attribute [local irreducible] DerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  CondensedRing.derivedUpperStarLowerStarAdjunction

private theorem isIso_unit_map_inv_unit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : G ⊣ F) [IsIso a.unit]
    (b : F ⊣ G) (d : F ⊣ H) (K : D) :
    IsIso (d.unit.app (G.obj K) ≫ H.map (inv (a.unit.app K))) := by
  have ff := a.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : IsIso (b.unit.app (G.obj K)) := inferInstance
  have : IsIso (d.unit.app (G.obj K)) := by
    rw [← Adjunction.unit_rightAdjointUniq_hom_app b d (G.obj K)]
    infer_instance
  infer_instance

private theorem traceOpenToStar_isIso (c : Coefficient ell) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : IsClosed (Set.range j))
    (K : c.derived ell X) : IsIso (traceOpenToStar ell c j K) := by
  let b := (WeilConjectures.CompactSupportCondensedRealization.clopenExtensionRightAdjunction
    (c.obj ell) j hj).mapDerivedCategoryAdjunction
  let b' := b.ofNatIsoLeft
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) j).symm
  exact isIso_unit_map_inv_unit
    (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction'
      (c.obj ell) j) b'
    (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj ell) j) K

private theorem compactificationOpen_closed {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsProper f] (cf : Compactification f) : IsClosed (Set.range cf.i) := by
  have : IsProper cf.i := cf.isProper_openImmersion inferInstance
  exact cf.i.isClosedMap.isClosed_range

/-- For a proper map every displayed compactification has invertible canonical
compact-support to direct-image comparison.

Source: current blueprint sec-smooth-purity/sk-def-sp-trace/
sk-def-sp-trace-properties.proof.md, (3), finite maps are proper
(blueprint: new-det-sp-trace-proper-comparison).

Proof in words. The open factor of a compactification of a proper map is proper,
since the proper factor is separated. Its image is therefore closed. For a clopen
immersion open extension is also right adjoint to pullback. Invertibility of
the open unit makes open extension fully faithful, so that reverse adjunction
has invertible counit. Its triangle makes its unit invertible on open-extension
objects. Right-adjoint uniqueness transfers this to the pullback/direct-image
unit at the same objects. The map traceOpenToStar is that invertible unit
followed by direct image of the inverse open unit, hence is invertible. Direct
image preserves the resulting natural isomorphism. Composing it in the functor
category with the direct-image compositor and equality comparison gives a
natural isomorphism. Its component is traceShriekToStar, so that map is an
isomorphism at every object, including an unbounded one. -/
theorem traceShriekToStar_isIso (c : Coefficient ell) {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsProper f] (cf : Compactification f) (K : c.derived ell X) :
    IsIso (traceShriekToStar ell c cf K) := by
  have : ∀ K, IsIso ((traceOpenToStarNat ell c cf.i).app K) :=
    fun K ↦ traceOpenToStar_isIso ell c cf.i (compactificationOpen_closed cf) K
  have : IsIso (traceOpenToStarNat ell c cf.i) := NatIso.isIso_of_isIso_app _
  have : IsIso (traceShriekToStarNat ell c cf) := by
    unfold traceShriekToStarNat
    infer_instance
  exact NatIso.isIso_app_of_isIso (traceShriekToStarNat ell c cf) K

end AlgebraicGeometry.ProEtale.PurityTransport
