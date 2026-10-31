/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
import WeilConjectures.PoincareDuality.IntegralTateBasis
import WeilConjectures.AlgebraicGeometry.NativeSignedLine
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Evaluation isomorphism for condensed Tate lines
Source: the root-line evaluation step of `sk-def-trace-cup`.
(blueprint: sk-def-trace-cup-evaluation-isIso)

A pro-etale cover trivializing the integral Tate module makes the first Tate
line locally regular after scalar extension; the native signed-line theorem then
shows every positive Tate line invertible, so its closed counit into the unit is
an isomorphism, uniformly for all coefficient stages.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj
open MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCup
open PurityTransport
attribute [local irreducible] _root_.AlgebraicGeometry.ProEtale.upperStarFromPoint

/-- Inverse image commutes with extension of scalars (mate of the restriction square). -/
private noncomputable def pullExtendIso
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    (_root_.AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).mapMod R ⋙
        Mod.extendScalars
          ((_root_.AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).map a) ≅
      Mod.extendScalars a ⋙
        (_root_.AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).mapMod S := by
  let adj := _root_.AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f
  exact Adjunction.pullIsoOfComapIso
    (Mod.extendRestrictAdjunction
      ((_root_.AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).map a))
    (Mod.extendRestrictAdjunction a)
    (adj.mapModAdjunction R) (adj.mapModAdjunction S)
    (Mod.comapMapModComapIso (_root_.AlgebraicGeometry.ProEtale.lowerStar Ab.{u + 1} f)
      ((_root_.AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).map a) a
      (adj.unitAlgHom R) (adj.unitAlgHom S) (adj.unit.naturality a))
variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)


/-- The positive Tate line evaluates against its signed inverse by an isomorphism.
Source: root-line evaluation in `sk-def-trace-cup`.
(blueprint: sk-def-trace-cup-evaluation-isIso)
Proof: ell is invertible in every residue field, hence (units are detected on
germs, and local residue maps reflect units) a unit in global sections. Take a
pro-etale cover trivializing the integral Tate module (`tateModule_locally_trivial`).
Inverse image commutes with extension of scalars along the integral coefficient map
(the mate of the commuting restriction square under the pullback adjunctions), and
extension of scalars sends the regular module to the regular module; so the first
line is regular on each member of the cover. By `nativeSignedLine` its signed power
of exponent d+1 is invertible; by induction that power is `c.line ell T (d+1)`.
The closed counit of an invertible object into the unit is an isomorphism. -/
theorem evaluation_isIso {T : Scheme.{u}}
    [∀ x : T, Invertible (ell : T.residueField x)] (d : ℕ) :
    IsIso ((ihom.ev (c.line ell T (d + 1))).app (𝟙_ _)) := by
  have hInv : IsUnit (ell : Γ(T, ⊤)) := by
    apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((T.presheaf.germ ⊤ x hx).hom (ell : Γ(T, ⊤)))
    rw [map_natCast]
    apply (isUnit_map_iff (IsLocalRing.residue (T.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using isUnit_of_invertible (ell : T.residueField x)
  obtain ⟨𝒰, h𝒰⟩ := tateModule_locally_trivial T ell hInv
  have hfirst : ∃ 𝒱 : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : 𝒱.I₀,
      Nonempty (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (𝒱.f i)).mapMod
        (condensedRingObj (c.obj ell) T)).obj (c.firstLine ell T) ≅ 𝟙_ _) := by
    refine ⟨𝒰, fun i ↦ ?_⟩
    let F := AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (𝒰.f i)
    exact ⟨(pullExtendIso (𝒰.f i) (coefficientMap (c.integralMap ell) T)).symm.app
        (tateModule T ell) ≪≫
      (Mod.extendScalars (F.map (coefficientMap (c.integralMap ell) T))).mapIso
        (h𝒰 i).some ≪≫
      Mod.extendScalarsObjRegularIso (F.map (coefficientMap (c.integralMap ell) T))⟩
  have hsigned := _root_.AlgebraicGeometry.ProEtale.nativeSignedLine
    (condensedRingObj (c.obj ell) T) (c.firstLine ell T)
    hfirst
  have hline : ∀ n : ℕ, c.line ell T n =
      _root_.AlgebraicGeometry.ProEtale.coefficientTwistNat T
        (condensedRingObj (c.obj ell) T) (c.firstLine ell T) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Coefficient.line,
        _root_.AlgebraicGeometry.ProEtale.coefficientTwistNat, ih]
  have hpow : IsInvertible (c.line ell T (d + 1)) := by
    have hnat := hsigned.2.2.1 (Int.ofNat (d + 1))
    change IsInvertible (_root_.AlgebraicGeometry.ProEtale.coefficientTwistNat T
      (condensedRingObj (c.obj ell) T) (c.firstLine ell T) (d + 1)) at hnat
    rw [hline (d + 1)]
    exact hnat
  exact hpow.isIso_ev (𝟙_ _)

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCup
