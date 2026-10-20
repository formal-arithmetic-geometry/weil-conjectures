/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierDimension
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Characteristic-prime vanishing above degree one in smooth proper curves

Source: Stacks Project, Tags 0GKV, case (b), and 0A3N.
(blueprint: lem-weil-pbc-prime-curve-charP-high-vanishing)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem prime_constant_stalk_zero
    {C S : Scheme.{u}} (f : C ⟶ S) [Smooth f] [IsProper f]
    [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (ell : ℕ) [Fact ell.Prime] (hp : (ell : Γ(S, ⊤)) = 0)
    (q : ℕ) (hq : 1 < q) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    IsZero (((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
      (higherDirectImage (ULift.{u + 1} (ZMod ell)) f q
        ((constantSheaf C.smallEtaleTopology _).obj
          (ModuleCat.of (ULift.{u + 1} (ZMod ell)) (ULift.{u + 1} (ZMod ell)))))) := by
  let R := ULift.{u + 1} (ZMod ell)
  let M := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R)
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : Scheme.IsFiniteSheaf M := by
    constructor
    intro Ξ _ _ t
    let e := (Scheme.pointSmallEtale t).sheafFiberConstantSheafIso (ModuleCat.of R R)
    have : Finite (((Scheme.pointSmallEtale t).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj M) :=
      Finite.of_equiv R e.toLinearEquiv.toEquiv.symm
    exact (ModuleCat.isFinitelyGenerated_iff _).mpr (Module.Finite.of_finite (R := R))
  have : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have : SmoothOfRelativeDimension 1 f :=
    smoothOfRelativeDimension_of_fiberToSpecResidueField f 1 fun t ↦ by
      have : Smooth (f.fiberToSpecResidueField t) :=
        inferInstanceAs (Smooth (pullback.snd _ _))
      have : IrreducibleSpace (f.fiber t) := inferInstance
      exact (smoothOfRelativeDimension_iff_topologicalKrullDim_eq
        (f.fiberToSpecResidueField t) 1).mpr (hdim t)
  have : ConnectedSpace (pullback f s : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := pullback.snd f s)
  have : IsCurve (pullback.snd f s) :=
    { krullDim_le_one := le_of_eq
        (topologicalKrullDim_eq_of_smoothOfRelativeDimension (pullback.snd f s) 1) }
  have hchar : (ell : Ω) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (fun a ↦ (Scheme.ΓSpecIso (.of Ω)).hom (s.appTop a)) hp
  have : CharP Ω ell := (CharP.charP_iff_prime_eq_zero (Fact.out : ell.Prime)).mpr hchar
  have : IsConnectedCurve (pullback.snd f s) :=
    { connectedSpace := inferInstance
      krullDim_eq_one :=
        topologicalKrullDim_eq_of_smoothOfRelativeDimension (pullback.snd f s) 1 }
  let N := (constantSheaf (pullback f s).smallEtaleTopology
    (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R)
  have hvan := isZero_etaleCohomology_constantZMod_of_one_lt_of_charP
    (pullback.snd f s) ell q hq
  obtain ⟨ec⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso (pullback f s) R q
  have : (pullback f s).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) := by
    apply GrothendieckTopology.instPreservesSheafification
  let eAb : (moduleAbelianForget R (pullback f s)).obj N ≅
      (pullback f s : Scheme.{u}).constantZMod ell :=
    (constantCommuteCompose (pullback f s).smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).app (ModuleCat.of R R)
  let eH := (ec.app N) ≪≫
    (cohomology AddCommGrpCat.{u + 1} (pullback f s) q).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso eAb)
  have hN : IsZero ((cohomology (ModuleCat.{u + 1} R) (pullback f s) q).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map_injective
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact (hvan.of_iso eH).eq_of_src _ _
  let e := (cohomology (ModuleCat.{u + 1} R) (pullback f s) q).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} R) (pullback.fst f s)).app
        (ModuleCat.of R R)))
  have hsource := hN.of_iso e
  obtain ⟨a, b, hab⟩ := geometricFiber_finite_stalk_formula R f Ω s M q
  exact hsource.of_iso (asIso (a.inv ≫
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} R)).map
      (baseChangeHomologyMap R (IsPullback.of_hasPullback f s) q M) ≫ b.hom))
/-- Above degree one, the prime-coefficient higher direct image vanishes over the
full characteristic-prime base, including nonreduced bases.
Source: Stacks Project, Tag 0GKV, case (b), vanishing paragraph; Tag 0A3N.
(blueprint: lem-weil-pbc-prime-curve-charP-high-vanishing)

Proof: at each algebraically closed geometric point, base change gives a smooth
proper connected curve of dimension one. The image of p = 0 in the global section
ring of the base gives characteristic p in this geometric field. The Artin--Schreier
curve dimension theorem makes the constant Z/p cohomology zero above degree one.
Constants commute with forgetting coefficients, and the module/abelian cohomology
comparison reflects zero objects, giving the same vanishing for prime modules.
Proper base change and preservation of constants identify this group with the
geometric stalk of the required higher direct image. The algebraic-closure-point
stalk functors are conservative; applied to the identity versus zero, they show the
whole higher direct image is zero. Empty schemes satisfy this argument vacuously. -/
theorem prime_higherDirectImage_zero_of_charP
    {C S : Scheme.{u}} (f : C ⟶ S) [Smooth f] [IsProper f]
    [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hp : (p : Γ(S, ⊤)) = 0) (q : ℕ) (hq : 1 < q) :
    IsZero (higherDirectImage (ULift.{u + 1} (ZMod p)) f q
      ((constantSheaf C.smallEtaleTopology _).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))) := by
  let R := ULift.{u + 1} (ZMod p)
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro s
  have hz := prime_constant_stalk_zero f hdim p hp q hq _ (S.algClosurePoint s)
  have := (Scheme.pointSmallEtale (S.algClosurePoint s)).sheafFiber_additive
    (A := ModuleCat.{u + 1} R)
  simpa only [CategoryTheory.Functor.map_id, Functor.map_zero] using hz.eq_of_src (𝟙 _) 0
end AlgebraicGeometry.Etale
