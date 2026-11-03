/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeightsEmbedding
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison

/-! # The upper weight bound for middle extensions on curves

Source: latest blueprint snapshot `slopmaster2-20261031`,
`sk-thm-wft-curve-middle-upper`.

The statement uses the recorded condensed compact coefficient complex and the
canonical global geometric-Frobenius operator. Its middle image is the
constructible object supplied by `NativeL2.middleImage_constructible`; the
proof is postponed below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeCurveWeights

instance datumCharP (D : FiniteFieldDatum.{u}) : CharP D.k D.p :=
  letI := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card).symm.trans (D.card_base.trans D.cardinality_eq))
  charP_of_injective_algebraMap' D.k₀ D.p

instance datumAlgClosed (D : FiniteFieldDatum.{u}) : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

/-- The ordinary middle image, placed in degree zero with its recorded Weil
structure, is a bounded constructible strict Weil complex.

Source: the constructibility clause of `def-wf-middle-extension` and the
strict-pair construction in `def-weil-weil-sheaf-complex`.
(blueprint: sk-thm-wft-curve-middle-upper).

Proof: the geometric curve is Noetherian since it is of finite type over a field.
The recorded middle-image constructibility theorem gives finite constant local models.
The adic constructibility comparison identifies these with the module-object
constructibility predicate. A constructible sheaf concentrated in degree zero is
bounded constructible. Finally, exact forgetting of the Weil structure commutes
with the degree-zero single functor, so transport along that canonical isomorphism.
-/
theorem middleImage_strict_bounded
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j : U₀ ⟶ C₀) [IsOpenImmersion j.left] [IsDominant j.left]
    (F : NativeL2.WeilModule D l U₀)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (D.geometricFiber C₀).left)
      ((condensedWeilModuleForget (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius C₀).hom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj (NativeL2.middleWeilImage D l j F))) := by
  let X := (D.geometricFiber C₀).left
  let Λ := Profinite.padicAlgClRingObj l
  let : LocallyOfFiniteType (D.geometricFiber C₀).hom := by
    change LocallyOfFiniteType (pullback.snd C₀.hom _)
    infer_instance
  let : QuasiCompact (D.geometricFiber C₀).hom := by
    change QuasiCompact (pullback.snd C₀.hom _)
    infer_instance
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber C₀).hom
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber C₀).hom
  have hc : IsConstantModelConstructible Λ X (NativeL2.middleWeilImage D l j F).carrier := by
    simpa only [NativeL2.middleWeilImage,
      CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso_obj_carrier] using
      (NativeL2.middleImage_constructible D l j hl F.carrier hF)
  have hM : IsConstructibleModuleObject (condensedRingObj Λ X)
      (NativeL2.middleWeilImage D l j F).carrier :=
    ((adicConstructibilityPredicateComparison l X Λ .algebraicClosure).1 _).mpr hc
  let G := condensedWeilModuleForget Λ (D.geometricFrobenius C₀).hom
  exact (boundedConstructible (condensedRingObj Λ X)).prop_of_iso
    ((G.mapDerivedCategorySingleFunctor 0).app (NativeL2.middleWeilImage D l j F)).symm
    (boundedConstructible_singleFunctor_obj Λ X 0 _ hM)

/--
For a dense open in a smooth curve, the ordinary middle image has compactly supported
cohomology of weight at most `w + r`. The operator in the existential is the recorded
compact global geometric-Frobenius operator on
`condensedRingCompactCoefficientComplex`, and the middle image is the recorded
constructible object from `NativeL2.middleImage_constructible`.

Source: latest blueprint snapshot `slopmaster2-20261031`,
`sk-thm-wft-curve-middle-upper`.
(blueprint: sk-thm-wft-curve-middle-upper).

Proof: first treat a geometrically connected curve by reduction to a dense affine open,
then use the affine estimate, the boundary calculation, and localization. For a general
smooth curve, pass to a finite constant extension and its smooth geometrically connected
components, apply the connected case componentwise, and descend the bound by
`sk-lem-wft-infinity-reduction`. The rank-zero, identity-open, proper, negative-degree,
and empty-boundary cases are included in these reductions.
-/
theorem middleExtension_compact_weightsAtMost
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (iota : PadicAlgCl l →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 U₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j : U₀ ⟶ C₀) [IsOpenImmersion j.left] [IsDominant j.left]
    (F : NativeL2.WeilModule D l U₀)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)
    (w : ℝ) (hw : NativeL2.Pure D l U₀ F iota w)
    (c : Compactification (D.geometricFiber C₀).hom) (r : ℤ) :
    (let N := NativeL2.middleWeilImage D l j F
     let Kobj := CategoryTheory.Endofunctor.IsoAlgebra.mk
       ((condensedWeilModuleForget (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius C₀).hom).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj N))
       ((condensedWeilDerivedStructure (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius C₀).hom).app
          ((DerivedCategory.singleFunctor _ 0).obj N))
     let K : WeilConjectures.strictWeilComplexCategory D l hl C₀ (WeilCoefficient.qbar) :=
       ⟨Kobj, by
         have hc := NativeL2.middleImage_constructible D l j hl F.carrier hF
         exact middleImage_strict_bounded D l hl U₀ C₀ j F hF⟩
     let H := condensedRingCompactCohomology
       (Profinite.padicAlgClRingObj l) c r
     let V := (ModuleCat.restrictScalars (Profinite.PadicAlgCl.constRingHom l)).obj
       (H.obj K.obj.carrier)
     ∃ (hfin : FiniteDimensional (PadicAlgCl l) V)
      (A : V ≃ₗ[PadicAlgCl l] V),
      A.toLinearMap =
        ((ModuleCat.restrictScalars (Profinite.PadicAlgCl.constRingHom l)).map
          ((DerivedCategory.homologyFunctor _ r).map
            (GlobalGeometricFrobenius.globalGeometricFrobenius D l hl C₀
              (WeilCoefficient.qbar) c K).2)).hom ∧
      FrobeniusModule.IsMixedOfWeightsAtMostEmbedding
        iota D.q
        { carrier := V, finiteDimensional := hfin, frobenius := A } (w + r)) := by
  sorry

end WeilConjectures.NativeCurveWeights
