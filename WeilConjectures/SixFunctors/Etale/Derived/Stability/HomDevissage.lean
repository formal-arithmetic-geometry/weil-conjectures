/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!
# Internal hom preserves `Dctf` by dévissage

For a finite ring `Λ` whose exponent is invertible on a scheme `X` of finite type over a field
`k`, the internal hom `RHom(K, L)` of two objects of `Dctf(X, Λ)` lies in `Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom_of_devissage`, blueprint
`det-rem-sf-matrix-hom-devissage`).

The proof is a dévissage in the first variable, without Verdier duality, so that no hypothesis on
the field `k` is needed. The objects `K` with `RHom(K, L) ∈ Dctf` for all `L ∈ Dctf` form a thick
subcategory (`RHom(-, L)` is exact, and turns shifts into shifts). So by the generation of
`Dctf(X, Λ)` by the objects `Rg_* Rj_! F` (`sk-lem-sf-ctf-generation`), for `j : U ⟶ Ū` an open
immersion, `g : Ū ⟶ X` a closed immersion and `F` a lisse flat sheaf on `U`, it suffices to treat
these. By the tensor–Hom exchange (`sk-thm-sf-tensor-hom`) for `g`, where `Rg_! = Rg_*`, and for
`j`,

`RHom(Rg_* Rj_! F, L) ≅ Rg_* Rj_* RHom(F, Rj^! Rg^! L)`,

and `Rg^!`, `Rj^!`, `Rj_*`, `Rg_*` preserve `Dctf`. Finally `F` placed in degree `0` has the
lisse flat dual `F^∨ = [F, Λ]` in `D(U_ét, Λ)`, so `RHom(F, N) ≅ F^∨ ⊗ᴸ N ∈ Dctf(U, Λ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- A lisse flat sheaf `F` placed in degree `0` has a left dual in `D(X_ét, Λ)` lying in
`Dctf(X, Λ)`: the termwise dual of the single complex, which is the lisse flat sheaf `[F, Λ_X]`
in degree `0`. -/
theorem exists_constructibleFiniteTor_exactPairing_singleFunctor {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    (hF : ObjectProperty.flat F) :
    ∃ D, constructibleFiniteTor (ModuleCat.{u + 1} Λ) X D ∧
      Nonempty (ExactPairing D ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  let P := (HomologicalComplex.single (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ComplexShape.up ℤ) 0).obj F
  have hPl (n : ℤ) : IsFiniteLocallyConstantSheaf (P.X n) := by
    by_cases hn : n = 0
    · subst hn
      exact IsFiniteLocallyConstantSheaf.of_iso (HomologicalComplex.singleObjXSelf _ 0 F).symm
    · exact IsFiniteLocallyConstantSheaf.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hPf (n : ℤ) : ObjectProperty.flat (P.X n) := by
    by_cases hn : n = 0
    · subst hn
      exact ObjectProperty.prop_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 F).symm hF
    · exact ObjectProperty.flat_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  -- the terms of `P` are dualizable, with right duals their internal duals
  let _ (n : ℤ) : HasRightDual (P.X n) :=
    { rightDual := (ihom (P.X n)).obj (𝟙_ _)
      exact := letI := exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf (P.X n) (hPf n)
        BraidedCategory.exactPairing_swap _ _ }
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_exactPairing_Q_obj_rightDual P 0 0
  obtain ⟨ep⟩ := nonempty_exactPairing_swap (_root_.DerivedCategory.Q.obj P)
    (_root_.DerivedCategory.Q.obj (CochainComplex.rightDual P))
  refine ⟨_, constructibleFiniteTor_Q_obj_of_flat Λ (CochainComplex.rightDual P) (-0) (-0)
    (fun n ↦ ?_) (fun n ↦ ?_), ⟨@exactPairingCongrRight _ _ _ _ _ _ ep
      ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app F)⟩⟩
  · -- the dual of a lisse flat sheaf is flat, being dualizable
    exact IsDualizable.flat ⟨@HasRightDual.mk _ _ _ _ (P.X (-n))
      (exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf (P.X (-n)) (hPf (-n)))⟩
  · -- and lisse
    have := isFiniteLocallyConstantSheaf_ihom_unit_of_flat (P.X (-n)) (hPf (-n))
    exact IsFiniteLocallyConstantSheaf.isConstructibleSheaf this

/-- For a lisse flat sheaf `F` and `N ∈ Dctf(X, Λ)`, the internal hom `RHom(F[0], N)` lies in
`Dctf(X, Λ)`: it is `F^∨ ⊗ᴸ N` for the left dual `F^∨ ∈ Dctf(X, Λ)` of `F[0]`
(`AlgebraicGeometry.Etale.exists_constructibleFiniteTor_exactPairing_singleFunctor`). -/
theorem constructibleFiniteTor_derivedHom_singleFunctor_of_isFiniteLocallyConstantSheaf
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] (hF : ObjectProperty.flat F)
    {N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X N) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj
        (op ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj N) := by
  obtain ⟨D, hD, ⟨_⟩⟩ := exists_constructibleFiniteTor_exactPairing_singleFunctor Λ F hF
  obtain ⟨ep⟩ := nonempty_exactPairing_swap D ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor ⟨@HasRightDual.mk _ _ _ _ D ep⟩ N
  have hT : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (D ⊗ N) :=
    constructibleFiniteTor_tensor Λ X hD hN
  exact (constructibleFiniteTor _ X).prop_of_iso
    ((whiskerRightIso (coefficientDualIsoOfExactPairing D _) N).symm ≪≫ e) hT

section Devissage

variable {X : Scheme.{u}} (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)))

/-- The objects `K` of `D(X_ét, Λ)` such that `RHom(K, L) ∈ Dctf(X, Λ)` for every
`L ∈ Dctf(X, Λ)`. -/
def derivedHomConstructibleFiniteTor (X : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ L, constructibleFiniteTor (ModuleCat.{u + 1} Λ) X L →
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj L)

instance : (derivedHomConstructibleFiniteTor Λ X).IsClosedUnderIsomorphisms where
  of_iso e hK L hL := (constructibleFiniteTor _ X).prop_of_iso
    (((RHom(X)[ModuleCat.{u + 1} Λ]).mapIso e.op).app L) (hK L hL)

instance : (derivedHomConstructibleFiniteTor Λ X).IsStableUnderRetracts where
  of_retract r hK L hL :=
    (constructibleFiniteTor _ X).prop_of_retract
      { i := ((RHom(X)[ModuleCat.{u + 1} Λ]).map r.r.op).app L
        r := ((RHom(X)[ModuleCat.{u + 1} Λ]).map r.i.op).app L
        retract := by
          rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, r.retract, op_id,
            Functor.map_id, NatTrans.id_app] }
      (hK L hL)

instance : (derivedHomConstructibleFiniteTor Λ X).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun L _ ↦ (constructibleFiniteTor _ X).prop_of_isZero
    (((RHom(X)[ModuleCat.{u + 1} Λ]).map_isZero (isZero_zero _).op).obj L)⟩
  isStableUnderShiftBy a := ⟨fun K hK L hL ↦ (constructibleFiniteTor _ X).prop_of_iso
    ((derivedHomShiftIso _ K a).app L).symm
      (hK _ ((constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).le_shift (-a) _ hL))⟩
  ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _ fun L hL ↦
    derivedHom_mem_of_distTriang_left (constructibleFiniteTor _ X) L T hT (h₁ L hL) (h₃ L hL)

end Devissage

/-- Blueprint `det-rem-sf-matrix-hom-devissage`: Internal Hom preserves finite Tor amplitude by
dévissage.

Let `k` be a field, `Λ` a finite ring whose exponent is invertible on `X`, and `X` a scheme of
finite type over `k`. For `K, L ∈ Dctf(X_ét, Λ)`, the internal hom `RHom(K, L)` lies in
`Dctf(X_ét, Λ)`. The blueprint assumes `k` separably closed; the dévissage below does not use it.

The objects `K` with `RHom(K, L) ∈ Dctf` for all `L ∈ Dctf` form a thick subcategory
(`RHom(-, L)` is exact and turns shifts into shifts), so by the generation of `Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek`) it
suffices to treat `K = Rg_* Rj_! F` for an open immersion `j : U ⟶ Ū`, a closed immersion
`g : Ū ⟶ X` and a lisse flat sheaf `F` on `U`. The tensor–Hom exchange
(`AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerShriek`) for `g`, where
`Rg_! ≅ Rg_*`, and for `j` gives `RHom(K, L) ≅ Rg_* Rj_* RHom(F, Rj^! Rg^! L)`; the exceptional
inverse images and direct images preserve `Dctf`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedUpperShriek`,
`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar`), and `RHom(F, N)` is in
`Dctf` for `N ∈ Dctf`, `F[0]` having a lisse flat dual. This replaces the Noetherian induction
of the blueprint over the open and closed parts by the generation statement, which encodes it. -/
theorem constructibleFiniteTor_derivedHom_of_devissage {k : Type u} [Field k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ X]
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X L) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj L) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  refine ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek Λ X
    (derivedHomConstructibleFiniteTor Λ X) (fun str i Ubar j _ _ g _ _ _ F _ hF M hM ↦ ?_) K hK
    L hL
  have : HasInvertibleExponent Λ Ubar := .of_hom g
  have : TopologicalSpace.NoetherianSpace (str.domain i) :=
    (str.immersion i).isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification g := (Compactification.ofIsProper g).hasCompactification
  let N := (R(j)_![ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  -- `RHom(Rg_* N, M) ≅ RHom(Rg_! N, M) ≅ Rg_* RHom(N, Rg^! M)`
  have e₁ := ((RHom(X)[ModuleCat.{u + 1} Λ]).mapIso
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ g).app N).op).app M
  obtain ⟨e₂⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek Λ g N M
  refine (constructibleFiniteTor _ X).prop_of_iso (e₂ ≪≫ e₁.symm) ?_
  refine constructibleFiniteTor_rightDerivedLowerStar Λ (g ≫ aX) aX g rfl ?_
  -- `RHom(Rj_! F, M') ≅ Rj_* RHom(F, Rj^! M')`
  have hM' := constructibleFiniteTor_rightDerivedUpperShriek Λ aX g hM
  obtain ⟨e₃⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek Λ j
    ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ((R(g)^![ModuleCat.{u + 1} Λ]).obj M)
  refine (constructibleFiniteTor _ Ubar).prop_of_iso e₃ ?_
  refine constructibleFiniteTor_rightDerivedLowerStar Λ (j ≫ g ≫ aX) (g ≫ aX) j rfl ?_
  exact constructibleFiniteTor_derivedHom_singleFunctor_of_isFiniteLocallyConstantSheaf Λ F hF
    (constructibleFiniteTor_rightDerivedUpperShriek Λ (g ≫ aX) j hM')

end Etale

end AlgebraicGeometry
