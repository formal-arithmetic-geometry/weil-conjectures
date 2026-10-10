/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.Derived.Duality
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Stability

/-!

# Perfect complexes of pro-étale sheaves and their coefficient duals

Let `X` be a scheme. A complex `K ∈ D(X_proét)` is *perfect* over `Λ_X` if it is, locally on
the small pro-étale site, quasi-isomorphic to a bounded complex of finite projective
`Λ_X`-modules. As in `WeilConjectures.SixFunctors.Etale.Derived.Perfect`, perfectness is
rendered as dualizability for the derived tensor product, `CategoryTheory.IsDualizable`; for
sheaves of modules over a ringed site the two notions agree (Stacks, Tag 0FPV). A *finite
projective `Λ_X`-module* is, as in the blueprint, a direct summand of a finite free module
`Λ_Xʳ`, that is, a retract of the finite direct sum `⨁ Λ_X` of copies of the monoidal unit.

This file proves that the coefficient dual `K^∨ = RHom(K, Λ_X)`
(`AlgebraicGeometry.ProEtale.derivedDual`) of a perfect complex is perfect, and, at a finite
coefficient ring `Λ`, lies in `Dctf(X, Λ)`.

## Main statements

- `AlgebraicGeometry.ProEtale.derivedDual_obj`,
  `AlgebraicGeometry.ProEtale.derivedDualEval_eq_uncurry` (`rem-ptr-pod-perfect-complex-on-x-5`):
  the coefficient dual and its evaluation `AlgebraicGeometry.ProEtale.derivedDualEval` are
  formed with the derived internal hom.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTorAmplitudeIn_single_of_retract`
  (`prop-pod-perfect-local-model`): a finite projective `Λ_X`-module is flat and constructible.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_of_isDualizable`
  (`prop-pod-perfect-local-model`): a perfect complex lies in `Dctf(X, Λ)`.
- `AlgebraicGeometry.ProEtale.isDualizable_derivedDual` (`lem-pod-coefficient-dual-perfect`):
  the coefficient dual of a perfect complex is perfect.
- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_derivedDual`
  (`lem-pod-coefficient-dual-perfect`): the coefficient dual of a perfect complex lies in
  `Dctf(X, Λ)`.

## Implementation notes

The blueprint argues locally, on a bounded complex of finite projective modules. With
perfectness rendered as dualizability, the first statement is instead the general fact that
in a braided monoidal closed category the internal dual `[K, 𝟙]` of a dualizable `K` is its
right dual `Kᘁ`, hence dualizable (`CategoryTheory.IsDualizable.ihom_unit`). It is applied to
some braiding of `D(X_proét)` (`DerivedCategory.nonempty_braidedCategory`); the conclusion
does not depend on which one.

The statements about `Dctf(X, Λ)` are made at a finite coefficient ring `Λ`, as in the
blueprint's setting: bounded constructibility is étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`), which is the right notion
only at the finite coefficient stages. A finite projective `Λ_X`-module is of étale origin
since `Λ_Xʳ = ν^* Λ_{X_ét}ʳ` and `ν^*` is full and exact. For perfect complexes `X` is moreover
taken Noetherian, as boundedness of a perfect complex needs `X` to be quasi-compact.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Dualizable

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {A} {X : Scheme.{u}}

/-- Blueprint `rem-ptr-pod-perfect-complex-on-x-5`: the coefficient dual `K^∨ = RHom(K, Λ_X)` is
formed with the derived internal hom: it is the internal hom of the monoidal closed structure of
`D(X_proét)` into the unit `Λ_X`. -/
lemma derivedDual_obj (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (derivedDual A X).obj (op K) = (ihom K).obj (𝟙_ _) := rfl

/-- Blueprint `rem-ptr-pod-perfect-complex-on-x-5`: the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` of the
tensor–internal-hom adjunction, for the coefficient dual `K^∨ = RHom(K, Λ_X)`. -/
noncomputable def derivedDualEval (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ⊗ (derivedDual A X).obj (op K) ⟶ 𝟙_ _ :=
  (ihom.ev K).app (𝟙_ _)

/-- Blueprint `rem-ptr-pod-perfect-complex-on-x-5`: the evaluation of the coefficient dual is the
map corresponding to the identity of `K^∨` under the tensor–internal-hom adjunction. -/
lemma derivedDualEval_eq_uncurry
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    derivedDualEval K = MonoidalClosed.uncurry (𝟙 ((derivedDual A X).obj (op K))) :=
  (MonoidalClosed.uncurry_id_eq_ev _ _).symm

/-- Blueprint `lem-pod-coefficient-dual-perfect`: Perfectness is preserved by coefficient
duality.

The coefficient dual `K^∨ = RHom(K, Λ_X)` of a perfect (that is, dualizable) complex `K` of
pro-étale sheaves is again perfect. -/
theorem isDualizable_derivedDual
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : IsDualizable K) :
    IsDualizable ((derivedDual A X).obj (op K)) := by
  obtain ⟨_⟩ :=
    _root_.DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology X) A)
  exact hK.ihom_unit

/-- The coefficient dual `K^∨` of a perfect complex `K` of Tor amplitude in `[a, b]` has Tor
amplitude in `[-b, -a]`: it is the dual `Kᘁ` of `K`
(`_root_.DerivedCategory.torAmplitudeIn_of_exactPairing`). -/
theorem DerivedCategory.torAmplitudeIn_derivedDual {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hKt : DerivedCategory.torAmplitudeIn A X a b K) (hK : IsDualizable K) :
    DerivedCategory.torAmplitudeIn A X (-b) (-a) ((derivedDual A X).obj (op K)) := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ :=
    _root_.DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology X) A)
  let := BraidedCategory.exactPairing_swap K Kᘁ
  exact (DerivedCategory.torAmplitudeIn A X _ _).prop_of_iso
    (MonoidalClosed.ihomObjUnitIso Kᘁ K).symm
    (_root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := Kᘁ) hKt)

end Dualizable

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}}

namespace DerivedCategory

section FiniteProjective

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Λ} {P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} {r : ℕ}

/-- A finite projective `Λ_X`-module `P`, that is, a direct summand of a finite free module
`Λ_Xʳ` on the small pro-étale site, regarded as a complex in degree `0`, is bounded
constructible.

Constructibility on the pro-étale site is étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`). The free module `Λ_Xʳ` is
`ν^*` of the constructible étale sheaf `Λ_{X_ét}ʳ`, and the idempotent of `Λ_Xʳ` cutting out
`P` comes from an endomorphism `e'` of `Λ_{X_ét}ʳ`, as `ν^*` is full
(`AlgebraicGeometry.ProEtale.full_comparisonUpperStar`). Since `ν^*` is exact, `P` is `ν^*` of
the kernel of `1 - e'`, which is constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.kernel`). -/
theorem boundedConstructible_single_of_retract
    (hP : Retract P (⨁ fun _ : Fin r ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)))) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj P) := by
  let N := ν^*(X)[ModuleCat.{u + 1} Λ]
  let L' := ⨁ fun _ : Fin r ↦ 𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let eL : N.obj L' ≅ ⨁ fun _ : Fin r ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)) :=
    N.mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ comparisonUpperStarUnitIso Λ X
  let ι : P ⟶ N.obj L' := hP.i ≫ eL.inv
  let π : N.obj L' ⟶ P := eL.hom ≫ hP.r
  have hιπ : ι ≫ π = 𝟙 P := by simp [ι, π, hP.retract]
  let e' : L' ⟶ L' := N.preimage (π ≫ ι)
  have he' : N.map (𝟙 L' - e') = 𝟙 _ - π ≫ ι := by simp [e']
  have : IsConstructibleSheaf L' := IsConstructibleSheaf.biproduct _
  have : IsConstructibleSheaf (kernel (𝟙 L' - e')) := IsConstructibleSheaf.kernel _
  -- `ι` is a kernel of `1 - π ≫ ι`
  have hlim : IsLimit (KernelFork.ofι (f := 𝟙 _ - π ≫ ι) ι (by
      simp [Preadditive.comp_sub, reassoc_of% hιπ])) :=
    KernelFork.IsLimit.ofι _ _ (fun g _ ↦ g ≫ π)
      (fun g hg ↦ by
        rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hg
        simpa using hg.symm)
      (fun g hg m hm ↦ by
        rw [← hm]
        simp [hιπ])
  let eP : N.obj (kernel (𝟙 L' - e')) ≅ P :=
    PreservesKernel.iso N _ ≪≫ kernelIsoOfEq he' ≪≫
      (limit.isLimit _).conePointUniqueUpToIso hlim
  exact ⟨_, Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
    ⟨(N.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso eP⟩⟩

omit [Finite Λ] in
/-- A finite projective `Λ_X`-module `P`, that is, a direct summand of a finite free module
`Λ_Xʳ` on the small pro-étale site, regarded as a complex in degree `0`, has Tor amplitude in
`[0, 0]`: `P` is flat, as a retract of the flat module `Λ_Xʳ`. -/
theorem torAmplitudeIn_single_of_retract
    (hP : Retract P (⨁ fun _ : Fin r ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)))) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj P) := by
  refine _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
    (ObjectProperty.flat_of_retract hP ?_)
  have h := ObjectProperty.flat_coproduct (fun _ : ULift.{u + 1} (Fin r) ↦
    𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    fun _ ↦ ObjectProperty.flat_of_isDualizable isDualizable_unit
  exact ObjectProperty.prop_of_iso _ ((Sigma.whiskerEquiv Equiv.ulift.symm
    (fun _ ↦ Iso.refl _)).symm ≪≫ (biproduct.isoCoproduct _).symm) h

/-- Blueprint `prop-pod-perfect-local-model`: The local finite projective model.

A finite projective `Λ_X`-module `P` on the small pro-étale site, that is, a direct summand of
a finite free module `Λ_Xʳ`, is flat and constructible: regarded as a complex in degree `0`, it
is bounded constructible with homology and Tor amplitude concentrated in degree `0`. -/
theorem constructibleTorAmplitudeIn_single_of_retract
    (hP : Retract P (⨁ fun _ : Fin r ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)))) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj P) :=
  have h := torAmplitudeIn_single_of_retract hP
  ⟨⟨boundedConstructible_single_of_retract hP,
    _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn h⟩, h⟩

end FiniteProjective

variable [IsNoetherian X] in
/-- Blueprint `prop-pod-perfect-local-model`: The local finite projective model.

A perfect complex of pro-étale `Λ`-sheaves, that is a complex locally quasi-isomorphic to a
bounded complex of finite projective `Λ_X`-modules (rendered as a dualizable object of
`D(X_proét)`), has bounded constructible cohomology sheaves and finite Tor amplitude: it lies
in `Dctf(X, Λ)`. -/
theorem constructibleFiniteTor_of_isDualizable
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K :=
  sorry

omit [Finite Λ] in
/-- The coefficient dual of `K ≅ ν^* K'` is of étale origin as soon as
`ν^* RHom(K', Λ) ≅ RHom(ν^* K', ν^* Λ)` and `RHom(K', Λ)` is bounded constructible. -/
theorem boundedConstructible_derivedDual_of_iso
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K' ≅ K)
    (c : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
        (((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K')).obj (𝟙_ _)) ≅
      ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
        (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K'))).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (𝟙_ _)))
    (hH : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        (((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K')).obj (𝟙_ _))) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((derivedDual (ModuleCat.{u + 1} Λ) X).obj (op K)) :=
  have h : boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj (𝟙_ _)) :=
    (boundedConstructible _ X).prop_of_iso
      (c ≪≫ ((ProEtale.derivedHom _ X).mapIso e.op.symm).app _ ≪≫
        ((ProEtale.derivedHom _ X).obj (op K)).mapIso
          (mapDerivedCategoryComparisonUpperStarUnitIso Λ X))
      (boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hH)
  h

end DerivedCategory

/-- Blueprint `lem-pod-coefficient-dual-perfect`: Perfectness is preserved by coefficient
duality.

Let `X` be of finite type over an algebraically closed field `k` and `Λ` a finite ring whose
exponent is invertible on `X`. The coefficient dual `K^∨ = RHom(K, Λ_X)` of a perfect complex
`K ∈ Dctf(X, Λ)` of pro-étale `Λ`-sheaves lies in `Dctf(X, Λ)`.

As `K` is of étale origin, `K ≅ ν^* K'` with `K' ∈ Dctf(X_ét, Λ)`
(`lem-sf-comparison-tor-amplitude`), and `K^∨ ≅ RHom(ν^* K', ν^* Λ) ≅ ν^* RHom(K', Λ)`
(`thm-sf-hom-comparison-constructible`) is of étale origin, `RHom(K', Λ)` being bounded
constructible on `X_ét` (`sk-thm-sf-hom-ctf`). As `K` is perfect, `K^∨` is its dual, whose Tor
amplitude is that of `K` reflected
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_derivedDual`). -/
theorem constructibleFiniteTor_derivedDual {k : Type u} [Field k] [IsAlgClosed k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent Λ X]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hKd : IsDualizable K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((derivedDual (ModuleCat.{u + 1} Λ) X).obj (op K)) := by
  obtain ⟨⟨K', hK', ⟨e⟩⟩, a, b, hKt⟩ := hK
  refine ⟨?_, -b, -a, DerivedCategory.torAmplitudeIn_derivedDual hKt hKd⟩
  -- `K'` has Tor amplitude in `[a, b]` on the étale site
  have hKt' : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K' :=
    DerivedCategory.torAmplitudeIn_of_mapDerivedCategory Λ hK'.1.1
      (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hK')
      ((DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm hKt)
  -- the unit `Λ_{X_ét}` is bounded constructible of Tor amplitude `[0, 0]`
  have hU : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
    (Etale.DerivedCategory.boundedConstructible _ X).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0)
  have hUt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0 (𝟙_ _) :=
    (Etale.DerivedCategory.torAmplitudeIn _ X 0 0).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))
  obtain ⟨c⟩ := DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom Λ aX
    ⟨hK', a, b, hKt'⟩ hU
  exact DerivedCategory.boundedConstructible_derivedDual_of_iso Λ e c
    (Etale.boundedConstructible_derivedHom Λ aX a b 0 0 hK' hKt' hU hUt)

end ProEtale

end AlgebraicGeometry
