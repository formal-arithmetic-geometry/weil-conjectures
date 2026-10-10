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
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Conservative

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
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_Q_obj_of_retract`
  (`prop-pod-perfect-local-model`): a bounded complex of finite projective `Λ_X`-modules lies in
  `Dctf(X, Λ)`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_of_isDualizable`
  (`prop-pod-perfect-local-model`): a perfect complex lies in `Dctf(X, Λ)`. The proof follows
  the local model: it uses `sk-def-perfect` and `lem-sf-proetale-constructible-origin`, and the
  local constancy of the cohomology of a bounded complex of finite projective modules
  (`AlgebraicGeometry.ProEtale.DerivedCategory.isFiniteLocallyConstant_homology_of_retract`),
  which is still `sorry`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_boundedConstructible`:
  `Dᵇc_proét(X, Λ)` is a triangulated subcategory at a finite coefficient ring.
- `AlgebraicGeometry.ProEtale.isDualizable_derivedDual` (`lem-pod-coefficient-dual-perfect`):
  the coefficient dual of a perfect complex is perfect.
- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_derivedDual`
  (`lem-pod-coefficient-dual-perfect`): the coefficient dual of a perfect complex in
  `Dctf(X, Λ)` lies in `Dctf(X, Λ)`.

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
since `Λ_Xʳ = ν^* Λ_{X_ét}ʳ` and `ν^*` is full and exact; so is a bounded complex of them, as
`ν^*` is fully faithful.

As in the blueprint (`def-pod-perfect-complex-on-x`), the coefficient dual is shown to lie in
`Dctf(X, Λ)` for perfect complexes which already lie in `Dctf(X, Λ)`, in the Poincaré duality
setting of a scheme of finite type over an algebraic closure of `𝔽_p` and a coefficient ring
whose exponent is invertible on `X`. The proof goes through the étale site rather than through
the local model: `K = ν^* K'` and `K^∨ ≅ ν^* RHom(K', Λ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom`), which
only needs `RHom(K', Λ)` to be constructible on `X_ét`.

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

section FiniteProjective

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Λ} {P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} {r : ℕ}

/-- A finite projective `Λ_X`-module `P`, that is, a direct summand of a finite free module
`Λ_Xʳ` on the small pro-étale site, is `ν^*` of a constructible étale sheaf.

The free module `Λ_Xʳ` is `ν^*` of the constructible étale sheaf `Λ_{X_ét}ʳ`, and the idempotent
of `Λ_Xʳ` cutting out `P` comes from an endomorphism `e'` of `Λ_{X_ét}ʳ`, as `ν^*` is full
(`AlgebraicGeometry.ProEtale.full_comparisonUpperStar`). Since `ν^*` is exact, `P` is `ν^*` of
the kernel of `1 - e'`, which is constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.kernel`). -/
theorem exists_isConstructibleSheaf_iso_comparisonUpperStar_obj_of_retract
    (hP : Retract P (⨁ fun _ : Fin r ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)))) :
    ∃ Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsConstructibleSheaf Q ∧ Nonempty ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj Q ≅ P) := by
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
  exact ⟨kernel (𝟙 L' - e'), IsConstructibleSheaf.kernel _,
    ⟨PreservesKernel.iso N _ ≪≫ kernelIsoOfEq he' ≪≫
      (limit.isLimit _).conePointUniqueUpToIso hlim⟩⟩

omit [Finite Λ] in
/-- A finite projective `Λ_X`-module `P`, that is, a direct summand of a finite free module
`Λ_Xʳ` on the small pro-étale site, is flat, as a retract of the flat module `Λ_Xʳ`. -/
theorem flat_of_retract
    (hP : Retract P (⨁ fun _ : Fin r ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)))) :
    ObjectProperty.flat P := by
  refine ObjectProperty.flat_of_retract hP ?_
  have h := ObjectProperty.flat_coproduct (fun _ : ULift.{u + 1} (Fin r) ↦
    𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    fun _ ↦ ObjectProperty.flat_of_isDualizable isDualizable_unit
  exact ObjectProperty.prop_of_iso _ ((Sigma.whiskerEquiv Equiv.ulift.symm
    (fun _ ↦ Iso.refl _)).symm ≪≫ (biproduct.isoCoproduct _).symm) h

namespace DerivedCategory

/-- A finite projective `Λ_X`-module `P`, that is, a direct summand of a finite free module
`Λ_Xʳ` on the small pro-étale site, regarded as a complex in degree `0`, is bounded
constructible: it is `ν^*` of a constructible étale sheaf
(`AlgebraicGeometry.ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj_of_retract`).
-/
theorem boundedConstructible_single_of_retract
    (hP : Retract P (⨁ fun _ : Fin r ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)))) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj P) := by
  obtain ⟨Q, _, ⟨eP⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj_of_retract hP
  exact ⟨_, Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
    ⟨((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso eP⟩⟩

omit [Finite Λ] in
/-- A finite projective `Λ_X`-module `P`, that is, a direct summand of a finite free module
`Λ_Xʳ` on the small pro-étale site, regarded as a complex in degree `0`, has Tor amplitude in
`[0, 0]`: `P` is flat, as a retract of the flat module `Λ_Xʳ`. -/
theorem torAmplitudeIn_single_of_retract
    (hP : Retract P (⨁ fun _ : Fin r ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)))) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj P) :=
  _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat (flat_of_retract hP)

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


/-- Blueprint `prop-pod-perfect-local-model`: The local finite projective model.

A bounded complex `P` of finite projective `Λ_X`-modules on the small pro-étale site, each a
direct summand of a finite free module `Λ_Xʳ`, lies in `Dctf(X, Λ)`. Its terms are flat, so it
has finite Tor amplitude (`_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat`). Each term is
`ν^*` of a constructible étale sheaf, and as `ν^*` is fully faithful so is `P` of a bounded
complex `P'` of constructible étale sheaves. The cohomology sheaves of `P'` are constructible,
as constructible sheaves are closed under kernels and cokernels, so `P = ν^* P'` is bounded
constructible. -/
theorem constructibleFiniteTor_Q_obj_of_retract
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ n, ∃ r : ℕ, Nonempty (Retract (P.X n) (⨁ fun _ : Fin r ↦
      𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))))) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (_root_.DerivedCategory.Q.obj P) := by
  refine ⟨?_, a, b, _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat P a b fun n ↦ by
    obtain ⟨r, ⟨h⟩⟩ := hP n
    exact flat_of_retract h⟩
  let N := ν^*(X)[ModuleCat.{u + 1} Λ]
  have h (n : ℤ) : ∃ Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsConstructibleSheaf Q ∧ Nonempty (N.obj Q ≅ P.X n) := by
    obtain ⟨r, ⟨h⟩⟩ := hP n
    exact exists_isConstructibleSheaf_iso_comparisonUpperStar_obj_of_retract h
  choose Q hQ e using h
  let e (n : ℤ) := (e n).some
  -- the étale complex `P'` with `ν^* P' ≅ P`
  let P' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ :=
    { X := Q
      d i j := N.preimage ((e i).hom ≫ P.d i j ≫ (e j).inv)
      shape i j hij := N.map_injective (by simp [P.shape i j hij])
      d_comp_d' i j k _ _ := N.map_injective (by simp) }
  let eP : (N.mapHomologicalComplex _).obj P' ≅ P :=
    HomologicalComplex.Hom.isoOfComponents e (fun i j _ ↦ by simp [P'])
  have hz (n : ℤ) (hn : IsZero (P.X n)) : IsZero (Q n) :=
    (IsZero.iff_id_eq_zero _).2 (N.map_injective (by
      rw [N.map_id, N.map_zero]
      exact (hn.of_iso (e n)).eq_of_src _ _))
  have : P'.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff P' a).2 fun i hi ↦
    hz i (P.isZero_of_isStrictlyGE a i hi)
  have : P'.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff P' b).2 fun i hi ↦
    hz i (P.isZero_of_isStrictlyLE b i hi)
  -- the cohomology sheaves of `P'` are constructible
  have hQ' (n : ℤ) : Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X (Q n) :=
    (Etale.constructibleSheaf_iff _ _ _).2 (hQ n)
  have hH (n : ℤ) : IsConstructibleSheaf (P'.homology n) := by
    have hcycles := (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).prop_of_isLimit_kernelFork
      (P'.sc n).cyclesIsKernel (hQ' _) (hQ' _)
    exact (Etale.constructibleSheaf_iff _ _ _).1
      ((Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).prop_of_isColimit_cokernelCofork
        (P'.sc n).homologyIsCokernel (hQ' _) hcycles)
  have hb : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (_root_.DerivedCategory.Q.obj P') := by
    refine ⟨⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩, fun n ↦ ?_⟩
    have : IsConstructibleSheaf ((HomologicalComplex.homologyFunctor _ _ n).obj P') := hH n
    exact IsConstructibleSheaf.of_iso
      ((_root_.DerivedCategory.homologyFunctorFactors _ n).app P').symm
  exact ⟨_, hb, ⟨N.mapDerivedCategoryFactors.app P' ≪≫ _root_.DerivedCategory.Q.mapIso eP⟩⟩

end DerivedCategory

end FiniteProjective

namespace DerivedCategory

section Triangulated

variable (X)

/-- At a finite coefficient ring, the bounded constructible pro-étale complexes form a
triangulated subcategory of `D(X_proét)`. They are the complexes of étale origin, and `ν^*` is
triangulated and fully faithful on bounded below complexes
(`AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map`), so the cone
of a map between complexes of étale origin is `ν^*` of the cone of a lift of this map. -/
instance isTriangulated_boundedConstructible :
    (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulated := by
  let F := D(ν^*(X)[ModuleCat.{u + 1} Λ])
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulatedClosed₃ := by
    refine ObjectProperty.IsTriangulatedClosed₃.mk' fun T hT ⟨A, hA, ⟨e₁⟩⟩ ⟨B, hB, ⟨e₂⟩⟩ ↦ ?_
    obtain ⟨f, hf⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map A B hB.1.1).2
      (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
    obtain ⟨Z, g, h, hZ⟩ := Pretriangulated.distinguished_cocone_triangle f
    obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ T
      (F.map_distinguished _ hZ) hT (Arrow.isoMk e₁ e₂ (by
        have hf' : F.map f = e₁.hom ≫ T.mor₁ ≫ e₂.inv := hf
        change e₁.hom ≫ T.mor₁ = F.map f ≫ e₂.hom
        simp [hf']))
    exact ⟨Z, (Etale.DerivedCategory.boundedConstructible _ X).ext_of_isTriangulatedClosed₃ _
      hZ hA hB, ⟨Pretriangulated.Triangle.π₃.mapIso e⟩⟩
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun K ⟨A, hA, ⟨e⟩⟩ ↦ ⟨A⟦n⟧,
      (Etale.DerivedCategory.boundedConstructible _ X).le_shift n _ hA,
      ⟨(F.commShiftIso n).app A ≪≫ (shiftFunctor _ n).mapIso e⟩⟩⟩⟩
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃
  obtain ⟨Z, hZ, hZP⟩ := ObjectProperty.ContainsZero.exists_zero
    (P := Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X)
  exact { exists_zero := ⟨F.obj Z, F.map_isZero hZ,
    boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hZP⟩ }

variable {X}

/-- At a finite coefficient ring, a bounded pro-étale complex is bounded constructible as soon as
each of its cohomology sheaves is `ν^*` of a constructible étale sheaf. -/
theorem boundedConstructible_of_homology
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.TStructure.t.bounded K)
    (hH : ∀ n, ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F ∧
      Nonempty ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F ≅
        (_root_.DerivedCategory.homologyFunctor _ n).obj K)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  let P : ObjectProperty (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
    fun G ↦ ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F ∧
      Nonempty ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F ≅ G)
  have : P.IsClosedUnderIsomorphisms := ⟨fun e ⟨F, hF, ⟨e'⟩⟩ ↦ ⟨F, hF, ⟨e' ≪≫ e⟩⟩⟩
  refine _root_.DerivedCategory.prop_of_bounded _ P (fun G ⟨F, hF, ⟨e⟩⟩ ↦ ?_) K hK hH
  exact ⟨_, Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
    ⟨((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso e⟩⟩

end Triangulated

section Local

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Blueprint `def-pod-perfect-complex-on-x`: a complex `K` of pro-étale `Λ`-sheaves on `X` is
*locally perfect* if there is a pro-étale covering family `g i : W i ⟶ X` such that every
derived pullback `Lg_i^* K` is quasi-isomorphic to a bounded complex of finite projective
`Λ_{W_i}`-modules, that is, of direct summands of finite free modules. -/
def IsLocallyPerfect (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} Λ))) : Prop :=
  ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
    Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
      ∀ i, ∃ (P : CochainComplex (Sheaf (Scheme.ProEt.topology (W i))
          (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ n, ∃ r : ℕ, Nonempty (Retract (P.X n) (⨁ fun _ : Fin r ↦
          𝟙_ (Sheaf (Scheme.ProEt.topology (W i)) (ModuleCat.{u + 1} Λ))))) ∧
        Nonempty ((L((g i)^*[ModuleCat.{u + 1} Λ])).obj K ≅ _root_.DerivedCategory.Q.obj P)

omit [Finite Λ] in
/-- Blueprint `sk-def-perfect`: Perfectness at the point and on `X`.

An object `K ∈ D(X_proét, Λ)` which is perfect over `Λ_X`, that is dualizable, is locally
quasi-isomorphic to a bounded complex of finite projective `Λ_X`-modules. -/
theorem isLocallyPerfect_of_isDualizable
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) : IsLocallyPerfect Λ K :=
  sorry

variable {Λ}

omit [Finite Λ] in
/-- Being locally constant with finite stalks is invariant under isomorphism. -/
theorem isFiniteLocallyConstant_of_iso
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    (hF : IsFiniteLocallyConstant Λ F) : IsFiniteLocallyConstant Λ G := by
  obtain ⟨ι, W, g, hg, h⟩ := hF
  refine ⟨ι, W, g, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e'⟩⟩ := h i
  exact ⟨M, hM, ⟨((g i)^*[ModuleCat.{u + 1} Λ]).mapIso e.symm ≪≫ e'⟩⟩

omit [Finite Λ] in
/-- Being locally constant with finite stalks is local for the pro-étale topology. -/
theorem isFiniteLocallyConstant_of_cover
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} {ι : Type (u + 1)}
    {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (h : ∀ i, IsFiniteLocallyConstant Λ (((g i)^*[ModuleCat.{u + 1} Λ]).obj F)) :
    IsFiniteLocallyConstant Λ F := by
  choose σ V f hf hc using h
  refine ⟨Σ i, σ i, fun p ↦ V p.1 p.2, fun p ↦ f p.1 p.2 ≫ g p.1,
    Precoverage.IsStableUnderComposition.comp_mem_coverings g hg f hf, fun ⟨i, j⟩ ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hc i j
  exact ⟨M, hM, ⟨(upperStarComp _ (f i j) (g i)).app F ≪≫ e⟩⟩

omit [Finite Λ] in
/-- The cohomology sheaves of a bounded complex of finite projective `Λ_W`-modules on the small
pro-étale site of `W` are locally constant with finite stalks.

This is not formalised yet: the differentials are locally constant (sections of a constant sheaf
are locally constant), but this needs that the pullback of a constant sheaf along a weakly étale
morphism is constant, and the comparison of morphisms between constant sheaves with sections. -/
theorem isFiniteLocallyConstant_homology_of_retract [Finite Λ] {W : Scheme.{u}}
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ)) ℤ)
    (hP : ∀ n, ∃ r : ℕ, Nonempty (Retract (P.X n) (⨁ fun _ : Fin r ↦
      𝟙_ (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ))))) (n : ℤ) :
    IsFiniteLocallyConstant Λ (P.homology n) :=
  sorry

omit [Finite Λ] in
/-- A sheaf whose pullbacks along the members of a pro-étale covering family vanish is zero. -/
theorem isZero_of_cover {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (h : ∀ i, IsZero (((g i)^*[ModuleCat.{u + 1} Λ]).obj G)) : IsZero G := by
  have (i : ι) : WeaklyEtale (g i) := proetalePrecoverage_le_precoverage_weaklyEtale _ hg ⟨i⟩
  have hz (i : ι) := ((h i).of_iso
    ((upperStarIsoLocalizationRestriction _ (g i) inferInstance).app G).symm).isoZero
  have := isIso_of_isIso_localizationRestriction (ModuleCat.{u + 1} Λ)
    (0 : G ⟶ G) g hg fun i ↦ isIso_of_source_target_iso_zero _ (hz i) (hz i)
  refine (IsZero.iff_id_eq_zero G).2 ?_
  rw [← IsIso.hom_inv_id (0 : G ⟶ G), zero_comp]

omit [Finite Λ] in
/-- A locally perfect complex on a quasi-compact quasi-separated scheme is bounded: finitely
many affine opens of members of the trivializing cover still cover `X`, and the bounds of the
finitely many local models bound the cohomology sheaves. -/
theorem bounded_of_isLocallyPerfect [CompactSpace X] [QuasiSeparatedSpace X]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsLocallyPerfect Λ K) : _root_.DerivedCategory.TStructure.t.bounded K := by
  obtain ⟨ι, W, g, hg, hP⟩ := hK
  choose P a b ha hb hr e using hP
  have (i : ι) : WeaklyEtale (g i) := proetalePrecoverage_le_precoverage_weaklyEtale _ hg ⟨i⟩
  let E : PreZeroHypercover X := ⟨ι, W, g⟩
  have : QuasiCompactCover E := by
    have := hg.1
    rwa [show Presieve.ofArrows W g = E.presieve₀ from rfl,
      presieve₀_mem_qcPrecoverage_iff] at this
  obtain ⟨n, c, V, hV, hU⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact E (U := ⊤) isCompact_univ
  have (k : Fin n) : IsAffine (V k).toScheme := hV k
  let h (k : ULift.{u + 1} (Fin n)) : (V k.down).toScheme ⟶ X := (V k.down).ι ≫ g (c k.down)
  let 𝒰 : X.Cover (precoverage @WeaklyEtale) :=
    Cover.mkOfCovers (ULift.{u + 1} (Fin n)) (fun k ↦ (V k.down).toScheme) h (fun x ↦ by
      have hx : x ∈ ((⊤ : X.Opens) : Set X) := trivial
      rw [← hU] at hx
      obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      obtain ⟨y, rfl⟩ : y ∈ Set.range (V k).ι := by rwa [Scheme.Opens.range_ι]
      exact ⟨⟨k⟩, y, by simp [h, E]⟩)
  have : Finite 𝒰.I₀ := inferInstanceAs (Finite (ULift.{u + 1} (Fin n)))
  have (k : 𝒰.I₀) : QuasiCompact (𝒰.f k) := by
    change QuasiCompact (h k)
    exact quasiCompact_of_compactSpace _
  have hcov : Presieve.ofArrows (fun k ↦ (V (ULift.down k)).toScheme) h ∈
      Scheme.proetalePrecoverage X := by
    have : Scheme.JointlySurjective (Scheme.precoverage.{u} @WeaklyEtale) :=
      Scheme.instJointlySurjectivePrecoverage
    exact mem_propQCPrecoverage_iff_exists_quasiCompactCover.2
      ⟨𝒰, QuasiCompactCover.of_finite, rfl⟩
  -- bounds valid for all members of the finite family
  let A : ℤ := -∑ k, |a (c k)|
  let B : ℤ := ∑ k, |b (c k)|
  have hA (k : Fin n) : A ≤ a (c k) := by
    have := Finset.single_le_sum (f := fun k ↦ |a (c k)|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ k)
    have := neg_abs_le (a (c k))
    simp only [A]; lia
  have hB (k : Fin n) : b (c k) ≤ B := by
    have := Finset.single_le_sum (f := fun k ↦ |b (c k)|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ k)
    have := le_abs_self (b (c k))
    simp only [B]; lia
  -- the cohomology sheaf in degree `m` vanishes as soon as it does on every `P (c k)`
  have hz (m : ℤ) (hm : ∀ k, IsZero ((P (c k)).homology m)) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj K) := by
    refine isZero_of_cover h hcov fun k ↦ ?_
    refine IsZero.of_iso ?_ ((upperStarComp _ (V k.down).ι (g (c k.down))).app _)
    refine Functor.map_isZero ((V k.down).ι)^*[ModuleCat.{u + 1} Λ] ?_
    refine (hm k.down).of_iso ?_
    exact ((leftDerivedUpperStarHomologyFunctorIso _ (g (c k.down)) m).app K) ≪≫
      (_root_.DerivedCategory.homologyFunctor _ m).mapIso (e (c k.down)).some ≪≫
      (_root_.DerivedCategory.homologyFunctorFactors _ m).app _
  refine ⟨⟨A, (_root_.DerivedCategory.isGE_iff K A).2 fun m hm ↦ hz m fun k ↦ ?_⟩,
    ⟨B, (_root_.DerivedCategory.isLE_iff K B).2 fun m hm ↦ hz m fun k ↦ ?_⟩⟩
  · exact ((_root_.DerivedCategory.homologyFunctorFactors _ m).app _).isZero_iff.1
      ((_root_.DerivedCategory.Q.obj (P (c k))).isZero_of_isGE (a (c k)) m
        (by have := hA k; lia))
  · exact ((_root_.DerivedCategory.homologyFunctorFactors _ m).app _).isZero_iff.1
      ((_root_.DerivedCategory.Q.obj (P (c k))).isZero_of_isLE (b (c k)) m
        (by have := hB k; lia))

variable [IsNoetherian X] in
/-- A perfect complex of pro-étale `Λ`-sheaves on a Noetherian scheme is bounded, and each of its
cohomology sheaves is `ν^*` of a constructible étale sheaf.

It is locally quasi-isomorphic to a bounded complex `P` of finite projective modules
(`sk-def-perfect`), so it is bounded (`bounded_of_isLocallyPerfect`) and its cohomology sheaves
are locally those of `P`, hence locally constant with finite stalks
(`isFiniteLocallyConstant_homology_of_retract`, `isFiniteLocallyConstant_of_cover`). They are
then constructible for the trivial stratification, hence of étale origin
(`lem-sf-proetale-constructible-origin`). -/
theorem bounded_and_homology_of_isDualizable
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    _root_.DerivedCategory.TStructure.t.bounded K ∧
      ∀ n, ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F ∧
        Nonempty ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F ≅
          (_root_.DerivedCategory.homologyFunctor _ n).obj K) := by
  have hK' := isLocallyPerfect_of_isDualizable Λ hK
  refine ⟨bounded_of_isLocallyPerfect hK', fun n ↦ ?_⟩
  obtain ⟨ι, W, g, hg, hP⟩ := hK'
  have hloc : IsFiniteLocallyConstant Λ
      ((_root_.DerivedCategory.homologyFunctor _ n).obj K) := by
    refine isFiniteLocallyConstant_of_cover g hg fun i ↦ ?_
    obtain ⟨P, a, b, _, _, hr, ⟨e⟩⟩ := hP i
    exact isFiniteLocallyConstant_of_iso
      (((_root_.DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
        (_root_.DerivedCategory.homologyFunctorFactors _ n).app P).symm ≪≫
        ((leftDerivedUpperStarHomologyFunctorIso _ (g i) n).app K).symm)
      (isFiniteLocallyConstant_homology_of_retract P hr n)
  -- the trivial stratification of `X`
  let S : Stratification X := Stratification.ofNoetherianSpace 1 (fun _ ↦ Set.univ)
    (fun _ ↦ isOpen_univ.isLocallyClosed) (Set.iUnion_const _)
    (fun i j h ↦ (h (Subsingleton.elim i j)).elim)
    (fun _ ↦ X) (fun _ ↦ 𝟙 X) (fun _ ↦ inferInstance) (fun _ ↦ by simp)
  obtain ⟨F, hF, e⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ
    (F := (_root_.DerivedCategory.homologyFunctor _ n).obj K) ⟨S, fun _ ↦
      isFiniteLocallyConstant_of_iso ((upperStarId _ X).app _).symm hloc⟩
  exact ⟨F, hF, e⟩

end Local


variable [IsNoetherian X] in
/-- Blueprint `prop-pod-perfect-local-model`: The local finite projective model.

A perfect complex of pro-étale `Λ`-sheaves, that is a complex locally quasi-isomorphic to a
bounded complex of finite projective `Λ_X`-modules (rendered as a dualizable object of
`D(X_proét)`), has bounded constructible cohomology sheaves and finite Tor amplitude: it lies
in `Dctf(X, Λ)`.

It is bounded constructible by `bounded_and_homology_of_isDualizable` and
`boundedConstructible_of_homology`. So is its dual `Kᘁ`, and as both are bounded above `K` has
finite Tor amplitude (`_root_.DerivedCategory.torAmplitudeIn_of_exactPairing_of_isLE`). -/
theorem constructibleFiniteTor_of_isDualizable
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K := by
  have hbc {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
      (hL : IsDualizable L) : boundedConstructible (ModuleCat.{u + 1} Λ) X L :=
    have h := bounded_and_homology_of_isDualizable hL
    boundedConstructible_of_homology Λ h.1 h.2
  refine ⟨hbc hK, ?_⟩
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
  let := BraidedCategory.exactPairing_swap K Kᘁ
  obtain ⟨b, _⟩ := (hbc (L := K) ⟨inferInstance⟩).bounded.2
  obtain ⟨b', _⟩ := (hbc (L := Kᘁ) ⟨⟨K⟩⟩).bounded.2
  exact ⟨_, _, _root_.DerivedCategory.torAmplitudeIn_of_exactPairing_of_isLE (L := Kᘁ) b b'⟩

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

Let `X` be of finite type over an algebraic closure `k` of `𝔽_p` and `Λ` a finite ring whose
exponent is invertible on `X`. The coefficient dual `K^∨ = RHom(K, Λ_X)` of a perfect complex
`K ∈ Dctf(X, Λ)` of pro-étale `Λ`-sheaves lies in `Dctf(X, Λ)`.

As `K` is of étale origin, `K ≅ ν^* K'` with `K' ∈ Dctf(X_ét, Λ)`
(`lem-sf-comparison-tor-amplitude`), and `K^∨ ≅ RHom(ν^* K', ν^* Λ) ≅ ν^* RHom(K', Λ)`
(`thm-sf-hom-comparison-constructible`) is of étale origin, `RHom(K', Λ)` being bounded
constructible on `X_ét` (`sk-thm-sf-hom-ctf`). As `K` is perfect, `K^∨` is its dual, whose Tor
amplitude is that of `K` reflected
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_derivedDual`). -/
theorem constructibleFiniteTor_derivedDual {k : Type u} [Field k] {p : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
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
  obtain ⟨c⟩ := DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom Λ (p := p) aX
    ⟨hK', a, b, hKt'⟩ hU
  exact DerivedCategory.boundedConstructible_derivedDual_of_iso Λ e c
    (Etale.boundedConstructible_derivedHom Λ aX a b 0 0 hK' hKt' hU hUt)

end ProEtale

end AlgebraicGeometry
