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
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable

/-!

# Perfect complexes of pro-étale sheaves and their coefficient duals

Let `X` be a scheme. A complex `K ∈ D(X_proét)` is *perfect* over `Λ_X` if it is, locally on
the small pro-étale site, quasi-isomorphic to a bounded complex of finite projective
`Λ_X`-modules. As in `WeilConjectures.SixFunctors.Etale.Derived.Perfect`, perfectness is
rendered as dualizability for the derived tensor product, `CategoryTheory.IsDualizable`; for
sheaves of modules over a ringed site the two notions agree (Stacks, Tag 0FPV). Likewise a
*finite projective `Λ_X`-module* is rendered as a dualizable pro-étale sheaf.

This file proves that the coefficient dual `K^∨ = RHom(K, Λ_X)`
(`AlgebraicGeometry.ProEtale.derivedDual`) of a perfect complex is perfect, and, at a finite
coefficient ring `Λ`, lies in `Dctf(X, Λ)`.

## Main statements

- `AlgebraicGeometry.ProEtale.derivedDual_obj`,
  `AlgebraicGeometry.ProEtale.derivedDualEval_eq_uncurry` (`rem-ptr-pod-perfect-complex-on-x-5`):
  the coefficient dual and its evaluation `AlgebraicGeometry.ProEtale.derivedDualEval` are
  formed with the derived internal hom.
- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible_of_isDualizable`
  (`prop-pod-perfect-local-model`): a perfect complex is of étale origin and bounded
  constructible. The proof is `sorry`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTorAmplitudeIn_single_of_isDualizable`
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

Flatness and Tor amplitude of a perfect complex are formal consequences of dualizability
(`CategoryTheory.ObjectProperty.flat_of_isDualizable`,
`DerivedCategory.torAmplitudeIn_of_exactPairing_of_isLE`) once it is known to be bounded, which
`boundedConstructible_of_isDualizable` provides.

The statements about `Dctf(X, Λ)` are made at a finite coefficient ring `Λ` and a Noetherian
scheme `X`, as in the blueprint's setting: bounded constructibility is étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`), which is the right notion
only at the finite coefficient stages, and boundedness of a perfect complex needs `X` to be
quasi-compact.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

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

end Dualizable

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}} [IsNoetherian X]

namespace DerivedCategory

/-- Blueprint `prop-pod-perfect-local-model`, the constructibility half: a perfect complex of
pro-étale `Λ`-sheaves (rendered as a dualizable object of `D(X_proét)`) is of étale origin and
bounded constructible.

Locally on the pro-étale site it is a bounded complex of finite projective `Λ_X`-modules, so
its cohomology sheaves are locally constant with finite stalks; on the quasi-compact `X`
finitely many such neighbourhoods suffice, so it is bounded, and its cohomology sheaves
descend to constructible étale sheaves. -/
theorem boundedConstructible_of_isDualizable
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X K :=
  sorry

/-- Blueprint `prop-pod-perfect-local-model`: The local finite projective model.

A finite projective `Λ_X`-module `P` on the small pro-étale site (rendered as a dualizable
sheaf of `Λ`-modules) is flat and constructible: regarded as a complex in degree `0`, it is
bounded constructible with homology and Tor amplitude concentrated in degree `0`. -/
theorem constructibleTorAmplitudeIn_single_of_isDualizable
    {P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (hP : IsDualizable P) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj P) :=
  -- `P[0]` is dualizable in `D(X_proét)`, as a bounded complex of dualizable objects
  have hP' : IsDualizable ((_root_.DerivedCategory.singleFunctor _ 0).obj P) :=
    (_root_.DerivedCategory.isDualizable_Q_obj ((HomologicalComplex.single _ _ 0).obj P) 0 0
      fun n ↦ by
        by_cases hn : n = 0
        · subst hn
          exact hP.of_iso (HomologicalComplex.singleObjXSelf _ 0 P).symm
        · exact isDualizable_of_isZero (HomologicalComplex.isZero_single_obj_X _ 0 P n hn)).of_iso
      ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app P).symm
  ⟨⟨boundedConstructible_of_isDualizable Λ hP', inferInstance, inferInstance⟩,
    _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_isDualizable hP⟩

/-- Blueprint `prop-pod-perfect-local-model`: The local finite projective model.

A perfect complex of pro-étale `Λ`-sheaves, that is a complex locally quasi-isomorphic to a
bounded complex of finite projective `Λ_X`-modules (rendered as a dualizable object of
`D(X_proét)`), has bounded constructible cohomology sheaves and finite Tor amplitude: it lies
in `Dctf(X, Λ)`. -/
theorem constructibleFiniteTor_of_isDualizable
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K := by
  -- `K` and its right dual are bounded constructible, hence bounded above, which bounds the
  -- Tor amplitude of `K`
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
  have hK' := boundedConstructible_of_isDualizable Λ hK
  obtain ⟨_⟩ := hK
  have hL := boundedConstructible_of_isDualizable Λ
    ((IsDualizable.ihom_unit ⟨inferInstance⟩).of_iso (ihomUnitIsoRightDual K))
  obtain ⟨b, _⟩ := hK'.bounded.2
  obtain ⟨b', _⟩ := hL.bounded.2
  exact ⟨hK', -b', b,
    _root_.DerivedCategory.torAmplitudeIn_of_exactPairing_of_isLE (L := Kᘁ) b b'⟩

end DerivedCategory

/-- Blueprint `lem-pod-coefficient-dual-perfect`: Perfectness is preserved by coefficient
duality.

The coefficient dual `K^∨ = RHom(K, Λ_X)` of a perfect complex `K` of pro-étale `Λ`-sheaves
lies in `Dctf(X, Λ)`. -/
theorem constructibleFiniteTor_derivedDual
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((derivedDual (ModuleCat.{u + 1} Λ) X).obj (op K)) :=
  DerivedCategory.constructibleFiniteTor_of_isDualizable Λ (isDualizable_derivedDual hK)

end ProEtale

end AlgebraicGeometry
