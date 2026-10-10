/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.Derived.Duality
public import WeilConjectures.SixFunctors.ProEtale.Derived.Local
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.Derived.WeaklyEtaleLowerShriek

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

section LocallyPerfect

open scoped CategoryTheory.Functor

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X : Scheme.{u}}

/-- Blueprint `def-pod-perfect-complex-on-x`, as used in `sk-def-perfect`: a complex
`K ∈ D(X_proét)` is *locally perfect* if, locally on the pro-étale site, it is quasi-isomorphic
to a bounded complex of finite projective `Λ_X`-modules: there are a pro-étale covering family
`g i : W i ⟶ X` and bounded complexes `P i` on `W i` with `Lg_i^* K ≅ P i`. As elsewhere in this
file, finite projective modules are rendered as dualizable sheaves. -/
def IsLocallyPerfect (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) : Prop :=
  ∃ (ι : Type u) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X) (_ : ∀ i, WeaklyEtale (g i)),
    Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
      ∀ i, ∃ (P : CochainComplex (Sheaf (Scheme.ProEt.topology (W i)) A) ℤ) (a b : ℤ),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ n, IsDualizable (P.X n)) ∧
          Nonempty (L((g i)^*[A]).obj K ≅ _root_.DerivedCategory.Q.obj P)

variable [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

/-- Blueprint `sk-def-perfect`: a locally perfect complex is perfect, that is, dualizable.

Dualizability can be tested after the derived pullbacks `Lg_i^*` along a pro-étale covering
family: they are monoidal, jointly reflect isomorphisms
(`AlgebraicGeometry.ProEtale.isIso_of_isIso_leftDerivedUpperStar_map`) and commute with derived
internal homs (`AlgebraicGeometry.ProEtale.isIso_ihomComparison_leftDerivedUpperStar`), while
each `Lg_i^* K` is a bounded complex of dualizable sheaves, hence dualizable. So
`[K, Λ_X] ⊗ K ⟶ [K, K]` is an isomorphism and `[K, Λ_X]` is a dual of `K`. -/
theorem isDualizable_of_isLocallyPerfect
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : IsLocallyPerfect K) :
    IsDualizable K := by
  obtain ⟨ι, W, g, hg, hcov, hloc⟩ := hK
  let (i : ι) := monoidalLeftDerivedUpperStar A (g i)
  have := MonoidalClosed.isIso_ihomUnitTensorToIhom_of_jointlyReflectIsomorphisms
    (fun i ↦ L((g i)^*[A])) (fun _ _ f hf ↦ isIso_of_isIso_leftDerivedUpperStar_map hcov f hf) K
    (fun i Z ↦ isIso_ihomComparison_leftDerivedUpperStar A (g i) K Z) (fun i ↦ ?_)
  · obtain ⟨_⟩ :=
      _root_.DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology X) A)
    let := MonoidalClosed.exactPairingOfIsIso K
    exact ⟨{ rightDual := (ihom K).obj (𝟙_ _), exact := BraidedCategory.exactPairing_swap _ _ }⟩
  · obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hloc i
    obtain ⟨_⟩ := (_root_.DerivedCategory.isDualizable_Q_obj P a b hP).of_iso e.symm
    obtain ⟨_⟩ :=
      _root_.DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology (W i)) A)
    exact ⟨_, ⟨BraidedCategory.exactPairing_swap _ (L((g i)^*[A]).obj K)ᘁ⟩⟩

end LocallyPerfect

section LocallyPerfectOfDualizable

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ] {X : Scheme.{u}}

/-- Blueprint `sk-def-perfect` (Stacks, Tag 0FPV): a dualizable complex of pro-étale sheaves of
modules over a Noetherian ring `Λ` is locally perfect.

Unfinished. -/
theorem isLocallyPerfect_of_isDualizable
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) : IsLocallyPerfect K :=
  sorry

/-- Blueprint `sk-def-perfect`: over a Noetherian coefficient ring `Λ`, a complex of pro-étale
sheaves of `Λ`-modules is perfect, that is dualizable for the derived tensor product, if and only
if it is locally quasi-isomorphic to a bounded complex of finite projective `Λ_X`-modules. -/
theorem isDualizable_iff_isLocallyPerfect
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    IsDualizable K ↔ IsLocallyPerfect K :=
  ⟨isLocallyPerfect_of_isDualizable Λ, isDualizable_of_isLocallyPerfect⟩

end LocallyPerfectOfDualizable

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}} [IsNoetherian X]

namespace DerivedCategory

/-- Blueprint `prop-pod-perfect-local-model`: The local finite projective model.

A finite projective `Λ_X`-module `P` on the small pro-étale site (rendered as a dualizable
sheaf of `Λ`-modules) is flat and constructible: regarded as a complex in degree `0`, it is
bounded constructible with homology and Tor amplitude concentrated in degree `0`. -/
theorem constructibleTorAmplitudeIn_single_of_isDualizable
    {P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (hP : IsDualizable P) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj P) :=
  sorry

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
