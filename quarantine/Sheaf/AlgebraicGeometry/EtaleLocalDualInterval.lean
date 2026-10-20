/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-! # Uniform local models of a twisted coefficient dual

Source: Stacks Project, Cohomology on Sites, Tags 08JH and 08JJ
(blueprint: lem-sf-etale-local-dual-interval).
The ordinary constant-coefficient realization of derived internal Hom is the existing
`Etale.derivedHom`, the K-injective right derived internal Hom characterized by the
adjunction with the existing derived tensor. The variable `H` merely names its value.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A locally finite-projective complex in `[a,b]`, dualized into a locally constant line
shifted by `m`, has the signed local dual models and Tor interval `[-b-m,-a-m]`.
Source: Stacks Project, Tags 08JH, 08JJ, 08JB, 08JC and 08G1
(blueprint: lem-sf-etale-local-dual-interval).

Proof:
1. Refine the two covers to trivialize both the source model and the line. Exact slice
restriction (`lem-pur-site-restriction-module-adjunction-exact`) and derived Hom restriction
(`lem-weil-pbc-ringed-internal-hom-exact-restriction`) identify the restricted dual.
A finite-projective term is a retract of a finite free term. Its internal Hom functor is
therefore a retract of the exact finite-free Hom functor
(`lem-sc-finite-free-internal-hom-exact`). Apply
`lem-pc-bounded-exact-term-hom-quasi-iso` to the K-injective replacement in
`def-pur-derived-internal-hom`. This identifies ordinary and derived Hom.
2. The unshifted dual has degree-q term Hom(E^{-q},A); its differential is
(-1)^{q+1} times precomposition with d_E^{-q-1}. Dualize the finite-free splittings.
The cochain shift subtracts m from the reversed support interval.
3. Finite constant terms and constant differentials have finite constant kernels, images
and cohomology. Thus all cohomology sheaves are finite locally constant. The single
stratum T and the support bounds give `def-weil-pbc-constructible-complexes`.
4. Dual terms, as finite-free retracts, are flat. Apply
`lem-kun-flat-bounded-tor-amplitude` on each cover member. Derived tensor restriction
(`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`) and exact cohomology restriction
identify these local vanishings for every degree-zero module sheaf. The sheaf axiom
descends vanishing to T, giving `def-kun-tor-amplitude`.
The displayed degreewise isomorphisms specify the entire unshifted dual, including its
sign, without choosing an unspecified complex in the definition of derived Hom. -/
theorem etaleLocalDualInterval
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (a b m : ℤ) (hab : a ≤ b) (P : DerivedCategoryModule A T)
    (U : Scheme.Cover.{u} Scheme.etalePrecoverage T)
    (E : U.I₀ → CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hE : ∀ (i : U.I₀) (q : ℤ), ∃ (n : ℕ)
      (s : (E i).X q ⟶ ModuleCat.of A (Fin n → A))
      (r : ModuleCat.of A (Fin n → A) ⟶ (E i).X q), s ≫ r = 𝟙 _)
    (hEzero : ∀ (i : U.I₀) (q : ℤ), q < a ∨ b < q → IsZero ((E i).X q))
    (hP : ∀ i : U.I₀, Nonempty
      (((upperStar (ModuleCat.{u + 1} A) (U.f i)).leftDerivedFunctor.obj P) ≅
        _root_.DerivedCategory.Q.obj
          (((constantSheaf (U.X i).smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (E i))))
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (V : Scheme.Cover.{u} Scheme.etalePrecoverage T)
    (hL : ∀ i : V.I₀, Nonempty
      ((upperStar (ModuleCat.{u + 1} A) (V.f i)).obj L ≅
        (constantSheaf (V.X i).smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))
    (H : DerivedCategoryModule A T)
    (hH : H = ((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj
      (((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦m⟧)) :
    (∃ (W : Scheme.Cover.{u} Scheme.etalePrecoverage T)
      (σ : W.I₀ → U.I₀) (τ : W.I₀ → V.I₀)
      (r : ∀ k : W.I₀, W.X k ⟶ U.X (σ k))
      (s : ∀ k : W.I₀, W.X k ⟶ V.X (τ k)),
      (∀ k : W.I₀, r k ≫ U.f (σ k) = W.f k) ∧
      (∀ k : W.I₀, s k ≫ V.f (τ k) = W.f k) ∧
      ∀ k : W.I₀,
        Nonempty ((upperStar (ModuleCat.{u + 1} A) (W.f k)).obj L ≅
          (constantSheaf (W.X k).smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A)) ∧
        ∃ (D : CochainComplex (ModuleCat.{u + 1} A) ℤ)
          (e : ∀ q : ℤ, D.X q ≅ ModuleCat.of A (Module.Dual A ((E (σ k)).X (-q)))),
          (∀ (q : ℤ) (φ : Module.Dual A ((E (σ k)).X (-q))),
            (e (q + 1)).hom (D.d q (q + 1) ((e q).inv φ)) =
              (q + 1).negOnePow • (φ.comp ((E (σ k)).d (-(q + 1)) (-q)).hom)) ∧
          Nonempty ((upperStar (ModuleCat.{u + 1} A) (W.f k)).leftDerivedFunctor.obj H ≅
            _root_.DerivedCategory.Q.obj
              ((((constantSheaf (W.X k).smallEtaleTopology
                (ModuleCat.{u + 1} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D)⟦m⟧)) ∧
          (∀ q : ℤ, ∃ (n : ℕ)
            (s : (D⟦m⟧).X q ⟶ ModuleCat.of A (Fin n → A))
            (r : ModuleCat.of A (Fin n → A) ⟶ (D⟦m⟧).X q), s ≫ r = 𝟙 _) ∧
          ∀ q : ℤ, q < -b - m ∨ -a - m < q → IsZero ((D⟦m⟧).X q)) ∧
    (∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ i).obj H)) ∧
    DerivedCategory.isBoundedConstructible A T H ∧
    DerivedCategory.hasTorAmplitudeIn A T (-b - m) (-a - m) H := by
  sorry

end AlgebraicGeometry.Etale
