module

public import Sheaf.Paper.OrientedNearbyCycles
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.CategoryTheory.BoundedHeartAmplitude
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.TraceFormula.GabberNearbyCycleDimensionBound
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Uniform cohomological bound for oriented nearby cycles

Source: Orgogozo, `Modifications et cycles proches sur une base générale`,
Proposition 2.3, pp. 3--4 and §2.2 (blueprint: lem-trf-nearby-dimension-bound).

The theorem records the vanishing bound for torsion coefficients, its arbitrary
scheme-base-change form, and the resulting bounded-complex amplitude statement.
The three abbreviations state the standard derived-category degree conditions and the
degree-zero embedding for an arbitrary small site in its own universe `s`, so that the
theorem is stated for a coefficient ring in an arbitrary universe `v`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v s

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- Cohomology of `L` vanishes in degrees `> n`: Mathlib's `DerivedCategory.IsLE` on the
derived category of constant-coefficient module sheaves of a site.
Source: Orgogozo, Proposition 2.3 and §2.2 (blueprint: lem-trf-nearby-dimension-bound). -/
abbrev DerivedIsLE (S : CategoryTheory.AdicSites.Site.{s}) (A : Type s) [CommRing A]
    (L : S.derived A) (n : ℤ) : Prop :=
  L.IsLE n

/-- Cohomology of `L` vanishes in degrees `< n`: Mathlib's `DerivedCategory.IsGE` on the
derived category of constant-coefficient module sheaves of a site.
Source: Orgogozo, Proposition 2.3 and §2.2 (blueprint: lem-trf-nearby-dimension-bound). -/
abbrev DerivedIsGE (S : CategoryTheory.AdicSites.Site.{s}) (A : Type s) [CommRing A]
    (L : S.derived A) (n : ℤ) : Prop :=
  L.IsGE n

/-- A module sheaf `F` as the complex `F[0]`: Mathlib's `DerivedCategory.singleFunctor`
in degree `0`.
Source: Orgogozo, Proposition 2.3 (blueprint: lem-trf-nearby-dimension-bound). -/
abbrev derivedSingle (S : CategoryTheory.AdicSites.Site.{s}) (A : Type s) [CommRing A] :
    S.modules A ⥤ S.derived A :=
  DerivedCategory.singleFunctor (S.modules A) 0

/-- Uniform cohomological dimension bound for oriented nearby cycles.

Source: Orgogozo, `Modifications et cycles proches sur une base générale`,
Proposition 2.3, pp. 3--4 and §2.2 (blueprint: lem-trf-nearby-dimension-bound).

Proof.
1. Fix `g : T ⟶ S` and `f_T : X_T ⟶ T`. `f_T` is of finite type
   (lem-sfb-finite-type-composition-base-change (2)). For `t ∈ T` over `s ∈ S`, the
   fibre `(X_T)_t` is `X_s ⊗_{κ(s)} κ(t)` (lem-sc-fibre-dimension-after-base-change);
   two applications of lem-kun-dimension-extension give
   `dim (X_T)_t = dim X_s = dim X_{s̄} ≤ d` (empty fibres have dimension `⊥`).
2. As `m Λ = 0`, `Λ` is a `ℤ/m`-algebra; lem-trf-gabber-nearby-cycle-dimension-bound
   with `N = d` gives `H^i(RΨ_{f_T}(F[0])) = 0` for `i > 2d`; `T = S` is the first clause.
3. `RΨ_{f_T}` is the K-injective right derived functor of a left exact right adjoint
   (lem-weil-pbc-ringed-topoi-module-adjunction, prop-pur-kinjective-resolutions-exist),
   hence triangulated (lem-pc-right-derived-functor-triangulated), and
   lem-weil-pbc-derived-functor-negative-vanishing gives vanishing in degrees `< 0`.
4. lem-pur-bounded-heart-amplitude with `[c, d'] = [0, 2d]` gives the interval
   `[a, b + 2d]` for `K` with cohomology in `[a, b]`; if `a > b`, `K ≅ 0`. Since `g`
   was arbitrary, all bounds hold after every base change with the same `d, a, b`.
-/
theorem nearbyCycles_uniformCohomologicalBound
    {S X : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ)
    (hgeom : ∀ (y : S) (K : Type u) [Field K]
      [Algebra (S.residueField y) K] [IsAlgClosed K],
      (topologicalKrullDim
          ((pullback f
            ((Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField y) K)) :
              Spec (CommRingCat.of K) ⟶
                Spec (CommRingCat.of (S.residueField y))) ≫
              S.fromSpecResidueField y)) : Scheme)) ≤ (d : WithBot ℕ∞))
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) (hmS : IsUnit (m : Γ(S, ⊤)))
    (a b : ℤ) :
    (∀ (F : (etaleDatum.{u, v} X).modules (Coeff.{u, v} Λ)),
      DerivedIsLE (vanishingDatum.{u, v} f) (Coeff.{u, v} Λ)
        ((nearbyCycles.{u, v} f Λ).obj
          ((derivedSingle (etaleDatum.{u, v} X) (Coeff.{u, v} Λ)).obj F))
        (2 * d : ℤ)) ∧
    (∀ {T : Scheme.{u}} (g : T ⟶ S)
      (F : (etaleDatum.{u, v} (pullback f g)).modules (Coeff.{u, v} Λ)),
      DerivedIsLE (vanishingDatum.{u, v} (pullback.snd f g)) (Coeff.{u, v} Λ)
        ((nearbyCycles.{u, v} (pullback.snd f g) Λ).obj
          ((derivedSingle (etaleDatum.{u, v} (pullback f g)) (Coeff.{u, v} Λ)).obj F))
        (2 * d : ℤ)) ∧
    (∀ (K : EtaleDerived.{u, v} X Λ),
      DerivedIsGE (etaleDatum.{u, v} X) (Coeff.{u, v} Λ) K a →
      DerivedIsLE (etaleDatum.{u, v} X) (Coeff.{u, v} Λ) K b →
      DerivedIsGE (vanishingDatum.{u, v} f) (Coeff.{u, v} Λ)
          ((nearbyCycles.{u, v} f Λ).obj K) a ∧
        DerivedIsLE (vanishingDatum.{u, v} f) (Coeff.{u, v} Λ)
          ((nearbyCycles.{u, v} f Λ).obj K) (b + 2 * d)) ∧
    (∀ {T : Scheme.{u}} (g : T ⟶ S)
      (K : EtaleDerived.{u, v} (pullback f g) Λ),
      DerivedIsGE (etaleDatum.{u, v} (pullback f g)) (Coeff.{u, v} Λ) K a →
      DerivedIsLE (etaleDatum.{u, v} (pullback f g)) (Coeff.{u, v} Λ) K b →
      DerivedIsGE (vanishingDatum.{u, v} (pullback.snd f g)) (Coeff.{u, v} Λ)
          ((nearbyCycles.{u, v} (pullback.snd f g) Λ).obj K) a ∧
        DerivedIsLE (vanishingDatum.{u, v} (pullback.snd f g)) (Coeff.{u, v} Λ)
          ((nearbyCycles.{u, v} (pullback.snd f g) Λ).obj K) (b + 2 * d)) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
