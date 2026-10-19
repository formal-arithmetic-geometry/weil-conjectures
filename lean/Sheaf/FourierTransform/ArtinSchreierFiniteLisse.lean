/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.FourierTransform.ArtinSchreier
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

import Sheaf.AlgebraicGeometry.ArtinSchreierPolynomialCover
import WeilConjectures.SixFunctors.Finite.BaseChange
import Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.BaseChange.Square
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.RingTheory.LocalRing.ArtinSchreierKernel
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Artin–Schreier character sheaves over finite rings

Source: Stacks Project, Tag 0A3J, section-artin-schreier
(blueprint: lem-fd-artin-schreier-finite-lisse).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry.Etale

/-- The canonical ring map from `ZMod p` to a commutative ring in which `p` is
zero, including the zero-ring case. Source: Stacks Tag 0A3J
(blueprint: lem-fd-artin-schreier-finite-lisse). -/
noncomputable def zmodRingHomOfNatCastEqZero {p : ℕ} {R : Type u} [CommRing R]
    (h : (p : R) = 0) : ZMod p →+* R :=
  { toFun := ZMod.lift p ⟨Int.castAddHom R, by simpa using h⟩
    map_zero' := by simp
    map_one' := by
      change ZMod.lift p _ (1 : ZMod p) = 1
      rw [show (1 : ZMod p) = (1 : ℤ) by simp, ZMod.lift_coe]
      exact (Int.castRingHom R).map_one
    map_add' := by
      intro a b
      exact (ZMod.lift p _).map_add a b
    map_mul' := by
      intro a b
      obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
      obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b
      have hab : ((a * b : ℤ) : ZMod p) = (a : ZMod p) * (b : ZMod p) := by
        exact (Int.castRingHom (ZMod p)).map_mul a b
      rw [← hab, ZMod.lift_coe, ZMod.lift_coe, ZMod.lift_coe]
      exact (Int.castRingHom R).map_mul a b }

/-- The canonical `F_p`-structure on a scheme whose global ring has `p = 0`
Source: Stacks Tag 0A3J (blueprint: lem-fd-artin-schreier-finite-lisse). -/
@[instance_reducible]
noncomputable def overSpecZModOfNatCastEqZero {p : ℕ} {X : Scheme.{u}}
    (h : (p : Γ(X, ⊤)) = 0) :
    X.Over (Spec (.of (ULift.{u} (ZMod p)))) :=
  ⟨X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((zmodRingHomOfNatCastEqZero h).comp ULift.ringEquiv.toRingHom))⟩

/-- The finite-ring Artin–Schreier sheaf attached to `b` on a characteristic-
`p` scheme. Source: Stacks Tag 0A3J (blueprint: lem-fd-artin-schreier-finite-lisse). -/
noncomputable def artinSchreierSheafOfNatCastEqZero {p : ℕ} [Fact p.Prime]
    {Λ : Type (u + 1)} [CommRing Λ] [Invertible (p : Λ)] {X : Scheme.{u}}
    (h : (p : Γ(X, ⊤)) = 0) (Ψ : AddChar (ZMod p) Λ) (b : Γ(X, ⊤)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  letI := overSpecZModOfNatCastEqZero h
  artinSchreierSheafOf X (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b

/-- The relative Artin–Schreier covering `T^p - T = b`, as the pullback of
`AS_p` along the map defined by `b`. Source: Stacks Tag 0A3J
(blueprint: lem-fd-artin-schreier-finite-lisse). -/
noncomputable def artinSchreierCoverOfNatCastEqZero {p : ℕ} [Fact p.Prime]
    {X : Scheme.{u}} (h : (p : Γ(X, ⊤)) = 0)
    (b : Γ(X, ⊤)) : Scheme.{u} :=
  letI := overSpecZModOfNatCastEqZero h
  pullback (artinSchreierMap PUnit (Spec (.of (ULift.{u} (ZMod p)))) p)
    (AffineSpace.homOfVector (X ↘ Spec (.of (ULift.{u} (ZMod p)))) fun _ ↦ b)

/-- Projection from the relative Artin–Schreier covering to `X`
Source: Stacks Tag 0A3J (blueprint: lem-fd-artin-schreier-finite-lisse). -/
noncomputable def artinSchreierCoverMapOfNatCastEqZero {p : ℕ} [Fact p.Prime]
    {X : Scheme.{u}} (h : (p : Γ(X, ⊤)) = 0)
    (b : Γ(X, ⊤)) : artinSchreierCoverOfNatCastEqZero h b ⟶ X :=
  letI := overSpecZModOfNatCastEqZero h
  pullback.snd (artinSchreierMap PUnit (Spec (.of (ULift.{u} (ZMod p)))) p)
    (AffineSpace.homOfVector (X ↘ Spec (.of (ULift.{u} (ZMod p)))) fun _ ↦ b)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.Etale

/-- Artin–Schreier character sheaves over arbitrary finite commutative rings
are lisse lines, constructible, and flat. Source: Stacks Project Tag 0A3J
(blueprint: lem-fd-artin-schreier-finite-lisse).

Proof plan, following the ten DAG steps (all postponed here):
1. On an affine open, the cover has algebra `A[T]/(T^p-T-b)`, generated by the first
   `p` powers of `T`. The derivative is `-1`, so the standard étale criterion proves
   finiteness and étaleness (`def-weil-finite-integral-morphism`,
   `lem-weil-pbc-standard-etale-monic-derivative`, `def-weil-etale-morphism`).
2. Local solvability (`lem-sc-artin-schreier-polynomial-cover`) supplies an étale
   surjection factoring through this cover, proving its surjectivity even for empty `X`.
3. The universal root identifies this cover with the pullback of `AS_p` along `b`:
   a map into either object is exactly a base map together with a root. Translations
   commute with the projection to the universal cover (`def-pc-fibre-product`).
4. Finite exchange (`lemma-weil-pbc-finite-exchange`), its module linearity
   (`lem-weil-pbc-underived-exchange-module-linear`), and constant coefficient pullback
   (`prop-weil-pbc-inverse-image-modules-exact`) identify the pulled-back universal
   pushforward with `q_* Λ_Y` as module sheaves.
5. The section formula for exchange (`def-weil-pbc-underived-exchange` and
   `lem-weil-pbc-constant-sheaf-sections-locally-constant`) commutes with translations.
   Exact inverse image therefore identifies the pullback-defined sheaf with the image
   of `p⁻¹ ∑ a, Ψ(-a) σ_a` on `q_* Λ_Y`.
6. On `Y ×_X Y`, the difference of the roots lies locally in `F_p`
   (`lem-sc-local-ring-artin-schreier-kernel`). The root translations give mutually
   inverse maps identifying this fibre product with the disjoint union of `p` copies of `Y`.
7. Étale inverse image is restriction (`lem-weil-pbc-etale-inverse-image-restriction`).
   The pushforward section formula (`def-weil-pbc-direct-image`) and constant sheaf
   section formula identify `q⁻¹q_* Λ_Y` with tuples `(f_a)` indexed by `F_p`, with
   translation by `c` sending this tuple to `(f_(a+c))`.
8. Exact inverse image preserves the image. Put `c(f) = p⁻¹ ∑ d, Ψ(-d) f_d`.
   Reindexing gives `(e f)_r = Ψ(r)c(f)`. For `g_r = Ψ(r)` one has `c(g)=1`.
   Thus the image is the free line generated by `g`, with inverse evaluation at zero.
   This proves the displayed trivialization, also for the trivial character or zero ring.
9. The singleton étale surjection `q` trivializes this line, proving local constancy
   (`def-constructible-locally-constant`). Its constant value `Λ` is finite. The one-stratum
   partition (empty partition for empty `X`) proves constructibility in the recorded
   `def-weil-pbc-etale-constructible-sheaf` sense, without a finite-type hypothesis.
10. Restriction to the slice site is exact and commutes with tensor
    (`lem-weil-pbc-etale-site-localization-open`,
    `lem-sfb-localized-site-tensor-restriction`). On this cover tensoring with the line is
    tensoring with the unit, hence exact. The kernel, cokernel, and middle homology defects
    vanish locally. Base change of the cover (`lem-weil-pbc-etale-covering-base-change`)
    and the separatedness axiom make these defects zero globally. This is exactness of
    `tensorRight L`, the defining condition of `def-pc-flat-sheaf-modules` (Tag 03ER). -/
theorem isFlat_isConstructible_isLisse_artinSchreierSheafOfNatCastEqZero
    {p : ℕ} [Fact p.Prime] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    [Invertible (p : Λ)] {X : Scheme.{u}}
    (h : (p : Γ(X, ⊤)) = 0) (b : Γ(X, ⊤)) (Ψ : AddChar (ZMod p) Λ) :
    IsFinite (AlgebraicGeometry.Etale.artinSchreierCoverMapOfNatCastEqZero h b) ∧
      Etale (AlgebraicGeometry.Etale.artinSchreierCoverMapOfNatCastEqZero h b) ∧
      Surjective (AlgebraicGeometry.Etale.artinSchreierCoverMapOfNatCastEqZero h b) ∧
      Nonempty ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} Λ)
        (AlgebraicGeometry.Etale.artinSchreierCoverMapOfNatCastEqZero h b)).obj
        (AlgebraicGeometry.Etale.artinSchreierSheafOfNatCastEqZero h Ψ b) ≅
        𝟙_ _) ∧
      IsLocallyConstantSheaf
        (AlgebraicGeometry.Etale.artinSchreierSheafOfNatCastEqZero h Ψ b) ∧
      IsConstructibleEtaleModuleSheaf
        (AlgebraicGeometry.Etale.artinSchreierSheafOfNatCastEqZero h Ψ b) ∧
      CategoryTheory.exactFunctor _ _ (tensorRight
        (AlgebraicGeometry.Etale.artinSchreierSheafOfNatCastEqZero h Ψ b)) := by
  sorry

end AlgebraicGeometry.Scheme

