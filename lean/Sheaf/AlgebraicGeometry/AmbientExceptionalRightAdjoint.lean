/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Ambient exceptional right adjoint datum

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`, order 1488
(blueprint: def-weil-ambient-exceptional-adjoint).

The canonical compact-support candidate uses the ordinary unbounded derived category of
modules over the constant coefficient sheaf. No compactification-independence theorem or
preservation theorem is used: the right adjoints and their coherent comparison maps are
data, and the predicate asks whether such data exist.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The finite-level compact-support candidate for a specified compactification: the
termwise descent of extension by zero followed by the ordinary K-injective right derived
direct image. Source: blueprint order 1488
(blueprint: def-weil-ambient-exceptional-adjoint). -/
noncomputable def sfAmbientCompactSupportCandidate
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A :=
  (sfIntrinsicExtensionByZero d.i A).mapDerivedCategory ⋙
    proEtaleConstantDerivedDirectImage d.g A

/-- The actual ambient datum. Its adjunction at the specified compactification `c` is
`adjunction c`; thus the family and the distinguished adjunction agree by definition.
`Adjunction.homEquiv` supplies precisely the natural bijections in the node, with unit
`homEquiv (𝟙 _)` and counit `homEquiv.symm (𝟙 _)`. All comparison isomorphisms are natural
isomorphisms of functors on the whole ordinary derived categories. Only the proper part
of `c` receives a FullCD bound.
Source: blueprint order 1488 (blueprint: def-weil-ambient-exceptional-adjoint). -/
structure SfAmbientExceptionalRightAdjointDatum
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : Compactification f) where
  /-- Nonnegative uniform full cohomological dimension bound for the chosen proper part. -/
  fullCD : ∃ c_cd : ℕ, sfFullCohomologicalDimension c.g A c_cd
  /-- Chosen ambient right adjoints for all compactifications. -/
  rightAdjoint : ∀ _d : Compactification f,
    proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A
  /-- Natural Hom bijections, including the one at `c`. -/
  adjunction : ∀ d : Compactification f,
    sfAmbientCompactSupportCandidate A d ⊣ rightAdjoint d
  /-- Natural comparison of compact-support candidates along a refinement. -/
  theta : ∀ {d e : Compactification f} (_v : d ⟶ e),
    sfAmbientCompactSupportCandidate A d ≅ sfAmbientCompactSupportCandidate A e
  /-- Contravariant natural comparison of right adjoints along a refinement. -/
  rho : ∀ {d e : Compactification f} (_v : d ⟶ e), rightAdjoint e ≅ rightAdjoint d
  /-- Refinement comparisons identify the units. -/
  unit_compatibility : ∀ {d e : Compactification f} (v : d ⟶ e)
    (K : proEtaleDerivedCategory X A),
    (adjunction e).unit.app K ≫
        (rho v).hom.app ((sfAmbientCompactSupportCandidate A e).obj K) =
      (adjunction d).unit.app K ≫ (rightAdjoint d).map ((theta v).hom.app K)
  /-- Refinement comparisons identify the counits. -/
  counit_compatibility : ∀ {d e : Compactification f} (v : d ⟶ e)
    (L : proEtaleDerivedCategory Y A),
    (sfAmbientCompactSupportCandidate A d).map ((rho v).hom.app L) ≫
        (adjunction d).counit.app L =
      (theta v).hom.app ((rightAdjoint e).obj L) ≫ (adjunction e).counit.app L
  /-- Identity refinements have identity left comparisons. -/
  theta_id : ∀ d : Compactification f, theta (𝟙 d) = Iso.refl _
  /-- Identity refinements have identity right comparisons. -/
  rho_id : ∀ d : Compactification f, rho (𝟙 d) = Iso.refl _
  /-- Composition coherence for the left comparisons. -/
  theta_comp : ∀ {d e h : Compactification f} (v : d ⟶ e) (w : e ⟶ h),
    theta (v ≫ w) = theta v ≪≫ theta w
  /-- Composition coherence for the contravariant right comparisons. -/
  rho_comp : ∀ {d e h : Compactification f} (v : d ⟶ e) (w : e ⟶ h),
    rho (v ≫ w) = rho w ≪≫ rho v

/-- A separated finite-type morphism of finite-type `S`-schemes carries the optional
ambient exceptional right adjoint datum at the finite coefficient level `A_{E,n}` if the
specified datum exists. The chosen uniformizer and quotient ring are those of the recorded
p-adic coefficient extension. Invertibility of the prime is required in every local ring
of the scheme base. No constructibility, interval, or Tor preservation is required.
Source: blueprint order 1488 (blueprint: def-weil-ambient-exceptional-adjoint). -/
noncomputable def HasAmbientExceptionalRightAdjointDatum
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  Nonempty (SfAmbientExceptionalRightAdjointDatum (Padic.coefficientExtensionRing l E n) f c)

end AlgebraicGeometry.Scheme
