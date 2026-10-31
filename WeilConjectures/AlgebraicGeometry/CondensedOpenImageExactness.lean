/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero

/-! Exactness of the condensed open-image connecting sequence.

Source: latest blueprint, p-dl-a1-exact, Step 3
(blueprint: new-dl-a1-rest).

Proof: the short exact sequence is already one of ambient modules. The lower star `R` is
additive and left exact; apply `RR` to the distinguished triangle of the short exact
sequence, take the homology long exact sequence `H⁰ → H⁰ → H⁰ → H¹`, and identify the
first three terms with `R X₁ → R X₂ → R X₃` by the canonical isomorphisms
`H⁰(RR(X[0])) ≅ R X` (`singleRightDerivedH0Iso`, natural in `X`). Monicity holds since
`R` preserves finite limits. The argument is generic in the left exact functor
(`exact_of_singleTriangle`); the constructibility hypotheses are not used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Generic form of the initial exact segment, for any left exact functor: for a short exact
sequence `0 → X₁ → X₂ → X₃ → 0`, the sequence `0 → F X₁ → F X₂ → F X₃ → H¹(RF(X₁[0]))`
is exact.
Source: Stacks Project, Tags 05TD and 0156 (blueprint: new-dl-a1-rest).
Proof: the derived functor sends the triangle of the short exact sequence to a
distinguished triangle; its homology long exact sequence gives the exactness of
`H⁰ → H⁰ → H⁰ → H¹`, and the canonical isomorphisms `H⁰(RF(X[0])) ≅ F X` identify the
first three terms with `F X₁ → F X₂ → F X₃`. Monicity holds since `F` preserves finite
limits. -/
private theorem exact_of_singleTriangle
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [Abelian.HasKInjectiveResolutions C]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    (S : ShortComplex C) (hS : S.ShortExact) :
    Mono (R.map S.f) ∧
      (ComposableArrows.mk₃ (R.map S.f) (R.map S.g)
        ((R.singleRightDerivedH0Iso S.X₃).inv ≫
          DerivedCategory.HomologySequence.δ
            (R.rightDerivedFunctor.mapTriangle.obj hS.singleTriangle) 0 1 rfl)).Exact := by
  let e (X : C) := R.singleRightDerivedH0Iso X
  let T := R.rightDerivedFunctor.mapTriangle.obj hS.singleTriangle
  have hT : T ∈ distTriang _ :=
    R.rightDerivedFunctor.map_distinguished _ hS.singleTriangle_distinguished
  let a := (DerivedCategory.homologyFunctor D 0).map T.mor₁
  let b := (DerivedCategory.homologyFunctor D 0).map T.mor₂
  let c := DerivedCategory.HomologySequence.δ T 0 1 rfl
  have hABC : (ComposableArrows.mk₃ a b c).Exact :=
    ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₂ T hT 0).exact_toComposableArrows
      (DerivedCategory.HomologySequence.exact₃ T hT 0 1 rfl).exact_toComposableArrows
  have nat {X Y : C} (f : X ⟶ Y) : R.map f ≫ (e Y).inv = (e X).inv ≫
      (DerivedCategory.homologyFunctor D 0).map
        (R.rightDerivedFunctor.map ((DerivedCategory.singleFunctor C 0).map f)) := by
    simpa only [e, Functor.singleRightDerivedH0Iso_def,
      Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso,
      NatIso.ofComponents_inv_app, Functor.comp_map] using
      R.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso.inv.naturality f
  have he : ComposableArrows.mk₃ (R.map S.f) (R.map S.g) ((e S.X₃).inv ≫ c) ≅
      ComposableArrows.mk₃ a b c :=
    ComposableArrows.isoMk₃ (e S.X₁).symm (e S.X₂).symm (e S.X₃).symm
      (Iso.refl _) (nat S.f) (nat S.g) (by dsimp; exact Category.comp_id _)
  have : Mono S.f := hS.mono_f
  exact ⟨inferInstance, ComposableArrows.exact_of_iso he.symm hABC⟩

/-- `exact_of_singleTriangle` for the lower star of any morphism of schemes, stated with
`dlOpenImageDelta`. -/
private theorem lowerStar_exact_of_singleTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} (j : U ⟶ C)
    (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) (hS : S.ShortExact) :
    Mono ((lowerStar Λ j).map S.f) ∧
      (ComposableArrows.mk₃ ((lowerStar Λ j).map S.f) ((lowerStar Λ j).map S.g)
        (dlOpenImageDelta Λ j S hS)).Exact :=
  exact_of_singleTriangle (lowerStar Λ j) S hS

/-- The monicity and initial exactness assertion for every constructible short exact
sequence on the geometric open. -/
theorem condensedOpenImage_exactness
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_iota : PadicAlgCl ell →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left] :
    ∀ (S : ShortComplex
      (Mod (Sheaf (Scheme.ProEt.topology
        ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap D.k₀ D.k)))).obj U₀).left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap D.k₀ D.k)))).obj U₀).left)))
      (hS : S.ShortExact),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left S.X₁ →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left S.X₂ →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left S.X₃ →
      Mono ((lowerStar (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀)).map S.f) ∧
      (ComposableArrows.mk₃
        ((lowerStar (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀)).map S.f)
        ((lowerStar (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀)).map S.g)
        (dlOpenImageDelta (Profinite.padicAlgClRingObj ell)
          (dlGeometricOpen D j₀) S hS)).Exact := by
  intro S hS _h₁ _h₂ _h₃
  exact lowerStar_exact_of_singleTriangle _ (dlGeometricOpen D j₀) S hS

end AlgebraicGeometry.ProEtale.CondensedRing
