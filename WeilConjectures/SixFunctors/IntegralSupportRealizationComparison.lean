/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralExceptionalMappingSystem

/-! # Compact-support realization for an arbitrary finite-operation realization

Source: the accepted integral exceptional mapping-adjunction interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralExceptionalMapping
open FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

variable {l E D hl}
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {c : Compactification f}
  {SX : CoefficientDerivedSystemCalculus l E X}
  {SZ : CoefficientDerivedSystemCalculus l E c.Z}
  {SY : CoefficientDerivedSystemCalculus l E Y}
  (r : Realization l E D hl f c SX SZ SY)


/-- The literal support-system limit realizes the recorded integral support functor.
Source: prop-coef-integral-exceptional-adjoint, proof paragraph 2, and the accepted
specified-adjunction interface
(blueprint: lem-coef-integral-support-realization-comparison).

Proof: obtain a geometric realization r0 and its recorded IntegralSupport from
the existing finiteAdjunctionDiagramRealization theorem. Its reduction and the
arbitrary reduction are left adjoints to the same total-limit functor, so they
are naturally isomorphic. Both open extensions are left adjoints to the same
actual geometric system pullback, and both proper images are right adjoints to
that pullback for the proper map. Uniqueness of adjoints gives whole-system
natural isomorphisms for both factors. Compose these with the actual supportIso
of each realization and apply total limit. Finally compose the resulting
comparison F_r isomorphic to F_r0 with r0's IntegralSupport.iso. No comparison
is inferred from finite evaluations. All isomorphisms exist before restricting
to individual inputs, so zero objects, identity maps, and empty opens are included. -/
theorem support_realization_comparison :
    Nonempty (F r ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E ⋙
        (sfIntegralConstructible l E Y).ι) := by
  classical
  obtain ⟨SX₀, SZ₀, SY₀, SS₀, _, _, _, _, βX₀, βY₀, r₀, g₀, s₀, aX₀, aY₀,
    _, _, _, _, ⟨i₀⟩⟩ := finiteAdjunctionDiagramRealization l E D hl f c
  let er : SX.reduction ≅ SX₀.reduction :=
    SX.adjunction.leftAdjointUniq SX₀.adjunction
  let eo : r.support.extension.mapDerivedCategory ≅ r₀.support.extension.mapDerivedCategory :=
    r.support.openAdj.leftAdjointUniq r₀.support.openAdj
  let ep : r.support.properGeometry.image.direct ≅ r₀.support.properGeometry.image.direct :=
    (r.support.properGeometry.adjunction l E).rightAdjointUniq
      (r₀.support.properGeometry.adjunction l E)
  let es : r.support.functor ≅ r₀.support.functor :=
    Functor.isoWhiskerRight eo r.support.properGeometry.image.direct ≪≫
      Functor.isoWhiskerLeft r₀.support.extension.mapDerivedCategory ep
  let e (r' : Realization l E D hl f c SX SZ SY) :
      F r' ≅ (sfIntegralConstructible l E X).ι ⋙ SX.reduction ⋙
        r'.support.functor ⋙ coefficientSequenceLimit l E Y :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (R l E D hl X SX) r'.supportIso)
      (coefficientSequenceLimit l E Y)
  let e₀ : F r₀ ≅ (sfIntegralConstructible l E X).ι ⋙ SX₀.reduction ⋙
      r₀.support.functor ⋙ coefficientSequenceLimit l E Y :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (R l E D hl X SX₀) r₀.supportIso)
      (coefficientSequenceLimit l E Y)
  exact ⟨e r ≪≫
    Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι
      (Functor.isoWhiskerRight er (r.support.functor ⋙ coefficientSequenceLimit l E Y)) ≪≫
    Functor.isoWhiskerLeft ((sfIntegralConstructible l E X).ι ⋙ SX₀.reduction)
      (Functor.isoWhiskerRight es (coefficientSequenceLimit l E Y)) ≪≫
    e₀.symm ≪≫ i₀.iso⟩

end WeilConjectures.IntegralExceptionalMapping
