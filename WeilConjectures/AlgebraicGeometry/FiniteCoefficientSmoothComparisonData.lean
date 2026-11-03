/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientSmoothAdjunctionData
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! The fixed-data comparison sub-step for smooth finite coefficients.

The theorem below proves invertibility and the ordered chart equation for a
specified natural transformation satisfying its counit normalization.
It is strictly below the parent theorem because it assumes all adjunction data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale
open GeneralFieldChart

abbrev finiteCoefficientSmoothComparisonProperty
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (D : FiniteCoefficientSmoothAdjunctionData ℓ pchar hp hℓ k j p φ hA hB)
    (c : D.GA ⋙ chartCtfScalar φ X D.hSX ⟶ chartCtfScalar φ Y D.hSY ⋙ D.GB) : Prop :=
  (∀ K : chartCtfCategory Y A,
    (chartCompact B j p).map (c.app K).hom ≫
        (D.adjB.counit.app ((chartCtfScalar φ Y D.hSY).obj K)).hom =
      @inv _ _ _ _ ((chartCompactScalarComparison φ j p).app (D.GA.obj K).obj)
        (D.hb K) ≫
        (chartScalar φ Y).map (D.adjA.counit.app K).hom) ∧
  (∀ K : chartCtfCategory Y A, IsIso (c.app K)) ∧
  (∀ (n : ℕ) (hn : 0 < ℓ ^ n) (hnA : ((ℓ ^ n : ℕ) : A) = 0)
      (hnB : ((ℓ ^ n : ℕ) : B) = 0)
      (MA : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} A))
      (MB : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} B))
      (tA : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} A)
        (ℓ ^ n) (congrArg ULift.up hnA))
      (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ℓ ^ n : ℕ) : Γ(T, ⊤))),
        Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} A) (ℓ ^ n)
          (congrArg ULift.up hnA) tA T hT)
      (tB : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} B)
        (ℓ ^ n) (congrArg ULift.up hnB))
      (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ℓ ^ n : ℕ) : Γ(T, ⊤))),
        Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} B) (ℓ ^ n)
          (congrArg ULift.up hnB) tB T hT)
      (hY : IsUnit ((ℓ ^ n : ℕ) : Γ(Y, ⊤)))
      (U : Scheme.{u}) [IsNoetherian U]
      (jU : U ⟶ X) [IsOpenImmersion jU]
      (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e]
      [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (he : jU ≫ f = e ≫ affineTraceProjection Y d)
      (K : chartCtfCategory Y A),
    FiniteCoefficientChartEquation k φ j p D.hFA D.hFB D.hSX D.hSY D.GA D.GB D.adjA D.adjB
      D.RA D.RB MA MB c jU d e ((congrArg (fun q ↦ jU ≫ q) hf).trans he)
      (ℓ ^ n) hn hnA hnB tA DA tB DB hY K)

/-- The counit-normalized mate has invertible components and the ordered chart equation.

Source: Locality, Charts, and the counit-transpose step of the current
`sk-lem-sp-reduction-exceptional` proof. The two independent hard parts are
kept separate from chart-adjunction existence and are not a restatement of the
parent, since all adjunction data is an explicit input here.
(blueprint: lem-pur-finite-coefficient-comparison-smooth).
Proof: retain the supplied counit equation. On a smooth etale coordinate chart, paste the
P1 scalar trace equation in coordinate order with etale summation and the open
restriction comparison. The canonical realization counit equations identify
this paste with the specified chart reassociation map. That map is invertible.
A finite smooth coordinate cover, together with conservativity of open
restriction, therefore proves component invertibility, including empty X.
-/
theorem finiteCoefficientSmoothComparison_of_counit
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (D : FiniteCoefficientSmoothAdjunctionData ℓ pchar hp hℓ k j p φ hA hB) :
    ∀ (c : D.GA ⋙ chartCtfScalar φ X D.hSX ⟶ chartCtfScalar φ Y D.hSY ⋙ D.GB),
      (∀ K : chartCtfCategory Y A,
        (chartCompact B j p).map (c.app K).hom ≫
            (D.adjB.counit.app ((chartCtfScalar φ Y D.hSY).obj K)).hom =
          @inv _ _ _ _ ((chartCompactScalarComparison φ j p).app (D.GA.obj K).obj)
              (D.hb K) ≫
            (chartScalar φ Y).map (D.adjA.counit.app K).hom) →
      finiteCoefficientSmoothComparisonProperty ℓ pchar hp hℓ k f d j p hf hA hB φ D c :=
  by sorry

end AlgebraicGeometry.ProEtale
