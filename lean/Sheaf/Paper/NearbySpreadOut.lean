module

public import Sheaf.Paper.OrgogozoInductionData
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.IntegersExcellent
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullback
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.TraceFormula.BoundedConstructibleDerivedHomContinuity

/-! # Spread out finite-type nearby-cycle input to an arithmetic base

Source: literature/orgogozo-modifications-cycles-proches.pdf, §2.1, p. 3
(blueprint: lem-trf-nearby-spread-out).
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Q11 stage-2 delivery restates the existing landed statement.

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Orgogozo
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.Orgogozo

/-- Arithmetic spreading out for finite-type nearby-cycle data.

Source: Orgogozo, Modifications et cycles proches sur une base générale, §2.1, p. 3
(blueprint: lem-trf-nearby-spread-out).

Proof plan, following the node's nine steps. (1) Present the affine integral base as a
filtered limit of finite-type integer rings, choose an integral finite-type
`ℤ[1/m]` stage, and use injectivity to obtain a dominant map. (2) Use Noetherian
finite-type descent and the finite-presentation limit theorem to descend `f`; the
identification `X ≅ X₀ ×_{S₀} S` is one over `S`, compatible with `f` and the second
projection.
(3) Descend the finitely many constructible cohomology sheaves at one common stage;
pullback preserves their finite locally constant module stratifications. (4) Exact
inverse image is triangulated and commutes with cohomology and truncations; apply the
bounded derived-Hom continuity statement to each connecting arrow in the finite
Postnikov tower. (5) Form the corresponding cones and use the long exact sequence and
TR3 to descend the whole bounded complex. (6) The integer ring is excellent and
finite-type algebras and localizations preserve excellence, so the arithmetic model
is excellent and Noetherian. (7) A polynomial presentation bounds its Krull dimension
by a natural number. (8) For a modification of the model, pull back its dense
isomorphism open, take the reduced closure in the fibre product, and verify properness,
density and the map to the model modification. (9) The universal quantifiers in
`UniversalTruncatedComparison` identify the two fibre-product families, so vanishing
through every degree `r` transfers to the strict transform.
-/
theorem nearby_spread_out
    {X S : Scheme.{u}} [IsIntegral S] [IsNoetherian S] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (m : ℕ) (hmΛ : ∀ x : Λ, m • x = 0)
    (hmS : IsUnit (m : Γ(S, ⊤)))
    (K : EtaleDerived X Λ)
    (hKb : IsBounded (etaleDatum.{u, u + 1} X) (Coeff.{u, u + 1} Λ) K)
    (hKc : ∀ q : ℤ,
      ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)),
        Scheme.IsConstructibleEtaleModuleSheaf F ∧
        Nonempty ((PresheafOfModules.forgetToPresheafModuleCat
            (op (⊤_ (EtaleSite.{u, u + 1} X))) terminalIsTerminal.op).obj
          ((PresheafOfModules.restrictScalars
            (Functor.whiskerRight
              (toSheafify (etaleTopology.{u, u + 1} X)
                ((Functor.const (EtaleSite.{u, u + 1} X)ᵒᵖ).obj
                  (CommRingCat.of (Coeff Λ))))
              (forget₂ CommRingCat RingCat))).obj
            ((DerivedCategory.homologyFunctor
              ((etaleDatum.{u, u + 1} X).modules (Coeff Λ)) q).obj K).val) ≅
            (AsSmall.down : EtaleSite.{u, u + 1} X ⥤ X.Etale).op ⋙ F.obj)) :
    ∃ (S₀ : Scheme.{u}) (a : S ⟶ S₀) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀)
      (K₀ : EtaleDerived X₀ Λ)
      (hK₀b : IsBounded (etaleDatum.{u, u + 1} X₀) (Coeff.{u, u + 1} Λ) K₀),
      IsIntegral S₀ ∧ IsAffine S₀ ∧ IsNoetherian S₀ ∧
      Algebra.FiniteType ℤ Γ(S₀, ⊤) ∧ IsUnit (m : Γ(S₀, ⊤)) ∧
      IsExcellentScheme S₀ ∧
      (∃ n : ℕ, topologicalKrullDim S₀ ≤ (n : WithBot ℕ∞)) ∧
      IsDominant a ∧
      (LocallyOfFiniteType f₀ ∧ QuasiCompact f₀) ∧
      (∀ q : ℤ,
        ∃ F : Sheaf X₀.smallEtaleTopology
            (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)),
          Scheme.IsConstructibleEtaleModuleSheaf F ∧
          Nonempty ((PresheafOfModules.forgetToPresheafModuleCat
              (op (⊤_ (EtaleSite.{u, u + 1} X₀))) terminalIsTerminal.op).obj
            ((PresheafOfModules.restrictScalars
              (Functor.whiskerRight
                (toSheafify (etaleTopology.{u, u + 1} X₀)
                  ((Functor.const (EtaleSite.{u, u + 1} X₀)ᵒᵖ).obj
                    (CommRingCat.of (Coeff Λ))))
                (forget₂ CommRingCat RingCat))).obj
              ((DerivedCategory.homologyFunctor
                ((etaleDatum.{u, u + 1} X₀).modules (Coeff Λ)) q).obj K₀).val) ≅
              (AsSmall.down : EtaleSite.{u, u + 1} X₀ ⥤ X₀.Etale).op ⋙ F.obj)) ∧
      (∃ eX : X ≅ pullback f₀ a, eX.hom ≫ pullback.snd f₀ a = f ∧
        Nonempty (K ≅
          ((etaleModules eX.hom).pull (Coeff Λ)).obj
            (((etaleModules (pullback.fst f₀ a)).pull (Coeff Λ)).obj K₀))) ∧
      (∀ (S₀' : Scheme.{u}) (q₀ : S₀' ⟶ S₀),
        (IsProper q₀ ∧ ∃ U₀ : S₀.Opens,
          Dense (U₀ : Set S₀) ∧ IsIso (pullback.snd q₀ U₀.ι) ∧
            Dense (q₀ ⁻¹' (U₀ : Set S₀))) →
        ∃ (S' : Scheme.{u}) (i : S' ⟶ pullback a q₀)
          (q : S' ⟶ S) (t : S' ⟶ S₀'),
          IsReduced S' ∧ IsClosedImmersion i ∧
          q = i ≫ pullback.fst a q₀ ∧ t = i ≫ pullback.snd a q₀ ∧
          IsModification q ∧
          (∀ r : ℤ,
            UniversalTruncatedComparison (pullback.snd f₀ q₀) Λ
              ⟨((etaleModules (pullback.fst f₀ q₀)).pull (Coeff Λ)).obj K₀,
                ((etaleModules (pullback.fst f₀ q₀)).modulePull
                  (Coeff Λ)).bounded_mapDerivedCategory_obj hK₀b⟩ r →
            UniversalTruncatedComparison (pullback.snd f q) Λ
              ⟨((etaleModules (pullback.fst f q)).pull (Coeff Λ)).obj K,
                ((etaleModules (pullback.fst f q)).modulePull
                  (Coeff Λ)).bounded_mapDerivedCategory_obj hKb⟩ r)) := by
  sorry

end AlgebraicGeometry.Orgogozo

end
