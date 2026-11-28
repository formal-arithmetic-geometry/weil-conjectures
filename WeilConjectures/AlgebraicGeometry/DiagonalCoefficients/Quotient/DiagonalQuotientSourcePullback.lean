/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFamilyPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarClosedSourceExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback

/-! # Ordinary quotient endpoints under geometric pullback
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The module adjoint transpose of a pulled-back module map has, as underlying map, the
abelian adjoint transpose of the map read through the forgetful pullback comparison. -/
theorem homEquiv_upperStar_hom
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : Modules R S) (N : Modules R X)
    (φ : (CondensedRing.upperStar R f).obj M ⟶ N) :
    (((CondensedRing.upperStarLowerStarAdjunction R f).homEquiv M N) φ).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv M.X N.X
        ((profinitePointModuleForgetPullbackIso R f).inv.app M ≫ φ.hom) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Mod.comp_hom']
  erw [(Scheme.proEtaleSheafDirectImage f Ab.{u + 1}).map_comp, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ (lowerStar Ab.{u + 1} f).map φ.hom)
    (moduleUnit_forget_inv R f M).symm

/-- The map of a pull endpoint is its module isomorphism read through the forgetful
pullback comparison. -/
theorem PullEndpoint.forget_comp_iso_hom
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {X S : Scheme.{u}} {f : X ⟶ S} {M : Modules R S} {N : Modules R X}
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X} (e : PullEndpoint R f M N m) :
    (profinitePointModuleForgetPullbackIso R f).inv.app M ≫ e.iso.hom.hom = m := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).injective
  exact (homEquiv_upperStar_hom R f M N e.iso.hom).symm.trans e.normalization

/-- Every module isomorphism out of a pullback is a pull endpoint for its underlying map,
read through the forgetful pullback comparison. -/
def PullEndpoint.ofIso
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {X S : Scheme.{u}} {f : X ⟶ S} {M : Modules R S} {N : Modules R X}
    (e : (CondensedRing.upperStar R f).obj M ≅ N) :
    PullEndpoint R f M N ((profinitePointModuleForgetPullbackIso R f).inv.app M ≫ e.hom.hom)
    where
  iso := e
  normalization := homEquiv_upperStar_hom R f M N e.hom

/-- On balanced tensor generators, the scalar extension of a pulled-back module map,
read through the forgetful pullback comparisons, is the coefficient pullback tensored
with the underlying map. -/
theorem extendπ_comp_pullIso_inv
    {Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ S) (N : Modules Λ X) (g : (CondensedRing.upperStar Λ f).obj M ⟶ N)
    (m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (hm : (profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫ g.hom = m) :
    (upperStar Ab.{u + 1} f).map (Mod.extendπ (coefficientMap φ S) M) ≫
        (profinitePointModuleForgetPullbackIso A f).inv.app
          ((Mod.extendScalars (coefficientMap φ S)).obj M) ≫
        ((CondensedRing.pullIso φ f).inv.app M ≫
          (Mod.extendScalars (coefficientMap φ X)).map g).hom =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj A S) M.X ≫
        (condensedPullbackHom A f ⊗ₘ m) ≫ Mod.extendπ (coefficientMap φ X) N := by
  subst hm
  exact extendedComparison_normalized f Λ A φ M N g

/-- The pullback isomorphism of a pull endpoint, extended along a change of coefficients. -/
def PullEndpoint.extendScalarsIso
    {Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules Λ S} {N : Modules Λ X} {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint Λ f M N m) :
    (CondensedRing.upperStar A f).obj ((Mod.extendScalars (coefficientMap φ S)).obj M) ≅
      (Mod.extendScalars (coefficientMap φ X)).obj N :=
  ((CondensedRing.pullIso φ f).app M).symm ≪≫
    (Mod.extendScalars (coefficientMap φ X)).mapIso e.iso

/-- On balanced tensor generators, the extended pull endpoint is the coefficient pullback
tensored with the original map. -/
theorem PullEndpoint.extendπ_comp_extendScalarsIso
    {Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules Λ S} {N : Modules Λ X} {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint Λ f M N m) :
    (upperStar Ab.{u + 1} f).map (Mod.extendπ (coefficientMap φ S) M) ≫
        (profinitePointModuleForgetPullbackIso A f).inv.app
          ((Mod.extendScalars (coefficientMap φ S)).obj M) ≫
        (e.extendScalarsIso φ).hom.hom =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj A S) M.X ≫
        (condensedPullbackHom A f ⊗ₘ m) ≫ Mod.extendπ (coefficientMap φ X) N :=
  extendπ_comp_pullIso_inv φ f M N e.iso.hom m e.forget_comp_iso_hom

/-- A pull endpoint extends along a change of coefficients, with the extended map fixed on
balanced tensor generators by the coefficient pullback `c` and the original map. -/
theorem PullEndpoint.exists_extendScalars
    {Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules Λ S} {N : Modules Λ X} {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint Λ f M N m)
    {c : (upperStar Ab.{u + 1} f).obj (condensedRingObj A S) ⟶ condensedRingObj A X}
    (hc : condensedPullbackHom A f = c) :
    ∃ m' : (upperStar Ab.{u + 1} f).obj ((Mod.extendScalars (coefficientMap φ S)).obj M).X ⟶
        ((Mod.extendScalars (coefficientMap φ X)).obj N).X,
      (upperStar Ab.{u + 1} f).map (Mod.extendπ (coefficientMap φ S) M) ≫ m' =
        Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj A S) M.X ≫
          (c ⊗ₘ m) ≫ Mod.extendπ (coefficientMap φ X) N ∧
      Nonempty (PullEndpoint A f ((Mod.extendScalars (coefficientMap φ S)).obj M)
        ((Mod.extendScalars (coefficientMap φ X)).obj N) m') := by
  subst hc
  refine ⟨_, ?_, ⟨PullEndpoint.ofIso (e.extendScalarsIso φ)⟩⟩
  exact e.extendπ_comp_extendScalarsIso φ

/-- The coefficient pullback map of a ring of continuous maps does not depend on the proof
that the coefficient ring is a topological ring. -/
theorem condensedPullbackHom_continuousMapRingObj_congr (T : Type) [TopologicalSpace T]
    [Ring T] (p q : IsTopologicalRing T) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    condensedPullbackHom (@Profinite.continuousMapRingObj.{u} T _ _ p) f =
      condensedPullbackHom (@Profinite.continuousMapRingObj.{u} T _ _ q) f := by
  obtain rfl : p = q := rfl
  rfl

/-- An integral line endpoint extends to the ordinary quotient lines, with the quotient
pullback map fixed on balanced tensor generators. -/
theorem quotientLine_pullEndpoint
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    (e : PullEndpoint (Profinite.padicIntegersRingObj.{u} l E.1) f
      (spIntegralTwist S l E) (spIntegralTwist X l E) (spIntegralComparison f l E)) :
    ∃ m : (upperStar Ab.{u + 1} f).obj (quotientLine l E π n S).X ⟶
        (quotientLine l E π n X).X,
      QuotientPullMap l E π n f m ∧
      Nonempty (PullEndpoint (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
        f (quotientLine l E π n S) (quotientLine l E π n X) m) := by
  refine e.exists_extendScalars (quotientMap l E π n) ?_
  exact condensedPullbackHom_continuousMapRingObj_congr _ _ _ f

/-- The coefficient-unit pull endpoint given by the monoidal unit of module pullback. -/
def unitPullEndpoint
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X S : Scheme.{u}} (f : X ⟶ S) : UnitPullEndpoint R f where
  iso := (Functor.Monoidal.εIso (CondensedRing.upperStar R f)).symm
  normalization := CondensedRing.homEquiv_εIso_inv_hom R f

/-- Over Noetherian bases, the base squares and the four endpoints determine the
ordinary source pullback data: the canonical supported-source map is invertible. -/
def SourcePullback.ofEndpoints
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsNoetherian Y] [IsNoetherian Y']
    {L : ∀ X : Scheme.{u}, Modules R X}
    {mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X}
    {mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X}
    (b : BaseSquares g) (e : PullbackEndpoints R g L mP mW) :
    SourcePullback R g L mP mW where
  geometry := b
  endpoints := e
  supported :=
    have := diagonalScalar_source_map_isIso R g b e.cP
    asIso (sourcePullbackMap R g b.diagonal_square e.cP)
  supported_normalization := rfl

attribute [local irreducible] quotientLine quotientLineMap derivedUpper derivedLower
  derivedScalars modelExchange singlePullback PullEndpoint.shift Endpoint.shift

/-- Extension of the integral source and line comparisons to an ordinary quotient.
No class, trace, right derived model, or scalar compatibility is used here. -/
theorem diagonalQuotient_sourcePullback
    (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ)
    (s : SourcePullback (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E)
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)) :
    ∃ (mP : (upperStar Ab.{u + 1} (baseP g)).obj
        (quotientLine l E π n (ProjectiveLine Y)).X ⟶
          (quotientLine l E π n (ProjectiveLine Y')).X)
      (mW : (upperStar Ab.{u + 1} (baseW g)).obj
        (quotientLine l E π n (diagonalSurface Y)).X ⟶
          (quotientLine l E π n (diagonalSurface Y')).X),
      QuotientPullMap l E π n (baseP g) mP ∧
      QuotientPullMap l E π n (baseW g) mW ∧
      Nonempty (SourcePullback
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
        (quotientLine l E π n) mP mW) := by
  have hP := quotientLine_pullEndpoint l E π n (baseP g) s.endpoints.lineP
  have hW := quotientLine_pullEndpoint l E π n (baseW g) s.endpoints.lineW
  let R := Profinite.continuousMapRingObj.{u} (completedResidue l E π n)
  exact ⟨hP.choose, hW.choose, hP.choose_spec.1, hW.choose_spec.1,
    ⟨SourcePullback.ofEndpoints R g s.geometry ⟨unitPullEndpoint R g,
      unitPullEndpoint R (baseP g), hP.choose_spec.2.some, hW.choose_spec.2.some⟩⟩⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
