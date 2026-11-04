/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.EtaleSupportRetraction
import WeilConjectures.AlgebraicGeometry.RelativeLineLowDegreeGeneral
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.Mathlib.CategoryTheory.Iso

/-!
# Standard-pair low-degree support vanishing

This is the affine-line calculation in Steps 2--3 of
`lem-pur-smooth-divisor-low-support`, before étale chart transport.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Low-degree support vanishing for the zero section of a relative affine line.

The proof is the standard-pair part of the blueprint.  Form the ordinary closed-support
triangle and compare its first term with the right-derived supported-kernel functor using
`etale_injective_support_sequence` and `closedUpperShriekCompLowerStarIso`.  The
bounded-below support triangle is then transported
through `rightDerivedFunctorPlusCompatibility`; this is the unbounded-versus-Plus comparison
needed before applying the long exact homology sequence.  Apply the affine-line projection.
`relativeLineLowDegreeGeneral` identifies the two degree-zero projection units with the
identity on the base Tate sheaf and kills degree one of the affine-line projection.  The
resulting exact sequence gives vanishing in degrees zero and one, while the nonnegative
resolution bound gives negative degrees.  The assertion is strictly local: it has no smooth
pair, codimension, or chart hypotheses beyond the zero section.
(source: clause (b), local-comparison paragraph beginning
"Both classes are global classes supported on D";
blueprint: lem-pur-smooth-divisor-low-support)
-/
theorem isZero_homology_rightDerivedSectionsWithSupport_standard_pair
    {k : Type u} [Field k] (ell N : ℕ) (hell : Nat.Prime ell)
    (hell_unit : IsUnit (ell : k)) (hN : 1 ≤ N)
    {Y G : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [QuasiCompact aY]
    (j : G ⟶ AffineSpace (ULift.{u} (Fin 1)) Y) [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ((ell ^ N : ℕ) : Λ) = 0) :
    ∀ q : ℤ, q < 2 →
      IsZero (((DerivedCategory.homologyFunctor _ q).obj
        ((sectionsWithSupport (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (AlgebraicGeometry.Scheme.finiteEtaleTateSheaf Λ (ell ^ N)
              (AffineSpace (ULift.{u} (Fin 1)) Y) (by simpa using hΛ) 1))))) := by
  intro q hq
  have hm : 0 < ell ^ N := pow_pos hell.pos _
  have hmk : IsUnit ((ell ^ N : ℕ) : Γ(Spec (.of k), ⊤)) := by
    simpa only [Nat.cast_pow, map_pow, map_natCast] using
      (hell_unit.pow N).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hmY : IsUnit ((ell ^ N : ℕ) : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using hmk.map aY.appTop.hom
  let p := (AffineSpace.over (ULift.{u} (Fin 1)) Y).hom
  have hmX : IsUnit ((ell ^ N : ℕ) : Γ(AffineSpace (ULift.{u} (Fin 1)) Y, ⊤)) := by
    simpa only [map_natCast] using hmY.map p.appTop.hom
  obtain ⟨-, c, -⟩ := Scheme.etaleFiniteTwistPullback Λ (ell ^ N) hm hΛ
  obtain ⟨e₀, eπ, -, -, hH1, hid⟩ :=
    relativeLineLowDegreeGeneral k ell hell hell_unit N hN Λ hΛ Y aY G j hj
  let F := lowerStar (ModuleCat.{u + 1} Λ) p
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  let LX := (upperStar (ModuleCat.{u + 1} Λ) p).obj
    (Scheme.finiteEtaleTateSheaf Λ (ell ^ N) Y hΛ 1)
  have : IsIso (F.map (adj.unit.app LX) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).hom.app _) :=
    isIso_of_comp_eq_comp_comp (a := 𝟙 _) (b := 𝟙 _) ((Category.id_comp _).trans hid.symm)
  have hres : IsIso (F.map (adj.unit.app LX)) := IsIso.of_isIso_comp_right _
    ((lowerStarComp (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).hom.app _)
  have hij : Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base =
      (Set.range j.base)ᶜ := by
    rw [hj, compl_compl]
  refine isZero_homology_rightDerived_sectionsWithSupport_of_retraction Λ
    (AffineSpace.zeroSection _ Y) j hij p (AffineSpace.zeroSection_comp_over _ Y) _ ?_ ?_ q hq
  · exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight adj.unit F)
      (c p hmY hmX 1)).1 hres
  · exact (hH1.of_iso (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso _ 1).symm).of_iso
      ((F.rightDerived 1).mapIso (c p hmY hmX 1)).symm

end AlgebraicGeometry.Etale
