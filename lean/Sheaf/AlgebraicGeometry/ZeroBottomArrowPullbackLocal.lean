/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.AlgebraicGeometry.ZeroBottomArrowAffineChainModel
import Sheaf.AlgebraicGeometry.BottomFreeChainPullbackSquare

/-! # Local pullback of a bottom truncation arrow
Source: Stacks Project, Tag 0BDL, zero-matrix chart argument.
(blueprint: lem-sc-zero-bottom-arrow-pullback-local). -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bottom_homology_isIso_iff
    {C : Type*} [Category C] [Abelian C]
    {A B : CochainComplex C ℤ} (α : A ⟶ B) (a : ℤ)
    (hfA : (A.sc a).f = 0) (hgA : (A.sc a).g = 0)
    (hfB : (B.sc a).f = 0) (hgB : (B.sc a).g = 0) :
    IsIso (HomologicalComplex.homologyMap α a) ↔ IsIso (α.f a) := by
  let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) a).map α
  change IsIso (ShortComplex.homologyMap φ) ↔ IsIso (α.f a)
  rw [(ShortComplex.LeftHomologyMapData.ofZeros φ hfA hgA hfB hgB).homologyMap_eq]
  change IsIso (_ ≫ α.f a ≫ _) ↔ IsIso (α.f a)
  constructor
  · intro h
    let eA := (ShortComplex.LeftHomologyData.ofZeros (A.sc a) hfA hgA).homologyIso
    let eB := (ShortComplex.LeftHomologyData.ofZeros (B.sc a) hfB hgB).homologyIso
    have heq : α.f a = eA.inv ≫ (eA.hom ≫ α.f a ≫ eB.inv) ≫ eB.hom := by
      simp
    rw [heq]
    infer_instance
  · intro h
    infer_instance

private theorem bottom_incoming_zero
    {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℤ) (a : ℤ)
    (hprev : IsZero (K.X (a - 1))) : (K.sc a).f = 0 := by
  change K.d ((ComplexShape.up ℤ).prev a) a = 0
  rw [(ComplexShape.up ℤ).prev_eq' (by omega : a - 1 + 1 = a)]
  exact hprev.eq_of_src _ _

private theorem bottom_outgoing_zero
    {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℤ) (a : ℤ)
    (hzero : K.d a (a + 1) = 0) : (K.sc a).g = 0 := by
  change K.d a ((ComplexShape.up ℤ).next a) = 0
  rw [(ComplexShape.up ℤ).next_eq' (rfl : a + 1 = a + 1)]
  exact hzero

/-- On one zero-bottom model chart, pullback preserves the bottom homology
isomorphism of a specified arrow from a single sheaf.
Source: Stacks Project, Tags 0BDL, 06YD, 06YJ, 0D5S and 08CR, second proof.
(blueprint: lem-sc-zero-bottom-arrow-pullback-local).

Proof: Restrict f to U. Exact restriction and the given isomorphism e identify
its bottom homology with a map M|U -> K.X a; the map is invertible by hf.
Refine U by affine opens, trivializing M|U by this identification with the
finite free K.X a. On an affine refinement, represent the restricted derived
arrow by a chain map from the single finite-free complex to the restricted K
using the affine perfect-map representative theorem. Both complexes have zero
incoming and outgoing differentials at a. Their homology map therefore is the
a-th component of the chain map, which is invertible. Both complexes are
bounded above and flat. The natural flat-complex counit represents pullback
of the specified arrow by its termwise pullback. The a-th component remains
invertible, and the zero bottom differentials persist. Exact open restriction
and derived composition identify this computation with the restriction of
H^a(Lg*f). Take the inverse image of the affine refinement containing g(y).
This gives V containing y and the asserted invertibility on V. No gluing of
chosen local object isomorphisms is needed: the arrow f is fixed globally.
Zero ranks, negative a, empty opens, and an empty source cause no exception. -/
theorem zeroBottomArrow_pullback_local
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (D : schemeDerivedCategory T) (a : ℤ)
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace))
    (f : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj M ⟶ D)
    (hf : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).map f))
    (U : T.Opens)
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ)
    (hbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (K.X i))
    (hnegative : ∀ i : ℤ, i < a → IsZero (K.X i))
    (hzero : K.d a (a + 1) = 0)
    (hfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (e : (derivedPullback U.ι).obj D ≅ DerivedCategory.Q.obj K)
    (T' : Scheme.{u}) (g : T' ⟶ T) (y : T') (hy : g.base y ∈ U) :
    ∃ V : T'.Opens, y ∈ V ∧
      IsIso (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).map
          ((derivedPullback g).map f)).over V)  := by
  obtain ⟨W, hyW, _, _, A, B, hAbounded, hBbounded, hAfree, hBfree,
    hAsingle, hBnegative, hBzero, α, hHα, eA, eB, hsquare⟩ :=
    zeroBottomArrow_affine_chain_model T D a M f hf U K hbounded hnegative
      hzero hfree e (g.base y) hy
  have hAprev : IsZero (A.X (a - 1)) := hAsingle _ (by omega)
  have hBprev : IsZero (B.X (a - 1)) := hBnegative _ (by omega)
  have hAzero : A.d a (a + 1) = 0 := (hAsingle _ (by omega)).eq_of_tgt _ _
  have hα : IsIso (α.f a) :=
    (bottom_homology_isIso_iff α a (bottom_incoming_zero A a hAprev)
      (bottom_outgoing_zero A a hAzero) (bottom_incoming_zero B a hBprev)
      (bottom_outgoing_zero B a hBzero)).mp hHα
  obtain ⟨V, hyV, P, Q, hPprev, hQprev, hPzero, hQzero, β, hβ,
    eP, eQ, hcomm⟩ :=
    bottomFreeChain_pullback_square T _ D f a W A B hAbounded hBbounded
      hAfree hBfree hAprev hBprev hAzero hBzero α hα eA eB hsquare T' g y hyW
  have hHβ : IsIso (HomologicalComplex.homologyMap β a) :=
    (bottom_homology_isIso_iff β a (bottom_incoming_zero P a hPprev)
      (bottom_outgoing_zero P a hPzero) (bottom_incoming_zero Q a hQprev)
      (bottom_outgoing_zero Q a hQzero)).mpr hβ
  refine ⟨V, hyV, ?_⟩
  have heq : (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).map
        ((derivedPullback g).map f)).over V) =
      eP.hom ≫ HomologicalComplex.homologyMap β a ≫ eQ.inv := by
    calc
      _ = ((((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).map
            ((derivedPullback g).map f)).over V) ≫ eQ.hom) ≫ eQ.inv := by simp
      _ = _ := by rw [hcomm]; simp only [Category.assoc]
  rw [heq]
  infer_instance

end AlgebraicGeometry.Scheme
