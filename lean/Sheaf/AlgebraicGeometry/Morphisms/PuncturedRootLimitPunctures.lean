/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.AdjoinRoot

/-! # Auxiliary limit statements for punctured root charts
Source: Stacks Project, Tags 0BSK, 05N9 and 01YW. -/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Punctured root charts commute with cofiltered affine ring colimits over R.

Source: Stacks Project, Tags 05N9 and 01YW; universal properties of polynomial
quotients and localization.
(blueprint: lem-sbc-punctured-root-colimit-continuity)

Proof: At each j take the localization of F(j)[T]/(T^n-a_j(f)) at a_j(f).
Transition maps are induced by the ring maps, preserving the relation and the inverted
coefficient by naturality of a. Maps from the colimit of these rings to B are compatible
families of maps from F(j) to B together with compatible roots and inverses. Since the
index category is filtered and nonempty, these roots and inverses specify one element
and one inverse in B. The colimit property of c and e therefore identifies this colimit
with H[T]/(T^n-b(f))[1/b(f)]. The compatibility assumption identifies the coefficients.
Apply Spec to obtain the limit cone, using its right-adjoint property. The spectrum of
localization is the indicated basic open at each stage and at H. These identifications
respect the base maps by the localization and quotient universal properties, giving the
two displayed equations. Every diagram object is affine as a localized spectrum.
No regularity, monicity, or nontriviality is required: n=0 gives the relation 1-g;
f=0 gives localization at zero and hence the empty affine schemes. -/
theorem punctured_root_colimit_continuity
    (R H : CommRingCat.{u}) (f : R) (n : ℕ) (b : R ⟶ H)
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (F : Iᵒᵖ ⥤ CommRingCat.{u}) (c₀ : Cocone F) (hc₀ : IsColimit c₀)
    (a : (Functor.const Iᵒᵖ).obj R ⟶ F) (e₀ : c₀.pt ≅ H)
    (ha : ∀ j, a.app j ≫ c₀.ι.app j ≫ e₀.hom = b) :
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ (D : I ⥤ Scheme.{u}) (c : Cone D)
      (t : D ⟶ (Functor.const I).obj (Spec R)),
      Nonempty (IsLimit c) ∧ (∀ j, IsAffine (D.obj j)) ∧
      ∃ e : V.toScheme ≅ c.pt,
        (∀ j, e.hom ≫ c.π.app j ≫ t.app j = V.ι ≫ q ≫ Spec.map b) ∧
        ∀ j,
          let S := F.obj (Opposite.op j)
          let g := (a.app (Opposite.op j)).hom f
          let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
          let N := Spec (CommRingCat.of A)
          let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
          let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
          ∃ d : V.toScheme ≅ D.obj j,
            d.hom ≫ t.app j = V.ι ≫ q ≫ Spec.map (a.app (Opposite.op j)) := by sorry

end AlgebraicGeometry.Scheme
