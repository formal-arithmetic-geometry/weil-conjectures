/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Algebra.Homology.FilteredPageLocalizationSetup
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import Sheaf.Algebra.Homology.DerivedTensorModuleTorComparison
import Sheaf.Algebra.Homology.KunnethCanonicalFirstPage

/-! # The first page of the canonically filtered derived tensor

Source: Stacks Project, More on Algebra, Tags 0H7Y and 0H7Z.
(blueprint: lem-kun-filtered-first-page).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject

namespace DerivedCategory

variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem bifunctor_iso_naturality
    {A B : ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R} (e : A ≅ B)
    {X X' Y Y' : ModuleCat.{u} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    (A.map f).app Y ≫ (A.obj X').map g ≫ ((e.app X').app Y').hom =
      ((e.app X).app Y).hom ≫ (B.map f).app Y ≫ (B.obj X').map g := by
  have h₁ := NatTrans.congr_app (e.hom.naturality f) Y
  have h₂ := (e.app X').hom.naturality g
  dsimp only [NatTrans.comp_app] at h₁ h₂
  change (A.obj X').map g ≫ (e.hom.app X').app Y' =
    (e.hom.app X').app Y ≫ (B.obj X').map g at h₂
  change (A.map f).app Y ≫ (A.obj X').map g ≫ (e.hom.app X').app Y' =
    (e.hom.app X).app Y ≫ (B.map f).app Y ≫ (B.obj X').map g
  rw [h₂, ← Category.assoc, h₁, Category.assoc]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem sigma_bifunctor_iso_naturality
    {J : Type v} [HasCoproductsOfShape J (ModuleCat.{u} R)]
    {A B : ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R} (e : A ≅ B)
    (X X' Y Y' : J → ModuleCat.{u} R)
    (f : ∀ i, X i ⟶ X' i) (g : ∀ i, Y i ⟶ Y' i) :
    Limits.Sigma.map (fun i ↦ (A.map (f i)).app (Y i) ≫ (A.obj (X' i)).map (g i)) ≫
        (Limits.Sigma.mapIso (fun i ↦ (e.app (X' i)).app (Y' i))).hom =
      (Limits.Sigma.mapIso (fun i ↦ (e.app (X i)).app (Y i))).hom ≫
        Limits.Sigma.map (fun i ↦ (B.map (f i)).app (Y i) ≫ (B.obj (X' i)).map (g i)) := by
  apply Limits.Sigma.hom_ext
  intro i
  simp only [Category.assoc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_mapIso_hom_assoc,
    Limits.Sigma.ι_mapIso_hom, Limits.Sigma.ι_map]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ Limits.Sigma.ι (fun j ↦ (B.obj (X' j)).obj (Y' j)) i)
    (bifunctor_iso_naturality R e (f i) (g i))

set_option maxHeartbeats 1000000 in
-- The coproduct comparison carries several large dependent functor expressions.
/-- The canonical convolution filtration represents the derived tensor, and its first
page is the direct sum of Tor of cohomology, naturally in both derived arguments.
This is only the filtered realization and first-page computation; convergence and
stationary identifications are supplied independently by finite filtered convergence.
Source: Stacks Project, Tags 0H7X, 0H7Y and 0H7Z, and Algebra Tags 00LY and 00LZ
(blueprint: lem-kun-filtered-first-page).

Proof. Apply `exists_derivedCanonicalFiltration` separately to the two bounded derived
objects and compose with the convolution bifunctor in `filteredTensor_localization`.
The forgetful comparison of the former and the tensor comparison of the latter identify
the ordinary derived object with C tensor D. Compare these forgetful functors with the
one in `d` through their normalized localization squares. Apply cohomology and transport
`d.Hbar` along this natural identification, giving the displayed filtration and filtered
isomorphism. Their naturality gives the filtered map h below and its underlying map.
For the first page, use `d.page_one` and the graded convolution comparison. The canonical
graded pieces of the factors are H^{-i}(C)[i] and H^{-j}(D)[j]. On a common finite support,
cohomology commutes with the finite direct sum. The signed shift comparison identifies
the cohomology in total degree a+b of their tensor with Tor_{-2a-b}. Compute this Tor using
a nonpositive projective resolution in the first variable and K-flat tensor comparison;
positive cochain cohomology is zero. Resolution lifts identify the induced homology map
with the Tor map in the first variable, while the second-variable map is the tensor of
the identity with the given map. Set a=-q, b=p+2q and replace i,j by -i,-j. The Tor degree
is -p and the summation condition becomes i+j=q. These natural comparisons give e₁ and
its direct-sum map equation. Only finite filtration bounds, not term bounds for K-flat
replacements or a global-dimension bound, are used. -/
theorem exists_kunnethFilteredFirstPage (d : FilteredPageLocalizationData R) :
    let I (k : ℤ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
      if k < 0 then
        (Functor.const (ModuleCat.{u} R)).obj
          ((Functor.const (ModuleCat.{u} R)).obj (0 : ModuleCat.{u} R))
      else Tor' (ModuleCat.{u} R) k.toNat
    let P (p q : ℤ) (C D : Bounded (ModuleCat.{u} R)) : ModuleCat.{u} R :=
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
        ((I (-p)).obj ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C.obj)).obj
          ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj)
    let m (p q : ℤ) {C C' D D' : Bounded (ModuleCat.{u} R)}
        (f : C ⟶ C') (g : D ⟶ D') : P p q C D ⟶ P p q C' D' :=
      Limits.Sigma.map fun ij ↦
        ((I (-p)).map ((homologyFunctor (ModuleCat.{u} R) ij.val.1).map f.hom)).app
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj) ≫
          ((I (-p)).obj ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C'.obj)).map
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).map g.hom)
    ∃ (U : Bounded (ModuleCat.{u} R) ⥤ Bounded (ModuleCat.{u} R) ⥤
          finiteFilteredModuleDerivedCategory R)
      (F : ∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        DecreasingFiltration ((homologyFunctor (ModuleCat.{u} R) n).obj (C.obj ⊗ D.obj)))
      (eH : ∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        (d.Hbar n).obj ((U.obj C).obj D) ≅
          (⟨(homologyFunctor (ModuleCat.{u} R) n).obj (C.obj ⊗ D.obj),
            F C D n⟩ : FilteredObject (ModuleCat.{u} R)))
      (e₁ : ∀ (C D : Bounded (ModuleCat.{u} R)) (p q : ℤ),
        ((d.Sbar.obj ((U.obj C).obj D)).page 1).X (-q, p + 2 * q) ≅ P p q C D),
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D')
          (p q : ℤ),
        ((d.Sbar.map ((U.map f).app D ≫ (U.obj C').map g)).hom 1).f (-q, p + 2 * q) ≫
            (e₁ C' D' p q).hom =
          (e₁ C D p q).hom ≫ m p q f g) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D') (n : ℤ),
        ∃ h : (⟨(homologyFunctor (ModuleCat.{u} R) n).obj (C.obj ⊗ D.obj), F C D n⟩ :
            FilteredObject (ModuleCat.{u} R)) ⟶
          ⟨(homologyFunctor (ModuleCat.{u} R) n).obj (C'.obj ⊗ D'.obj), F C' D' n⟩,
          h.hom = (homologyFunctor (ModuleCat.{u} R) n).map (f.hom ⊗ₘ g.hom) ∧
          (d.Hbar n).map ((U.map f).app D ≫ (U.obj C').map g) ≫ (eH C' D' n).hom =
            (eH C D n).hom ≫ h) := by
  classical
  dsimp only
  obtain ⟨U, F, eH, e₁, h₁, hH⟩ := exists_kunnethCanonicalFirstPage R d
  let eT (p : ℤ) : kunnethModuleTensorHomology R p ≅
      (if -p < 0 then
        (Functor.const (ModuleCat.{u} R)).obj
          ((Functor.const (ModuleCat.{u} R)).obj (0 : ModuleCat.{u} R))
      else Tor' (ModuleCat.{u} R) (-p).toNat) := by
    simpa only [neg_neg] using
      (kunnethModuleTensorHomology_tor (R := R) (-p)).some
  let e₂ (C D : Bounded (ModuleCat.{u} R)) (p q : ℤ) :=
    e₁ C D p q ≪≫ Limits.Sigma.mapIso
      (fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
        ((eT p).app ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C.obj)).app
          ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj))
  refine ⟨U, F, eH, e₂, ?_, hH⟩
  intro C C' D D' f g p q
  dsimp only [e₂, Iso.trans_hom]
  rw [← Category.assoc, h₁ C C' D D' f g p q, Category.assoc]
  exact congrArg ((e₁ C D p q).hom ≫ ·)
    (sigma_bifunctor_iso_naturality R
      (J := {ij : ℤ × ℤ // ij.1 + ij.2 = q}) (eT p)
      (fun ij ↦ (homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C.obj)
      (fun ij ↦ (homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C'.obj)
      (fun ij ↦ (homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj)
      (fun ij ↦ (homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D'.obj)
      (fun ij ↦ (homologyFunctor (ModuleCat.{u} R) ij.val.1).map f.hom)
      (fun ij ↦ (homologyFunctor (ModuleCat.{u} R) ij.val.2).map g.hom))

end DerivedCategory
