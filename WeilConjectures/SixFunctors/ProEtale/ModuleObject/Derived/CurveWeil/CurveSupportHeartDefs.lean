/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteOrClosedPerverseSubcategories
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.Basic

/-! # Support and cosupport describe the perverse heart on a smooth curve

Source: latest blueprint, part-weights-riemann-hypothesis/sec-fourier-transform/
sec-wft-perverse/sk-lem-wft-curve-heart/thm-a1-curve-perverse-heart.md and its proof
(thm-a1-curve-perverse-heart.proof.md), Steps 0--6.
The finite-or-algebraically-closed field scope follows Wei Yang #1441, item 36.
(blueprint: def-dl-a1-curve-support-assertions).

This statement uses the registered condensed support classes, not a definition of the
perverse classes by the cohomological description that the theorem must establish.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ell : ℕ) [Fact ell.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hbase : Finite k ∨ IsAlgClosed k)
  (C : Over (Spec (.of k))) [Smooth C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]

local notation "Λ" => Profinite.padicAlgClRingObj ell
local notation "R" => condensedRingObj Λ C.left
local notation "B" => BoundedConstructible R
local notation "M" => Mod (Sheaf (Scheme.ProEt.topology C.left) Ab) R
local notation "H" => DerivedCategory.homologyFunctor M
local notation "Perv" => FiniteOrClosedPerverseHeart ell hbase C
local notation "Punctual" => CondensedCurvePerverse.IsPunctual Λ C.left
local notation "NoPunctual" => CondensedCurvePerverse.HasNoPunctualSubsheaf Λ C.left

/-- The two equivalences in clause (1), using the existing punctual-sheaf predicates.
Source: curve-heart theorem, clause (1) (blueprint: thm-a1-curve-perverse-heart). -/
def CurveSupportDescription : Prop :=
  (∀ K : B, FiniteOrClosedPerverseLEZero ell hbase C K ↔
    (∀ a : ℤ, 0 < a → IsZero ((H a).obj K.obj)) ∧ Punctual ((H 0).obj K.obj)) ∧
  (∀ K : B, FiniteOrClosedPerverseGEZero ell hbase C K ↔
    (∀ a : ℤ, a < -1 → IsZero ((H a).obj K.obj)) ∧ NoPunctual ((H (-1)).obj K.obj))

/-- Clauses (2) and (3): the prescribed classes form a bounded t-structure and their
full intersection is abelian, with precisely the stated cohomological description.
Source: curve-heart theorem, clauses (2)--(3) (blueprint: thm-a1-curve-perverse-heart). -/
def CurveSupportHeart : Prop :=
  (∃ t : TStructure B,
    (∀ n : ℤ, t.le n = FiniteOrClosedPerverseLE ell hbase C n) ∧
    (∀ n : ℤ, t.ge n = FiniteOrClosedPerverseGE ell hbase C n) ∧ t.bounded = ⊤) ∧
  Nonempty (Abelian (Perv).FullSubcategory) ∧
  (∀ K : B, Perv K ↔
    (∀ a : ℤ, a ≠ -1 → a ≠ 0 → IsZero ((H a).obj K.obj)) ∧
    Punctual ((H 0).obj K.obj) ∧ NoPunctual ((H (-1)).obj K.obj))

/-- Clause (4), using ordinary module direct image, and the canonical residue-field
inclusion for each closed point. Existential membership only supplies the proof that
the displayed, already constructed complex is bounded constructible.
Source: curve-heart theorem, clause (4) (blueprint: thm-a1-curve-perverse-heart). -/
def CurveSupportBasicObjects : Prop :=
  (∀ (U : Scheme.{u}) (j : U ⟶ C.left), IsOpenImmersion j → DenseRange j →
    ∀ N : CondensedCurvePerverse.Modules Λ U, IsLisseCoefficientModule Λ N →
      ∃ K : B, Perv K ∧ Nonempty (K.obj ≅
        ((DerivedCategory.singleFunctor _ 0).obj ((lowerStar Λ j).obj N)) ⟦(1 : ℤ)⟧)) ∧
  (∀ x : C.left, IsClosed ({x} : Set C.left) →
    ∀ E : CondensedCurvePerverse.Modules Λ (Spec (.of (C.left.residueField x))),
      IsConstructibleModuleObject _ E →
      ∃ K : B, Perv K ∧ Nonempty (K.obj ≅ (DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar Λ (C.left.fromSpecResidueField x)).obj E)))

/-- The canonical standard truncation sequence is short exact in the perverse heart.
The comparisons to the two ordinary truncations specify the arrows; the further
isomorphisms identify its endpoints as H^-1(P)[1] and H^0(P)[0].
Source: curve-heart theorem, clause (5), first sentence
(blueprint: thm-a1-curve-perverse-heart). -/
def CurveSupportTruncationExact : Prop :=
  ∀ P : (Perv).FullSubcategory,
    ∃ (A D : (Perv).FullSubcategory) (S : ShortComplex (Perv).FullSubcategory),
      S.X₁ = A ∧ S.X₂ = P ∧ S.X₃ = D ∧ S.ShortExact ∧
      ∃ (e₁ : A.obj.obj ≅ (DerivedCategory.TStructure.t.truncLE (-1)).obj P.obj.obj)
        (e₂ : D.obj.obj ≅ (DerivedCategory.TStructure.t.truncGE 0).obj P.obj.obj),
        Nonempty (A.obj.obj ≅ ((DerivedCategory.singleFunctor M 0).obj
          ((H (-1)).obj P.obj.obj)) ⟦(1 : ℤ)⟧) ∧
        Nonempty (D.obj.obj ≅ (DerivedCategory.singleFunctor M 0).obj
          ((H 0).obj P.obj.obj)) ∧
        ∃ (f : A ⟶ P) (g : P ⟶ D),
          HEq S.f f ∧ HEq S.g g ∧
          f.hom.hom = e₁.hom ≫ (DerivedCategory.TStructure.t.truncLEι (-1)).app P.obj.obj ∧
          g.hom.hom = (DerivedCategory.TStructure.t.truncGEπ 0).app P.obj.obj ≫ e₂.inv

/-- The six-term sequence has the canonical connecting map of a distinguished triangle
with the given heart arrows. Endpoint mono/epi conditions include the two zero terms.
Source: curve-heart theorem, clause (5), second sentence
(blueprint: thm-a1-curve-perverse-heart). -/
def CurveSupportSixTermExact : Prop :=
  ∀ S : ShortComplex (Perv).FullSubcategory, S.ShortExact →
    ∃ d : S.X₃.obj.obj ⟶ S.X₁.obj.obj⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk S.f.hom.hom S.g.hom.hom d ∈ distTriang _ ∧
      let δ := DerivedCategory.HomologySequence.δ
        (Pretriangulated.Triangle.mk S.f.hom.hom S.g.hom.hom d) (-1) 0
      Mono ((H (-1)).map S.f.hom.hom) ∧ Epi ((H 0).map S.g.hom.hom) ∧
      (ComposableArrows.mk₂ ((H (-1)).map S.f.hom.hom)
        ((H (-1)).map S.g.hom.hom)).Exact ∧
      (ComposableArrows.mk₂ ((H (-1)).map S.g.hom.hom) δ).Exact ∧
      (ComposableArrows.mk₂ δ ((H 0).map S.f.hom.hom)).Exact ∧
      (ComposableArrows.mk₂ ((H 0).map S.f.hom.hom) ((H 0).map S.g.hom.hom)).Exact


end AlgebraicGeometry.ProEtale.CondensedRing


namespace AlgebraicGeometry.ProEtale.CondensedRing.CurveWeil

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  [Fact (ringChar D.k).Prime] [Fact (ringChar D.k ≠ ell)]
  (C₀ : Over (Spec (.of D.k₀))) [Smooth C₀.hom] [QuasiCompact C₀.hom]
  [IsSeparated C₀.hom]

local notation "Λ" => Profinite.padicAlgClRingObj ell
local notation "C" => D.geometricFiber C₀
local notation "g" => Iso.hom (WeilConjectures.FiniteFieldDatum.geometricFrobenius D C₀)
local notation "WM" => WeilConjectures.condensedWeilModules Λ g
local notation "Wprop" => WeilConjectures.condensedWeilComplexProperty Λ g
local notation "W" => WeilConjectures.condensedWeilComplex Λ g
local notation "For" => WeilConjectures.condensedWeilForget Λ g
local notation "H" => DerivedCategory.homologyFunctor WM
local notation "forgetM" => WeilConjectures.condensedWeilModuleForget Λ g
set_option quotPrecheck false in
local notation "Punctual" => CondensedCurvePerverse.IsPunctual Λ (C).left
set_option quotPrecheck false in
local notation "NoPunctual" => CondensedCurvePerverse.HasNoPunctualSubsheaf Λ (C).left

local instance : LocallyOfFiniteType (C).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd C₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
local instance : QuasiCompact (C).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd C₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
local instance : IsSeparated (C).hom :=
  inferInstanceAs (IsSeparated (pullback.snd C₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The registered support class pulled back along actual derived Weil forgetting.
Source: curve-heart theorem, Weil convention and clause (1)
(blueprint: thm-a1-curve-perverse-heart). -/
def upperZero : ObjectProperty W := fun K ↦ CondensedSupportCondition ell ((For).obj K)

/-- The registered cosupport class pulled back along actual derived Weil forgetting.
Source: curve-heart theorem, Weil convention and clause (1)
(blueprint: thm-a1-curve-perverse-heart). -/
def lowerZero : ObjectProperty W := fun K ↦
  FiniteOrClosedCosupportCondition ell (Or.inr (IsAlgClosure.isAlgClosed D.k₀)) C ((For).obj K)

/-- Full intersection of the prescribed Weil support and cosupport classes.
Source: curve-heart theorem, clause (2) (blueprint: thm-a1-curve-perverse-heart). -/
def heart : ObjectProperty W := upperZero D ell C₀ ⊓ lowerZero D ell C₀

local notation "Perv" => heart D ell C₀

/-- Both descriptions for Weil objects, testing punctuality on geometric sheaves.
Source: curve-heart theorem, clause (1) and Weil convention
(blueprint: thm-a1-curve-perverse-heart). -/
def Description : Prop :=
  (∀ K : W, upperZero D ell C₀ K ↔
    (∀ a : ℤ, 0 < a → IsZero ((H a).obj K.obj)) ∧
      Punctual ((forgetM).obj ((H 0).obj K.obj))) ∧
  (∀ K : W, lowerZero D ell C₀ K ↔
    (∀ a : ℤ, a < -1 → IsZero ((H a).obj K.obj)) ∧
      NoPunctual ((forgetM).obj ((H (-1)).obj K.obj)))

/-- The bounded perverse t-structure and abelian heart on the actual Weil derived category.
The existential triangulated instance is inherited from its full derived subcategory.
Source: curve-heart theorem, clauses (2)--(3) and Weil convention
(blueprint: thm-a1-curve-perverse-heart). -/
def HeartAssertions : Prop :=
  (Exists fun [_hTri : (Wprop).IsTriangulated] ↦
    ∃ t : TStructure W,
      t.le 0 = upperZero D ell C₀ ∧ t.ge 0 = lowerZero D ell C₀ ∧ t.bounded = ⊤) ∧
  Nonempty (Abelian (Perv).FullSubcategory) ∧
  (∀ K : W, Perv K ↔
    (∀ a : ℤ, a ≠ -1 → a ≠ 0 → IsZero ((H a).obj K.obj)) ∧
      Punctual ((forgetM).obj ((H 0).obj K.obj)) ∧
      NoPunctual ((forgetM).obj ((H (-1)).obj K.obj)))

/-- Ordinary middle direct image with its canonical Frobenius mate, and direct image
from a closed point. A closed point is presented by a closed immersion from a field
spectrum; this includes the canonical residue-field immersion, with no rationality assumption.
Source: curve-heart theorem, clause (4) and Weil convention
(blueprint: thm-a1-curve-perverse-heart). -/
def BasicObjects : Prop :=
  (∀ (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (j₀ : U₀ ⟶ C₀), IsOpenImmersion j₀.left → DenseRange j₀.left →
    ∀ N : WeilConjectures.NativeL2.WeilModule D ell U₀,
      IsLisseCoefficientModule Λ N.carrier →
      ∃ K : W, Perv K ∧ Nonempty (K.obj ≅
        ((DerivedCategory.singleFunctor WM 0).obj
          (WeilConjectures.NativeL2.middleWeilImage D ell j₀ N)) ⟦(1 : ℤ)⟧)) ∧
  (∀ (Z₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ C₀), IsClosedImmersion i₀.left →
    (∃ (F : Type u) (_ : Field F), Nonempty (Z₀.left ≅ Spec (.of F))) →
    ∀ E : WeilConjectures.NativeL2.WeilModule D ell Z₀,
      IsConstructibleModuleObject _ E.carrier →
      ∃ K : W, Perv K ∧ Nonempty (K.obj ≅ (DerivedCategory.singleFunctor WM 0).obj
        (WeilConjectures.NativeL2.middleWeilImage D ell i₀ E)))

/-- Standard truncation gives the canonical short exact sequence in the Weil heart.
All arrows are in the derived Weil category, so their Weil compatibility is retained.
Source: curve-heart theorem, clause (5), first sentence
(blueprint: thm-a1-curve-perverse-heart). -/
def TruncationExact : Prop :=
  ∀ P : (Perv).FullSubcategory,
    ∃ (A B : (Perv).FullSubcategory) (S : ShortComplex (Perv).FullSubcategory),
      S.X₁ = A ∧ S.X₂ = P ∧ S.X₃ = B ∧ S.ShortExact ∧
      ∃ (e₁ : A.obj.obj ≅ (DerivedCategory.TStructure.t.truncLE (-1)).obj P.obj.obj)
        (e₂ : B.obj.obj ≅ (DerivedCategory.TStructure.t.truncGE 0).obj P.obj.obj),
        Nonempty (A.obj.obj ≅ ((DerivedCategory.singleFunctor WM 0).obj
          ((H (-1)).obj P.obj.obj)) ⟦(1 : ℤ)⟧) ∧
        Nonempty (B.obj.obj ≅ (DerivedCategory.singleFunctor WM 0).obj
          ((H 0).obj P.obj.obj)) ∧
        ∃ (f : A ⟶ P) (h : P ⟶ B), HEq S.f f ∧ HEq S.g h ∧
          f.hom.hom = e₁.hom ≫ (DerivedCategory.TStructure.t.truncLEι (-1)).app P.obj.obj ∧
          h.hom.hom = (DerivedCategory.TStructure.t.truncGEπ 0).app P.obj.obj ≫ e₂.inv

/-- The canonical six-term ordinary cohomology sequence in actual Weil modules.
Source: curve-heart theorem, clause (5), second sentence
(blueprint: thm-a1-curve-perverse-heart). -/
def SixTermExact : Prop :=
  ∀ S : ShortComplex (Perv).FullSubcategory, S.ShortExact →
    ∃ d : S.X₃.obj.obj ⟶ S.X₁.obj.obj⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk S.f.hom.hom S.g.hom.hom d ∈ distTriang _ ∧
      let δ := DerivedCategory.HomologySequence.δ
        (Pretriangulated.Triangle.mk S.f.hom.hom S.g.hom.hom d) (-1) 0
      Mono ((H (-1)).map S.f.hom.hom) ∧ Epi ((H 0).map S.g.hom.hom) ∧
      (ComposableArrows.mk₂ ((H (-1)).map S.f.hom.hom)
        ((H (-1)).map S.g.hom.hom)).Exact ∧
      (ComposableArrows.mk₂ ((H (-1)).map S.g.hom.hom) δ).Exact ∧
      (ComposableArrows.mk₂ δ ((H 0).map S.f.hom.hom)).Exact ∧
      (ComposableArrows.mk₂ ((H 0).map S.f.hom.hom) ((H 0).map S.g.hom.hom)).Exact


end AlgebraicGeometry.ProEtale.CondensedRing.CurveWeil
