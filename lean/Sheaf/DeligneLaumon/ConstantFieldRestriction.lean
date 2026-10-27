/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Transport
public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact
import WeilConjectures.WeilSheaf.UpperStarPointwise

/-! # Source Weil restriction along a finite constant extension

The functor is the restriction of the actual iterated pro-etale transport to
constructible objects. No common-stage category is substituted for the source.
Source: blueprint `thm-zl-real-mixed-by-curves`, first paragraph.
(blueprint: def-zl-source-constant-field-restriction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

variable {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₁))]
  (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y ↘ Spec (CommRingCat.of k₁)).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (Y ↘ Spec (CommRingCat.of k₁)).geometricGaloisFrobenius.hom =
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)

/-- Restriction to constructible objects of the explicit source transport.
Source: blueprint `thm-zl-real-mixed-by-curves`, first paragraph, constant extension.
(blueprint: def-zl-source-constant-field-restriction). -/
noncomputable def constantFieldRestriction : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l Y :=
  (WeilSheaf.objectProperty k₀ l X).liftFullSubcategory (WeilSheaf.objectProperty k₁ l Y)
    (ProEtaleWeilSheaf.transport θ r hθ) fun F hF ↦
      (IsAdicConstructibleSheaf.upperStar θ.inv hF).of_iso
        ((adicUpperStarIsoLowerStarInv l θ.symm).app F.carrier)

instance : (constantFieldRestriction (l := l) θ r hθ).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₁))] :
    PreservesFiniteLimits (constantFieldRestriction (l := l) θ r hθ) := by
  have : PreservesFiniteLimits (constantFieldRestriction (l := l) θ r hθ ⋙
      (WeilSheaf.objectProperty k₁ l Y).ι) :=
    preservesFiniteLimits_of_natIso (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm
  have : ReflectsLimitsOfSize.{0, 0} (WeilSheaf.objectProperty k₁ l Y).ι := inferInstance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₁ l Y).ι

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₁))] :
    PreservesFiniteColimits (constantFieldRestriction (l := l) θ r hθ) := by
  have : PreservesFiniteColimits (constantFieldRestriction (l := l) θ r hθ ⋙
      (WeilSheaf.objectProperty k₁ l Y).ι) :=
    preservesFiniteColimits_of_natIso (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm
  have : ReflectsColimitsOfSize.{0, 0} (WeilSheaf.objectProperty k₁ l Y).ι := inferInstance
  exact preservesFiniteColimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₁ l Y).ι

/-- Source constant-field transport preserves lissity, since its carrier is
pullback along an isomorphism of geometric fibers.
Source: blueprint `thm-zl-real-mixed-by-curves`, first paragraph.
(blueprint: def-zl-source-constant-field-restriction). -/
theorem isLisse_constantFieldRestriction {F : WeilSheaf k₀ l X} (hF : F.IsLisse) :
    ((constantFieldRestriction θ r hθ).obj F).IsLisse :=
  (IsAdicLisseSheaf.upperStar θ.inv hF).of_iso
    ((adicUpperStarIsoLowerStarInv l θ.symm).app F.obj.carrier)

/-- A functor has pointwise power transport along `c` when its stalks are
conjugate to positive powers at the image point, with the same residue-size power.
Source: blueprint `thm-zl-real-mixed-by-curves`, paragraphs 1--3.
(blueprint: def-zl-source-constant-field-restriction). -/
def HasPointwisePowerTransport (R : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l Y)
    (c : Y ⟶ X) : Prop :=
  ∀ z : Y.finitePoints, ∃ (z₀ : X.finitePoints) (e : ℕ),
    c z.1 = z₀.1 ∧ 0 < e ∧
    (Y ↘ Spec (CommRingCat.of k₁)).residueCard z.1 =
      (X ↘ Spec (CommRingCat.of k₀)).residueCard z₀.1 ^ e ∧
    ∀ F : WeilSheaf k₀ l X,
      Nonempty (((F.stalk z₀).powFrobenius e).Equiv ((R.obj F).stalk z))

/-- Pointwise power transport preserves reality, including repeated powered
Frobenius eigenvalues.
Source: blueprint `thm-zl-real-mixed-by-curves`, first paragraph.
(blueprint: def-zl-source-constant-field-restriction). -/
theorem HasPointwisePowerTransport.isReal
    {R : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l Y} {c : Y ⟶ X}
    (hR : HasPointwisePowerTransport R c) {F : WeilSheaf k₀ l X}
    {ι : PadicAlgCl l →+* ℂ} (hF : F.IsReal ι) : (R.obj F).IsReal ι := by
  intro z
  obtain ⟨z₀, e, _, _, _, h⟩ := hR z
  exact (hF z₀).of_charpoly_eq_pow e
    (by simpa only [FrobeniusModule.powFrobenius_frobeniusEnd] using
      (h F).some.charpoly_frobeniusEnd)

variable [Algebra k₀ k₁] [Algebra.IsAlgebraic k₀ k₁]
  {c : Y ⟶ X}

/-- Canonical source restriction for an actual cartesian constant-field square.
Source: blueprint `thm-zl-real-mixed-by-curves`, first paragraph.
(blueprint: def-zl-source-constant-field-restriction). -/
noncomputable abbrev constantFieldRestrictionOfSquare
    (hc : IsPullback c (Y ↘ Spec (CommRingCat.of k₁)) (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))))
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l Y :=
  constantFieldRestriction (Scheme.Hom.geometricFiberBaseChangeIso hc) r
    (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hc r hr)

end AlgebraicGeometry.WeilSheaf
