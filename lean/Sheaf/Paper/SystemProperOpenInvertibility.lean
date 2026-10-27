/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.CompactSupportNativeSystemEvaluation
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.ProEtaleConstantModuleEncoding
public import Sheaf.Paper.ProEtaleConstructibleOrigin
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import all Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import all Sheaf.Paper.ProEtaleConstructibleOrigin
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf

/-! # Invertibility and finite normalization of the varying-ring proper/open mate

Source: Stacks Project, more-etale.tex, Tag 0F7B, lemma-shriek-proper-and-open,
and the simultaneous-system extension in the blueprint
(blueprint: lem-pur-system-proper-open-invertibility).

The mate, clopen projector, quotient coefficients and all evaluation comparisons
are existing constructions. Positive level n+1 is indexed by n : ℕ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits WeilConjectures
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftAdjoint constantSheaf

private theorem exists_iso_with_property
    {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [IsIso f]
    (P : (X ≅ Y) → Prop) (hP : ∀ e : X ≅ Y, e.hom = f → P e) :
    ∃ e : X ≅ Y, e.hom = f ∧ P e :=
  ⟨asIso f, asIso_hom f, hP (asIso f) (asIso_hom f)⟩

private theorem finite_iso_normalization
    {C D : Type*} [Category C] [Category D] (V : C ⥤ D)
    {X Y X' Y' : C} (s : X ≅ X') (t : Y ≅ Y') (e : X ≅ Y)
    {Z W : D} (a : Z ≅ V.obj X') (b : W ≅ V.obj Y') (g : Z ≅ W)
    (h : a.hom ≫ V.map s.inv ≫ V.map e.hom ≫ V.map t.hom = g.hom ≫ b.hom) :
    (a ≪≫ V.mapIso s.symm) ≪≫ V.mapIso e = g ≪≫ (b ≪≫ V.mapIso t.symm) := by
  apply Iso.ext
  apply (cancel_mono (V.map t.hom)).1
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    ← V.map_comp, Iso.inv_hom_id, V.map_id, Category.comp_id] using h

private theorem finite_iso_normalization_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (U : C ⥤ D) (V : D ⥤ E) {X Y : C} {X' Y' : D}
    (s : U.obj X ≅ X') (t : U.obj Y ≅ Y') (e : X ≅ Y)
    {Z W : E} (a : Z ≅ V.obj X') (b : W ≅ V.obj Y') (g : Z ≅ W)
    (f : X ⟶ Y) (he : e.hom = f)
    (h : a.hom ≫ V.map s.inv ≫ V.map (U.map f) ≫ V.map t.hom = g.hom ≫ b.hom) :
    (a ≪≫ V.mapIso s.symm) ≪≫ (U ⋙ V).mapIso e =
      g ≪≫ (b ≪≫ V.mapIso t.symm) := by
  apply finite_iso_normalization V s t (U.mapIso e) a b g
  simpa only [Functor.mapIso_hom, he] using h

private theorem inverse_naturality
    {C : Type*} [Category C] {X Y X' Y' : C} (e : X ≅ Y) (e' : X' ≅ Y')
    (f : X ⟶ X') (g : Y ⟶ Y') (h : f ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv = e.inv ≫ f := by
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

private theorem inverse_natural_app
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G)
    {M N : C} (f : M ⟶ N) (e : F.obj M ≅ G.obj M) (e' : F.obj N ≅ G.obj N)
    (he : e.hom = α.app M) (he' : e'.hom = α.app N) :
    G.map f ≫ e'.inv = e.inv ≫ F.map f := by
  apply inverse_naturality e e' (F.map f) (G.map f)
  rw [he, he']
  exact α.naturality f

private theorem iso_square_isIso
    {C : Type*} [Category C] {X Y Z W : C}
    (a : X ≅ Y) (b : Z ≅ W) (d : X ≅ W) (f : Y ⟶ Z)
    (h : a.hom ≫ f ≫ b.hom = d.hom) : IsIso f := by
  have : IsIso (a.hom ≫ f ≫ b.hom) := by rw [h]; infer_instance
  have := IsIso.of_isIso_comp_left a.hom (f ≫ b.hom)
  exact IsIso.of_isIso_comp_right f b.hom

private theorem system_isIso_of_evaluations
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    (X : Scheme.{u}) {M N : Derived C τ X} (f : M ⟶ N)
    (hf : ∀ n : ℕ, IsIso (((E C τ n X) ⋙ StrictTower.ev (C n) X 0).map f)) :
    IsIso f := by
  let S := (SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (coefficients C X) (transition C τ X)).some
  apply S.systems.detects f
  intro n
  let d : E C τ n X ⋙ StrictTower.ev (C n) X 0 ≅
      SemilinearSections.e (Scheme.ProEt.topology X) (coefficients C X)
        (transition C τ X) n :=
    (Functor.mapDerivedCategoryCompIso (levelTower C τ n X)
      ((CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules (C n) X)).obj
        (Opposite.op 0))).symm ≪≫
      Functor.mapDerivedCategoryNatIso (Iso.refl _)
  exact (NatIso.isIso_map_iff d f).mp (hf n)

private theorem scalar_origin (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (K : DerivedCategory (StrictTower.Modules (ULift.{u + 1, u} B) X))
    (hc : ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X
      (ULift.{u + 1, u} B) ((Scheme.proEtaleModuleRestriction X B).obj
        ((DerivedCategory.homologyFunctor _ q).obj K)))
    (hb : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    ∃ w : StrictTower.ScalarEtaleOrigin (ULift.{u + 1, u} B) X K,
      w.Λ = ULift.{u + 1, u} B ∧ HEq w.φ (RingHom.id (ULift.{u + 1, u} B)) := by
  classical
  let A := ULift.{u + 1, u} B
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let U := StrictTower.fixedRestriction A X
  have : U.IsEquivalence := StrictTower.fixedRestriction_equivalence A X
  have : U.Additive := StrictTower.fixedRestriction_additive A X
  have hc' (q : ℤ) : ProEtale.IsConstructible A
      ((DerivedCategory.homologyFunctor _ q).obj (U.mapDerivedCategory.obj K)) := by
    obtain ⟨S, _, _, hS⟩ := hc q
    have hs : ProEtale.IsConstructible A
        (U.obj ((DerivedCategory.homologyFunctor _ q).obj K)) :=
      ⟨S, fun i ↦ Scheme.finite_models_of_fixed_lisse (S.domain i) A _ (hS i)⟩
    exact ProEtale.isConstructible_of_iso
      ((U.mapDerivedCategoryHomologyFunctorIso q).app K) hs
  obtain ⟨a, b, hab, hz⟩ := hb
  obtain ⟨L, hL, ⟨e⟩⟩ := fixedDerivedOrigin X A (U.mapDerivedCategory.obj K)
    hc' a b (fun q hq ↦ U.isZero_homologyFunctor_mapDerivedCategory_obj (hz q hq))
  have hplus : DerivedCategory.TStructure.t.plus L := by
    obtain ⟨c, d, _, hcd⟩ := hL.2
    exact ⟨c, (DerivedCategory.isGE_iff L c).mpr (fun q hq ↦ hcd q (Or.inl hq))⟩
  let Lp : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨L, hplus⟩
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
  let V := ProEtale.finiteCoefficientRealization X A
  let R := StrictTower.finiteRestriction A X A (RingHom.id A)
  let F := (ProEtale.finiteCoefficientComparison X A).mapDerivedCategoryPlus.obj Lp
  have c : StrictTower.C A X A (RingHom.id A) ⋙ U ≅ 𝟭 _ := by
    refine StrictTower.cFixed A X A (RingHom.id A) ≪≫ ?_
    exact Iso.refl _
  have : (StrictTower.C A X A (RingHom.id A) ⋙ U).IsEquivalence :=
    Functor.isEquivalence_of_iso c.symm
  have : (StrictTower.C A X A (RingHom.id A) ⋙ U).Additive :=
    Functor.additive_of_iso c.symm
  have ce : U.mapDerivedCategory.obj (R.mapDerivedCategory.obj F.obj) ≅
      ν.mapDerivedCategory.obj L := by
    exact U.mapDerivedCategory.mapIso (R.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryCompIso ν V).app L)) ≪≫
      (Functor.mapDerivedCategoryCompIso R U).symm.app _ ≪≫
      (Functor.mapDerivedCategoryCompIso V (R ⋙ U)).symm.app
        (ν.mapDerivedCategory.obj L) ≪≫
      (Functor.mapDerivedCategoryNatIso c).app (ν.mapDerivedCategory.obj L) ≪≫
      (Functor.mapDerivedCategoryIdIso _).app (ν.mapDerivedCategory.obj L)
  refine ⟨{ Λ := A
            φ := RingHom.id A
            F := F
            origin := { L := Lp, alpha := Iso.refl _ }
            iso := U.mapDerivedCategory.preimageIso (ce ≪≫ e) }, rfl, HEq.rfl⟩

variable (l : ℕ) [Fact l.Prime] (E₀ : Type u) [Field E₀]
  [Algebra (Padic l) E₀] [FiniteDimensional (Padic l) E₀]

/-- The canonical finite-source identification, retaining the chosen origin and both
ordinary derived evaluations. Source: Stacks 0F7B; Zheng 4.10
(blueprint: lem-pur-system-proper-open-invertibility). -/
def systemProperOpenFiniteSource {A C T : Scheme.{u}} (r : A ⟶ C) (i : C ⟶ T)
    [IsProper r] [IsOpenImmersion i]
    (H : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) A)
    (n : ℕ) (w : StrictTower.ScalarEtaleOrigin (compactSupportSystemLevel l E₀ n) A
      ((StrictTower.ev (compactSupportSystemLevel l E₀ n) A 0).obj
        ((E (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) n A).obj H))) :=
  StrictTower.finiteSource (compactSupportSystemLevel l E₀ n) r i
    ((E (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) n A).obj H) 0 w ≪≫
  (StrictTower.ev (compactSupportSystemLevel l E₀ n) T 0).mapIso
    (evalSource (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) n r i H).symm

/-- The canonical finite-target identification, with exactly the same origin witness.
Source: Stacks 0F7B; Zheng 4.10
(blueprint: lem-pur-system-proper-open-invertibility). -/
def systemProperOpenFiniteTarget {A B T : Scheme.{u}} (k : A ⟶ B) (p : B ⟶ T)
    [IsOpenImmersion k] [IsProper p]
    (H : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) A)
    (n : ℕ) (w : StrictTower.ScalarEtaleOrigin (compactSupportSystemLevel l E₀ n) A
      ((StrictTower.ev (compactSupportSystemLevel l E₀ n) A 0).obj
        ((E (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) n A).obj H))) :=
  StrictTower.finiteTarget (compactSupportSystemLevel l E₀ n) k p
    ((E (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) n A).obj H) 0 w ≪≫
  (StrictTower.ev (compactSupportSystemLevel l E₀ n) T 0).mapIso
    (evalTarget (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) n k p H).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] R J gamma evalSource evalTarget
  StrictTower.finiteSource StrictTower.finiteTarget


set_option maxHeartbeats 20000 in
-- Diagnostic limit for the final comparison application.
/-- The specified proper/open mate is invertible on levelwise bounded constructible
systems, and its forward and inverse arrows have the specified finite normalization.
Source: Stacks Project, Tag 0F7B, open-immersion case, and the varying-ring extension
(blueprint: lem-pur-system-proper-open-invertibility).

Proof: At each level, finite lisse models and bounded derived descent supply an
identity-scalar etale origin. The existing gamma_finite equation compares the evaluated
mate to the finite comparison, so every evaluation is invertible. Ordinary derived
composition comparisons identify these evaluations with the jointly conservative level
evaluations. Naturality and cancellation give inverse naturality; gamma_finite and
cancellation give the specified normalization for every identity-scalar origin.
The construction includes empty schemes, refinement and noncartesian squares, and
independent cohomological bounds at each level. -/
theorem systemProperOpenInvertibility
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {A B C T : Scheme.{u}}
    [A.Over (Spec (.of D.k))] [B.Over (Spec (.of D.k))]
    [C.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (A ↘ Spec (.of D.k))] [QuasiCompact (A ↘ Spec (.of D.k))]
    [IsSeparated (A ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of D.k))] [QuasiCompact (B ↘ Spec (.of D.k))]
    [IsSeparated (B ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (C ↘ Spec (.of D.k))] [QuasiCompact (C ↘ Spec (.of D.k))]
    [IsSeparated (C ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ T) (i : C ⟶ T)
    [k.IsOver (Spec (.of D.k))] [r.IsOver (Spec (.of D.k))]
    [p.IsOver (Spec (.of D.k))] [i.IsOver (Spec (.of D.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (H : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) A)
    (hH : ∀ n : ℕ,
      (∀ q : ℤ, @Scheme.IsConstructibleProEtaleFixedModuleSheaf A
        (compactSupportSystemLevel l E₀ n) _
        (@Finite.of_equiv
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E₀ (n + 1)))
          (Padic.coefficientExtensionRing l E₀ (n + 1))
          (Padic.finite_coefficientExtensionRing l E₀ (n + 1) (Nat.succ_pos n))
          Equiv.ulift.symm)
        ((Scheme.proEtaleModuleRestriction A
          (Padic.coefficientExtensionRing l E₀ (n + 1))).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((StrictTower.ev (compactSupportSystemLevel l E₀ n) A 0).obj
              ((E (compactSupportSystemLevel l E₀)
                (compactSupportSystemQuotient l E₀) n A).obj H))))) ∧
      ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((StrictTower.ev (compactSupportSystemLevel l E₀ n) A 0).obj
            ((E (compactSupportSystemLevel l E₀)
              (compactSupportSystemQuotient l E₀) n A).obj H)))) :
    ∃ e :
      (J (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) i).obj
        ((R (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) r).obj H) ≅
      (R (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) p).obj
        ((J (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) k).obj H),
      e.hom = (gamma (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) k r p i h).app H ∧
      (∀ (H' : Derived (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) A) (f : H ⟶ H')
        (e' :
          (J (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) i).obj
            ((R (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) r).obj H') ≅
          (R (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) p).obj
            ((J (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) k).obj H')),
        e'.hom = (gamma (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) k r p i h).app H' →
        (R (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) p).map
            ((J (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) k).map f) ≫
            e'.inv = e.inv ≫
          (J (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) i).map
            ((R (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) r).map f)) ∧
      ∀ n : ℕ,
        (∃ w : StrictTower.ScalarEtaleOrigin (compactSupportSystemLevel l E₀ n) A
          ((StrictTower.ev (compactSupportSystemLevel l E₀ n) A 0).obj
            ((E (compactSupportSystemLevel l E₀)
              (compactSupportSystemQuotient l E₀) n A).obj H)),
          w.Λ = (compactSupportSystemLevel l E₀ n : Type (u + 1)) ∧
          HEq w.φ (RingHom.id (compactSupportSystemLevel l E₀ n))) ∧
        ∀ w : StrictTower.ScalarEtaleOrigin (compactSupportSystemLevel l E₀ n) A
          ((StrictTower.ev (compactSupportSystemLevel l E₀ n) A 0).obj
            ((E (compactSupportSystemLevel l E₀)
              (compactSupportSystemQuotient l E₀) n A).obj H)),
          w.Λ = (compactSupportSystemLevel l E₀ n : Type (u + 1)) →
          HEq w.φ (RingHom.id (compactSupportSystemLevel l E₀ n)) →
          systemProperOpenFiniteSource l E₀ r i H n w ≪≫
            ((E (compactSupportSystemLevel l E₀)
                (compactSupportSystemQuotient l E₀) n T) ⋙
              StrictTower.ev (compactSupportSystemLevel l E₀ n) T 0).mapIso e =
            (StrictTower.HD (compactSupportSystemLevel l E₀ n) T w.Λ w.φ).mapIso
              ((StrictTower.finiteGamma w.Λ k r p i h).app w.origin.L) ≪≫
              systemProperOpenFiniteTarget l E₀ k p H n w := by
  classical
  have hfinite (n : ℕ) : Finite ((compactSupportSystemLevel l E₀) n) :=
    Finite.of_equiv (Padic.coefficientExtensionRing l E₀ (n + 1)) Equiv.ulift.symm
  have origins (n : ℕ) :
      ∃ w : StrictTower.ScalarEtaleOrigin ((compactSupportSystemLevel l E₀) n) A
        ((StrictTower.ev ((compactSupportSystemLevel l E₀) n) A 0).obj
          ((E (compactSupportSystemLevel l E₀)
            (compactSupportSystemQuotient l E₀) n A).obj H)),
        w.Λ = ((compactSupportSystemLevel l E₀) n : Type (u + 1)) ∧
          HEq w.φ (RingHom.id ((compactSupportSystemLevel l E₀) n)) := by
    have : Finite (Padic.coefficientExtensionRing l E₀ (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E₀ (n + 1) (Nat.succ_pos n)
    exact scalar_origin A (Padic.coefficientExtensionRing l E₀ (n + 1)) _
      (hH n).1 (hH n).2
  have evaluated (n : ℕ) : IsIso
      (((E (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) n T) ⋙
        StrictTower.ev ((compactSupportSystemLevel l E₀) n) T 0).map
          ((gamma (compactSupportSystemLevel l E₀)
            (compactSupportSystemQuotient l E₀) k r p i h).app H)) := by
    have := hfinite n
    obtain ⟨w, hw, hφ⟩ := origins n
    let V := StrictTower.ev ((compactSupportSystemLevel l E₀) n) T 0
    let a := StrictTower.finiteSource ((compactSupportSystemLevel l E₀) n) r i
      ((E (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) n A).obj H) 0 w ≪≫
      V.mapIso (evalSource (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) n r i H).symm
    let b := V.mapIso (evalTarget (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) n k p H)
    let d := (StrictTower.HD ((compactSupportSystemLevel l E₀) n) T w.Λ w.φ).mapIso
      ((StrictTower.finiteGamma w.Λ k r p i h).app w.origin.L) ≪≫
        StrictTower.finiteTarget ((compactSupportSystemLevel l E₀) n) k p
          ((E (compactSupportSystemLevel l E₀)
            (compactSupportSystemQuotient l E₀) n A).obj H) 0 w
    apply iso_square_isIso a b d _
    simpa only [a, b, d, V, Iso.app_hom, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, Functor.comp_map, Category.assoc] using
      gamma_finite (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) n k r p i h H w hw hφ
  have := system_isIso_of_evaluations (compactSupportSystemLevel l E₀)
    (compactSupportSystemQuotient l E₀) T
      ((gamma (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) k r p i h).app H) evaluated
  apply exists_iso_with_property ((gamma (compactSupportSystemLevel l E₀)
    (compactSupportSystemQuotient l E₀) k r p i h).app H)
  intro e he
  constructor
  · intro H' f e' he'
    exact inverse_natural_app (gamma (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) k r p i h) f e e' he he'
  · intro n
    refine ⟨origins n, ?_⟩
    intro w hw hφ
    have := hfinite n
    exact finite_iso_normalization_comp
      (E (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) n T)
      (StrictTower.ev ((compactSupportSystemLevel l E₀) n) T 0)
      (evalSource (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) n r i H)
      (evalTarget (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) n k p H) e
      (StrictTower.finiteSource ((compactSupportSystemLevel l E₀) n) r i
        ((E (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) n A).obj H) 0 w)
      (StrictTower.finiteTarget ((compactSupportSystemLevel l E₀) n) k p
        ((E (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) n A).obj H) 0 w)
      ((StrictTower.HD ((compactSupportSystemLevel l E₀) n) T w.Λ w.φ).mapIso
        ((StrictTower.finiteGamma w.Λ k r p i h).app w.origin.L))
      ((gamma (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) k r p i h).app H) he
      (gamma_finite (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) n k r p i h H w hw hφ)

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
