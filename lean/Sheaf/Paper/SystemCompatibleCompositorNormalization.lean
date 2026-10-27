/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.SystemCompatibleCompositorData
import Sheaf.Paper.SystemCompositorFiniteWordEvaluation
import all Sheaf.Paper.SystemProperOpenInvertibility
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Compatible-triangle normalization of the system compositor

Source: Stacks Project, Tag 0F7J, compatible triangle and four identifications
(blueprint: lem-pur-system-compatible-compositor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

variable (l : ℕ) [Fact l.Prime] (E₀ : Type u) [Field E₀]
  [Algebra (Padic l) E₀] [FiniteDimensional (Padic l) E₀]

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftAdjoint constantSheaf R J gamma compatibleCompositorWord
  compositorSupportTransport compositorFiniteSource compositorFiniteTarget
  compositorSupportEvaluation compositorLevelJ compositorLevelR
  coherenceEtaleCompositor StrictTower.HD

private theorem isIso_of_comparison
    {A : Type*} [Category A] {U V W : A} (a : U ≅ V) (f : V ⟶ W) (b : U ≅ W)
    (h : a.hom ≫ f = b.hom) : IsIso f := by
  have : IsIso (a.hom ≫ f) := h.symm ▸ b.isIso_hom
  exact IsIso.of_isIso_comp_left a.hom f

private theorem finite_word_isIso
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {X V XB Y YB Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian V] [IsNoetherian XB]
    [IsNoetherian Y] [IsNoetherian YB] [IsNoetherian Z]
    (j : X ⟶ V) (b : V ⟶ XB) (q : V ⟶ Y) (p : XB ⟶ YB)
    (i : Y ⟶ YB) (s : YB ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    [QuasiCompact j] [QuasiCompact b] [QuasiCompact i]
    [IsProper q] [IsProper p] [IsProper s]
    (sq : IsPullback b q p i) (h : b ≫ p = q ≫ i)
    (n : ℕ) [Finite (C n)] (M : Derived C τ X)
    (w : StrictTower.ScalarEtaleOrigin (C n) X ((compositorLevel C τ X n).obj M))
    (hC : w.Λ = (C n : Type (u + 1))) (hφ : HEq w.φ (RingHom.id (C n))) :
    IsIso ((compositorLevel C τ Z n).map
      ((compatibleCompositorWord C τ j b q p i s h).app M)) := by
  let a := compositorFiniteSource C τ j q i s n M w
  let d := (StrictTower.HD (C n) Z w.Λ w.φ).mapIso
    ((coherenceEtaleCompositor w.Λ
      (FiniteSiteTower.compactificationF j q)
      (FiniteSiteTower.compactificationG s i)
      (FiniteSiteTower.compactificationGF j b p s i q sq)).app w.origin.L) ≪≫
      compositorFiniteTarget C τ j b p s n M w
  apply isIso_of_comparison a _ d
  exact systemCompositorFiniteWordEvaluation C τ j b q p i s sq h n M w hC hφ

-- The original existential binder hqj is used implicitly in the finite normalization.
set_option linter.unusedVariables false in
/-- The geometric triangle and its actual system compositor, with the exact finite word.
Source: Stacks 0F7J, first paragraph, compatible diagram and four identifications
(blueprint: lem-pur-system-compatible-compositor-normalization).

Proof: (1) Finite-type schemes over the fixed field are Noetherian and qcqs. Apply
lem-weil-pbc-compatible-compactification-triangle to the prescribed compactification d,
obtaining V, XB, j, b, q, p and the cartesian square. Properness and composition give
separated finite-type ambient k-schemes.
(2) Compose the actual system mate gamma with sComp and jComp, in this order. These
are morphisms on the ringed sequence site and already commute with quotient transitions;
compatibleCompositorWord is exactly this construction, not a lift of finite arrows.
(3) For a levelwise bounded constructible M, exact open extension preserves each
level's own interval (lem-sf-open-finite-constructibility-interval). Apply
lem-pur-system-proper-open-invertibility to J_j M. The two compositors are isomorphisms,
so the word is invertible, without a common interval or any Tor condition.
(4) lem-sf-proetale-constructible-origin supplies the finite-level origin. Evaluation of
gamma is the normalized intrinsic finite mate by gamma_finite and
lem-cbc-finite-clopen-mate-site-transport. The open and proper factors evaluate to the
same normalized finite compositors, by lem-coef-semilinear-derived-sections.
(5) lem-sp-proper-open-coefficient-mate and lem-cbc-proper-open-interchange-coherence
identify that finite mate with the open-adjunct interchange on J_j M. Naturality
transports this identification through every chosen origin isomorphism.
(6) lem-sp-finite-site-tower-paste identifies the word with AE transported through the
canonical site comparisons. lem-sp-finite-compact-site-coherence and
lem-sf-class-compact-support-comparison identify it with the specified originComposition
of thm-sf-comp-composition in these compactifications, independently of witnesses.
(7) Identity-square normalization and normalized unital compositors give the identity
cases. Empty open extension is zero, so every factor is the unique map on zero objects.
These are equations of actual system words; evaluation is never used to detect equality.
-/
theorem systemCompatibleCompositorNormalization
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d : Compactification g) :
    ∃ (V XB : Scheme.{u}) (j : X ⟶ V) (b : V ⟶ XB) (q : V ⟶ Y) (p : XB ⟶ d.Z)
      (hj : IsOpenImmersion j) (hb : IsOpenImmersion b)
      (hqj : QuasiCompact j) (hqb : QuasiCompact b)
      (hpq : IsProper q) (hpp : IsProper p) (hi : QuasiCompact d.i)
      (sq : IsPullback b q p d.i),
      j ≫ q = f ∧
      j ≫ b ≫ (p ≫ d.g) = f ≫ g ∧
      ∀ (h : b ≫ p = q ≫ d.i)
        (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X),
        compatibleCompositorDomain l E₀ X M →
        IsIso ((@compatibleCompositorWord (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) X V XB Y d.Z Z j b q p d.i d.g
          hj hb d.isOpenImmersion hqb hi hpq hpp h).app M) ∧
        ∀ n : ℕ,
          ∃ w : StrictTower.ScalarEtaleOrigin (compactSupportSystemLevel l E₀ n) X
            ((compositorLevel (compactSupportSystemLevel l E₀)
              (compactSupportSystemQuotient l E₀) X n).obj M),
            w.Λ = (compactSupportSystemLevel l E₀ n : Type (u + 1)) ∧
            HEq w.φ (RingHom.id (compactSupportSystemLevel l E₀ n)) ∧
            (compositorFiniteSource (compactSupportSystemLevel l E₀)
              (compactSupportSystemQuotient l E₀) j q d.i d.g n M w).hom ≫
              (compositorLevel (compactSupportSystemLevel l E₀)
                (compactSupportSystemQuotient l E₀) Z n).map
                ((@compatibleCompositorWord (compactSupportSystemLevel l E₀)
                  (compactSupportSystemQuotient l E₀) X V XB Y d.Z Z j b q p d.i d.g
                  hj hb d.isOpenImmersion hqb hi hpq hpp h).app M) =
              (StrictTower.HD (compactSupportSystemLevel l E₀ n) Z w.Λ w.φ).map
                ((coherenceEtaleCompositor w.Λ
                  (FiniteSiteTower.compactificationF j q)
                  (FiniteSiteTower.compactificationG d.g d.i)
                  (FiniteSiteTower.compactificationGF j b p d.g d.i q sq)).hom.app
                    w.origin.L) ≫
                (compositorFiniteTarget (compactSupportSystemLevel l E₀)
                  (compactSupportSystemQuotient l E₀) j b p d.g n M w).hom := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of D.k))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated
    (Y ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (Z ↘ Spec (.of D.k))
  have : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k)) }
  have : IsNoetherian Y :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k)) }
  have : IsNoetherian Z :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of D.k)) }
  have triangle := exists_compatible_compactification_triangle (X := X) (Y := Y)
    (Z := Z) f g d
  obtain ⟨e, he, j, hj, hqj, hjb, hjq, hb, hqb, hq, sq, hproper, hcomp⟩ := triangle
  have hi : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  refine ⟨pullback e.g d.i, e.Z, j, pullback.fst e.g d.i,
    pullback.snd e.g d.i, e.g, hj, hb, hqj, hqb, hq, e.isProper, hi, sq,
    hjq, ?_, ?_⟩
  · rw [← Category.assoc, hjb]
    exact hcomp
  · intro h M hM
    have : CompactSpace (d.Z) :=
      QuasiCompact.compactSpace_of_compactSpace (d.g)
    have : IsNoetherian (d.Z) :=
      { __ := LocallyOfFiniteType.isLocallyNoetherian (d.g) }
    have : CompactSpace (e.Z) :=
      QuasiCompact.compactSpace_of_compactSpace (e.g)
    have : IsNoetherian (e.Z) :=
      { __ := LocallyOfFiniteType.isLocallyNoetherian (e.g) }
    have : CompactSpace (pullback e.g d.i : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd e.g d.i)
    have : IsNoetherian (pullback e.g d.i) :=
      { __ := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd e.g d.i) }
    have hfinite (n : ℕ) : Finite ((compactSupportSystemLevel l E₀) n) := by
      have := Padic.finite_coefficientExtensionRing l E₀ (n + 1) (Nat.succ_pos n)
      exact Finite.of_equiv (Padic.coefficientExtensionRing l E₀ (n + 1))
        Equiv.ulift.symm
    have origins (n : ℕ) :
        ∃ w : StrictTower.ScalarEtaleOrigin ((compactSupportSystemLevel l E₀) n) X
          ((compositorLevel (compactSupportSystemLevel l E₀)
            (compactSupportSystemQuotient l E₀) X n).obj M),
          w.Λ = ((compactSupportSystemLevel l E₀) n : Type (u + 1)) ∧
          HEq w.φ (RingHom.id ((compactSupportSystemLevel l E₀) n)) := by
      have := Padic.finite_coefficientExtensionRing l E₀ (n + 1) (Nat.succ_pos n)
      unfold compatibleCompositorDomain at hM
      have hn := hM n
      change _ ∧ _ at hn
      exact scalar_origin X (Padic.coefficientExtensionRing l E₀ (n + 1)) _
        hn.1 hn.2
    -- Keep coefficient expressions literal: local aliases make kernel conversion expensive.
    constructor
    · apply system_isIso_of_evaluations (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) Z
        ((compatibleCompositorWord (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) j (pullback.fst e.g d.i)
          (pullback.snd e.g d.i) e.g d.i d.g h).app M)
      intro n
      have := hfinite n
      obtain ⟨w, hw, hφ⟩ := origins n
      exact finite_word_isIso (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) j
        (pullback.fst e.g d.i) (pullback.snd e.g d.i) e.g d.i d.g sq h n M w
        hw hφ
    · intro n
      have := hfinite n
      exact Exists.imp (fun w hw ↦ ⟨hw.1, hw.2,
        systemCompositorFiniteWordEvaluation (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) j (pullback.fst e.g d.i)
          (pullback.snd e.g d.i) e.g d.i d.g sq h n M w hw.1 hw.2⟩) (origins n)

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
