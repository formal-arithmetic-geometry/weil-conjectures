/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction
import Sheaf.Paper.UniversalTranslationMultiplier
import Sheaf.AlgebraicGeometry.AffineConstantSectionZeroDetection

/-!
# Translation invariance of the affine-space trace

Source: main-20261015, sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md, Step 1
(blueprint: lem-trf-ambient-affine-translation-trace).

We use the recorded coordinate-tower presentation of affine space and of its
shifted Tate complex. All action maps are constructed from the existing
proper/open exchange and the normalized roots-of-unity pullback comparisons.
No trace, exchange, or coefficient identification is an arbitrary parameter.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] ModuleCat.extendScalars
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem multiplier_one (A : Type (u + 1)) [CommRing A] (B : Scheme.{u})
    (h : ordinaryFiniteConstant A B ⟶ ordinaryFiniteConstant A B)
    (hh : IsEtaleUnitMultiplier A B (LocallyConstant.const B 1) h) : h = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (ordinaryFiniteConstant A B).property
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change h.hom.app U
      ((toSheafify B.smallEtaleTopology
        ((Functor.const B.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U c) =
    (toSheafify B.smallEtaleTopology
      ((Functor.const B.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U c
  simpa only [Units.val_one, one_mul] using hh U.unop 1 (fun _ ↦ rfl) c

private theorem tower_iso_coord (S : Scheme.{u}) (d : ℕ) (j : Fin d) :
    (affineTraceAffineSpaceIso S d).inv.appTop (affineTraceCoordinate S d j) =
      AffineSpace.coord S (ULift.up j) := by
  have h := congrArg (fun f ↦ f.appTop (AffineSpace.coord S (ULift.up j)))
    (affineTraceAffineSpaceIso S d).inv_hom_id
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
    AffineSpace.homOfVector_appTop_coord, Scheme.Hom.id_appTop, ConcreteCategory.id_apply] using h

/-- Translation preserves the actual coordinate-tower counit trace.
Source: main-20261015, sk-prop-sp-orientation-vector-bundle.proof.md, Step 1
(blueprint: lem-trf-ambient-affine-translation-trace).
Proof:
1. Form the universal translation over P = affine d-space over S. The coordinate
   tower gives Noetherian stages and preserves invertibility of N. Nagata and
   finite-type Noetherianity give the allowed compactifications.
2. Apply the compact-support action/base-change lemma and the unbounded comparison
   normalization to the shifted Tate sheaf. The trace dependency gives the actual
   counit isomorphism and its base-change equation; Tate transport composes.
3. Conjugate this action by the trace. Degree-zero full faithfulness identifies
   the resulting endomorphism of the constant complex with a module-sheaf map.
   Linearity makes it multiplication by a section b. Its inverse makes b a unit,
   including for A = 0. The constant-sheaf lemma makes b locally constant.
4. Every residue-field affine fibre is a nonempty integral spectrum, hence
   connected, including in rank zero. The identity normalization makes b = 1
   along the zero section. Thus it is one on every fibre and on all of P.
5. Specialize along a. The action and trace base-change equations identify the
   specialization with the displayed concrete exchange and Tate map. Cancel the
   base-change isomorphism to obtain the equality of actual derived morphisms.
   Rank zero uses only identity comparisons; the empty base is also included.
-/
theorem ambientAffineTranslationTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (a : Fin d → Γ(S, ⊤)) :
    ambientAffineTranslationExchange A S d a
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
      (affineTraceLeft A S d).map
        (ambientAffineTranslationTate A N hA (ambientAffineTraceTransport N hN A hA)
          S hS d a).hom ≫
      affineTraceCounit A N hA (ambientAffineTraceTransport N hN A hA)
        (ambientAffineTraceDatum N hN A hA) S hS d =
      affineTraceCounit A N hA (ambientAffineTraceTransport N hN A hA)
        (ambientAffineTraceDatum N hN A hA) S hS d := by
  obtain ⟨b, _, _, hbase, hzero, _⟩ :=
    purUniversalTranslationMultiplier N hN A hA S hS d
  have hb (x : affineTraceTower S d) : b x = 1 := by
    let i := affineTraceAffineSpaceIso S d
    let c : LocallyConstant (AffineSpace (ULift.{u} (Fin d)) S) A :=
      LocallyConstant.map (fun z : Aˣ ↦ (z : A)) (b.comap ⟨i.inv, i.inv.continuous⟩)
    have hz (s : S) : c ((AffineSpace.zeroSection (ULift.{u} (Fin d)) S) s) = 1 :=
      congrArg (fun z : Aˣ ↦ (z : A)) (hzero s)
    apply Units.ext
    calc
      (b x : A) = c (i.hom x) := by
        change (b x : A) = (b (i.inv (i.hom x)) : A)
        rw [← Scheme.Hom.comp_apply, i.hom_inv_id]
        rfl
      _ = c ((AffineSpace.zeroSection (ULift.{u} (Fin d)) S)
          ((AffineSpace (ULift.{u} (Fin d)) S ↘ S) (i.hom x))) :=
        (affine_constant_section_zero_detection S d A).2.1 c (i.hom x)
      _ = 1 := hz _
  let v : S ⟶ affineTraceTower S d :=
    AffineSpace.homOfVector (𝟙 S) (fun i : ULift.{u} (Fin d) ↦ a i.down) ≫
      (affineTraceAffineSpaceIso S d).inv
  have hv : (fun i ↦ v.appTop (affineTraceCoordinate S d i)) = a := by
    funext i
    simp only [v, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, tower_iso_coord,
      AffineSpace.homOfVector_appTop_coord]
  obtain ⟨wT, _, _, _, _⟩ := hbase S inferInstance v
  have hs : IsEtaleUnitMultiplier A S (LocallyConstant.const S 1) wT.scalar := by
    have he : b.comap ⟨v, v.continuous⟩ = LocallyConstant.const S 1 :=
      LocallyConstant.ext (fun x ↦ hb (v x))
    rw [← he]
    exact wT.scalar_spec
  have hc := wT.conjugate
  rw [multiplier_one A S wT.scalar hs, CategoryTheory.Functor.map_id] at hc
  have ht : wT.action ≫ wT.trace.hom = wT.trace.hom := by
    apply (cancel_epi wT.trace.inv).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc
  rw [wT.action_eq, wT.trace_hom] at ht
  rw [← hv]
  simpa only [Category.assoc] using ht

end AlgebraicGeometry.Etale
