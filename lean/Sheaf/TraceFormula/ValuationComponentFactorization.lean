/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.Modification
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.IsSepClosed

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Jacobson.Ring
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.TraceFormula.ProperCurveImagePositiveFibreComponent

/-! # Factorization of curve modifications detected on contracted components

Source: Temkin, *Stable modification of relative curves*, Proposition 4.2.3,
printed page 27, in the common-model form of the DAG
(blueprint: lem-trf-valuation-component-factorization).

The statement reuses `EtaModification` and `Scheme.IsPureDimension`. Eta-normality
and the contracted-component implication are written out, without new predicates.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The common-model component criterion for factorization of relative curves.
Source: Temkin, Proposition 4.2.3, printed p. 27, and the eta-normality definition
of Proposition 3.5.2 (blueprint: lem-trf-valuation-component-factorization).

Proof plan, following the ten steps of the DAG's agent reconstruction:
1. Finite height makes the generic point of Spec V a principal open D(t). Flatness
   gives injectivity of multiplication by t on sections by
   `lem-sc-flat-invertible-sections-torsion-free`, hence schematic generic density.
2. In P = X ×_C Y take the scheme-theoretic closure Gamma of its generic graph,
   using `def-nagata-scheme-theoretic-closure` and
   `lemma-nagata-scheme-theoretic-closure-minimal`. Affine-locally its ideal is
   ker(A → A[1/t]); its generic fibre is the graph and is schematically dense.
3. The compatible map (a,b) from W factors through Gamma: its pulled-back ideal
   vanishes generically, hence vanishes by step 1. Denote this factor by r.
4. The projection p : Gamma → Y is proper by
   `lem-weil-pbc-proper-fp-permanence` and `def-weil-proper-morphism`.
   Its composite to S is finite type, so its fibres are finite type over residue fields.
5. The factor r is proper by `lem-weil-pbc-proper-to-separated`. Its closed image
   contains the schematically dense generic graph, hence r is surjective.
6. Proper base change and `lem-weil-pbc-surjective-base-change` apply on every fibre.
   If a fibre of p has positive dimension, use
   `lem-trf-proper-curve-image-positive-fibre-component` to find a component of W_s
   contracted by b_s whose image in Gamma_s has dimension one. It is also contracted
   by a_s, and both image points are closed by properness.
7. By `lem-weil-pbc-zariski-lemma` and `lem-trf-closed-point-residue-immersion`,
   these image points have finite residue fields over the base residue field and
   define closed subschemes. Their fibre product has finite-dimensional coordinate
   algebra and dimension zero, contradicting the one-dimensional graph image.
8. Thus all fibres of p have dimension at most zero. Apply
   `lem-trf-locally-quasi-finite-relative-dimension-zero` and
   `pqf-lem-proper-lqf-finite`: p is finite. Its generic isomorphism and the schematic
   density from steps 1--2 make it a finite eta-modification.
9. Eta-normality of Y makes p invertible. Compose its inverse with Gamma → X to
   obtain h; the graph equations give b ≫ h = a and h ≫ f = g.
10. Any two such C-morphisms agree generically since b is a generic isomorphism.
    Properness of f makes their equalizer closed; schematic generic density of Y
    makes its ideal zero. This proves uniqueness. -/
theorem valuation_component_factorization
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)]
    (C X Y W : Scheme.{u})
    (cC : C ⟶ Spec (CommRingCat.of V))
    (cX : X ⟶ Spec (CommRingCat.of V))
    (cY : Y ⟶ Spec (CommRingCat.of V))
    (cW : W ⟶ Spec (CommRingCat.of V))
    (hC : Flat cC ∧ LocallyOfFinitePresentation cC ∧ QuasiCompact cC ∧
      QuasiSeparated cC ∧ IsReduced C ∧ ∀ s : Spec (CommRingCat.of V),
        (cC.fiber s).IsPureDimension 1)
    (hX : Flat cX ∧ LocallyOfFinitePresentation cX ∧ QuasiCompact cX ∧
      QuasiSeparated cX ∧ IsReduced X ∧ ∀ s : Spec (CommRingCat.of V),
        (cX.fiber s).IsPureDimension 1)
    (hY : Flat cY ∧ LocallyOfFinitePresentation cY ∧ QuasiCompact cY ∧
      QuasiSeparated cY ∧ IsReduced Y ∧ ∀ s : Spec (CommRingCat.of V),
        (cY.fiber s).IsPureDimension 1)
    (hW : Flat cW ∧ LocallyOfFinitePresentation cW ∧ QuasiCompact cW ∧
      QuasiSeparated cW ∧ IsReduced W ∧ ∀ s : Spec (CommRingCat.of V),
        (cW.fiber s).IsPureDimension 1)
    (hCη : Smooth (pullback.snd cC (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (hXη : Smooth (pullback.snd cX (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (hYη : Smooth (pullback.snd cY (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (hWη : Smooth (pullback.snd cW (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (f : X ⟶ C) (g : Y ⟶ C) (a : W ⟶ X) (b : W ⟶ Y)
    (hfc : f ≫ cC = cX) (hgc : g ≫ cC = cY)
    (hac : a ≫ cX = cW) (hbc : b ≫ cY = cW)
    (hfa : a ≫ f = b ≫ g)
    (hf : EtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) f cC)
    (hg : EtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) g cC)
    (ha : EtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) a cX)
    (hb : EtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) b cY)
    (hYn : ∀ (Z : Scheme.{u}) (p : Z ⟶ Y), IsFinite p →
      EtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) p cY → IsIso p)
    (hcontract : ∀ (s : Spec (CommRingCat.of V)) (Z : Set (cW.fiber s)),
      Z ∈ irreducibleComponents (cW.fiber s) →
      Set.Subsingleton ((fun w : cW.fiber s ↦ b (cW.fiberι s w)) '' Z) →
      Set.Subsingleton ((fun w : cW.fiber s ↦ a (cW.fiberι s w)) '' Z)) :
    ∃! h : Y ⟶ X, b ≫ h = a ∧ h ≫ f = g := by
  sorry

end AlgebraicGeometry
