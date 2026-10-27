/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.TraceFormula.ElementaryModuleDevissage
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent
import Sheaf.AlgebraicGeometry.FinitePushforwardModuleFinitePresentation
import Sheaf.TraceFormula.EtaleModuleFinitePresentationLocal

/-! # Finite presentation across elementary module dévissage

Source: Stacks Project, flat.tex, Tag 057T, lemma-devissage-finite-presentation
(blueprint: lem-trf-elementary-devissage-finite-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Stalk finite presentation ascends and descends along a flat scheme morphism.
Source: Stacks Project, Tag 057T, stalkwise proof, and Tag 0098.
Identify the pullback stalk with extension of scalars. A flat local ring map is
faithfully flat; tensor base change preserves finite presentation and faithfully
flat descent reflects it. -/
private theorem finitePresentation_stalk_iff_flat_pullback
    {T U : Scheme.{u}} (p : T ⟶ U) [Flat p] (t : T) (M : U.Modules) :
    Module.FinitePresentation (U.presheaf.stalk (p t))
        ((RingedSpace.moduleStalkFunctor U.toRingedSpace (p t)).obj M) ↔
      Module.FinitePresentation (T.presheaf.stalk t)
        ((RingedSpace.moduleStalkFunctor T.toRingedSpace t).obj
          ((tensorPullback p).obj M)) := by
  algebraize [(p.stalkMap t).hom]
  have : Module.FaithfullyFlat (U.presheaf.stalk (p t)) (T.presheaf.stalk t) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap p t) (p.toLRSHom.prop t)
  obtain ⟨e, _⟩ := exists_tensorPullback_stalk_iso p t
  have he := (e.app M).toLinearEquiv.finitePresentation_iff
  constructor
  · intro hM
    have := hM
    apply he.mpr
    change Module.FinitePresentation (T.presheaf.stalk t)
      (TensorProduct (U.presheaf.stalk (p t)) (T.presheaf.stalk t)
        ((RingedSpace.moduleStalkFunctor U.toRingedSpace (p t)).obj M))
    infer_instance
  · intro hM
    have : Module.FinitePresentation (T.presheaf.stalk t)
        (TensorProduct (U.presheaf.stalk (p t)) (T.presheaf.stalk t)
          ((RingedSpace.moduleStalkFunctor U.toRingedSpace (p t)).obj M)) := he.mp hM
    exact Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
      (B := T.presheaf.stalk t)

/-- In elementary étale module dévissage, finite presentation of the structural morphism
makes the finite map finitely presented. Finite presentation near the three marked points
is equivalent, as is finite presentation of the three stalks (a separate equivalence).

Source: Stacks Project, flat.tex, Tag 057T, lemma-devissage-finite-presentation
(blueprint: lem-trf-elementary-devissage-finite-presentation).

Proof:
1. Use g ≫ f = f' ≫ e and finite-presentation cancellation to obtain local finite
   presentation of f'. Use i ≫ f' = π ≫ h and cancellation along the smooth map h
   to obtain local finite presentation of π. Finiteness gives quasi-compactness
   and quasi-separatedness.
2. The closed immersion i has singleton fibres by injectivity. Apply the existing
   finite-pushforward comparison to i and to π, obtaining both neighbourhood and
   stalk comparisons in each case
   (lem-trf-finite-pushforward-module-finite-presentation).
3. Apply the étale-local neighbourhood comparison to g and F. Restrict the given
   isomorphism i_*G ≅ g^*F to every open neighbourhood of x', and transport finite
   presentation across these isomorphisms. Compose with the i-comparison from
   step 2 to compare F near x with G near z'. The π-comparison gives the next
   neighbourhood equivalence (lem-trf-etale-module-finite-presentation-local).
4. The proved private flat-pullback helper identifies the pullback stalk with
   extension of scalars along the faithfully flat local ring map. Tensor base
   change preserves finite presentation, and faithfully flat descent reflects it
   (lem-weil-pbc-module-stalk-pullback and
   lem-trf-finite-presentation-module-descent-flat-local).
5. Apply this helper to g, transport stalk finite presentation through the given
   sheaf isomorphism, and compose with the i-stalk comparison from step 2.
   The π-stalk comparison supplies the last equivalence. -/
theorem elementary_devissage_finite_presentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (_hF : F.IsQuasiCoherentFiniteType) (x : X)
    (hx : ¬ Subsingleton
      (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk (f.asFiber x)))
    (n : ℕ)
    (_hn : topologicalKrullDimAt
      (⟨f.asFiber x, hx⟩ :
        {q : f.fiber (f x) |
          ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk q)}) =
      (n : WithBot ℕ∞))
    (X' Z' Y' S' : Scheme.{u})
    (g : X' ⟶ X) (e : S' ⟶ S) (f' : X' ⟶ S')
    (i : Z' ⟶ X') (π : Z' ⟶ Y') (h : Y' ⟶ S')
    (x' : X') (s' : S') (z' : Z') (G : Z'.Modules)
    [Etale g] [Etale e] (_hg : g x' = x) (_he : e s' = f x)
    [IsIso (g.residueFieldMap x')] [IsIso (e.residueFieldMap s')]
    (_hfg : g ≫ f = f' ≫ e) (_hπ : i ≫ f' = π ≫ h)
    [IsAffine X'] [IsAffine Z'] [IsAffine Y'] [IsAffine S']
    [IsClosedImmersion i] [LocallyOfFinitePresentation i] [QuasiCompact i] [QuasiSeparated i]
    [IsFinite π] (_hG : G.IsQuasiCoherentFiniteType)
    (_hiso : Nonempty ((pushforward i).obj G ≅ (tensorPullback g).obj F))
    [SmoothOfRelativeDimension n h] [GeometricallyIntegral h]
    (_hi : i z' = x') (_hs : h (π z') = s')
    (_hfibre : (π ⁻¹' ({π z'} : Set Y')) = {z'})
    (_hpure : @Algebra.IsPurelyTranscendentalExtension
      (S'.residueField (h (π z'))) (Y'.residueField (π z'))
      inferInstance inferInstance (h.residueFieldMap (π z')).hom.toAlgebra)
    [LocallyOfFinitePresentation f] :
    (LocallyOfFinitePresentation π ∧ QuasiCompact π ∧ QuasiSeparated π) ∧
    ((∃ U : X.Opens, x ∈ U ∧ (F.over U).IsFinitePresentation) ↔
      (∃ U : Z'.Opens, z' ∈ U ∧ (G.over U).IsFinitePresentation)) ∧
    ((∃ U : Z'.Opens, z' ∈ U ∧ (G.over U).IsFinitePresentation) ↔
      (∃ U : Y'.Opens, π z' ∈ U ∧ ((pushforward π).obj G |>.over U).IsFinitePresentation)) ∧
    (Module.FinitePresentation (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) ↔
      Module.FinitePresentation (Z'.presheaf.stalk z')
        ((RingedSpace.moduleStalkFunctor Z'.toRingedSpace z').obj G)) ∧
    (Module.FinitePresentation (Z'.presheaf.stalk z')
        ((RingedSpace.moduleStalkFunctor Z'.toRingedSpace z').obj G) ↔
      Module.FinitePresentation (Y'.presheaf.stalk (π z'))
        ((RingedSpace.moduleStalkFunctor Y'.toRingedSpace (π z')).obj
          ((pushforward π).obj G))) := by
  have : F.IsQuasicoherent := _hF.1
  have : G.IsQuasicoherent := _hG.1
  have := SmoothOfRelativeDimension.smooth n h
  have : LocallyOfFinitePresentation (f' ≫ e) := by
    rw [← _hfg]
    infer_instance
  have : LocallyOfFinitePresentation f' := locallyOfFinitePresentation_of_comp f' e
  have : LocallyOfFinitePresentation (π ≫ h) := by
    rw [← _hπ]
    infer_instance
  have : LocallyOfFinitePresentation π := locallyOfFinitePresentation_of_comp π h
  have hifibre : i ⁻¹' ({i z'} : Set X') = ({z'} : Set Z') := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact i.isEmbedding.injective.eq_iff
  have hiFP := finitePresentation_near_and_stalk_iff_pushforward_of_singleton_fibre
    i z' hifibre G
  have hpFP := finitePresentation_near_and_stalk_iff_pushforward_of_singleton_fibre
    π z' _hfibre G
  obtain ⟨a⟩ := _hiso
  have hnear :
      (∃ U : X'.Opens, x' ∈ U ∧
        (((pushforward i).obj G).over U).IsFinitePresentation) ↔
      (∃ U : X'.Opens, x' ∈ U ∧
        (((tensorPullback g).obj F).over U).IsFinitePresentation) := by
    constructor
    · rintro ⟨U, hxU, hU⟩
      exact ⟨U, hxU, (SheafOfModules.isFinitePresentation (X'.ringCatSheaf.over U)).prop_of_iso
        ((SheafOfModules.overFunctor X'.ringCatSheaf U).mapIso a) hU⟩
    · rintro ⟨U, hxU, hU⟩
      exact ⟨U, hxU, (SheafOfModules.isFinitePresentation (X'.ringCatSheaf.over U)).prop_of_iso
        ((SheafOfModules.overFunctor X'.ringCatSheaf U).mapIso a.symm) hU⟩
  have hstalk := ((RingedSpace.moduleStalkFunctor X'.toRingedSpace x').mapIso a).toLinearEquiv
      |>.finitePresentation_iff
  have hetale := finitePresentation_stalk_iff_flat_pullback g x' F
  rw [_hg] at hetale
  rw [_hi] at hiFP
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    (etale_module_finite_presentation_local g x x' _hg F).trans
      (hnear.symm.trans hiFP.1.symm), hpFP.1,
    hetale.trans (hstalk.symm.trans hiFP.2.symm), hpFP.2⟩

end AlgebraicGeometry.Scheme.Modules
