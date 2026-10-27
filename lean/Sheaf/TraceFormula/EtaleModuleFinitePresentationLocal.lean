/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Descent

/-!
# Étale-local finite presentation of a module

Source: Stacks Project, flat.tex, Tag 057T, proof of (1) iff (4)
(blueprint: lem-trf-etale-module-finite-presentation-local).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_overEquiv {X : Scheme.{u}} (U : X.Opens)
    (N : SheafOfModules.{u} (X.ringCatSheaf.over U)) [N.IsFinitePresentation] :
    ((overEquiv U).functor.obj N).IsFinitePresentation := by
  have := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  have (V : _) : (Over.post (X := V) U.overEquivalence.inverse).IsContinuous
      ((Opens.grothendieckTopology U.carrier).over V)
      (((Opens.grothendieckTopology X).over U).over _) := by
    exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.inverse _ _).overPost V)
  exact @SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) _ _ (fun V ↦ this V) _ _ N _

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (N : U.toScheme.Modules) [N.IsFinitePresentation] :
    ((overEquiv U).inverse.obj N).IsFinitePresentation := by
  have := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  have (V : _) : (Over.post (X := V) U.overEquivalence.functor).IsContinuous
      (((Opens.grothendieckTopology X).over U).over V)
      ((Opens.grothendieckTopology U.carrier).over _) := by
    exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.functor _ _).overPost V)
  exact @SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _ _ (fun V ↦ this V) _ _ N _

private theorem finitePresentation_over_iff {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) : (M.over U).IsFinitePresentation ↔ (M.restrict U.ι).IsFinitePresentation := by
  constructor
  · intro h
    have : SheafOfModules.IsFinitePresentation.{u}
        ((SheafOfModules.overFunctor X.ringCatSheaf U ⋙ (overEquiv U).functor).obj M) :=
      finitePresentation_overEquiv U (M.over U)
    exact isFinitePresentation_of_iso ((overFunctorEquiv U).app M)
  · intro h
    have := finitePresentation_overEquiv_inverse U (M.restrict U.ι)
    exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso
      ((overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
        ((overEquiv U).unitIso.app (M.over U)).symm) inferInstance

/-- Finite presentation of a quasi-coherent module is local at an étale neighbourhood.

Source: Stacks Project, flat.tex, Tag 057T, proof of (1) iff (4)
(blueprint: lem-trf-etale-module-finite-presentation-local).

Proof: Identify tensor pullback with ordinary scheme-module pullback by uniqueness
of left adjoints to pushforward. The opens/over-site equivalence identifies finite
presentation of `M.over U` with that of `M.restrict U.ι`. For the forward direction,
pull back the restriction to `U` along the restricted map from `g ⁻¹ᵁ U`; ordinary
pullback preserves finite presentation. The pullback composition isomorphisms identify
this with the restriction of `g^* M`. For the reverse direction, let `V` be the given
neighbourhood of `x'` and put `U = g(V)`. Étale openness makes `U` open, and the
restricted map `q : V ⟶ U` is surjective and étale. Its singleton family is an fppf
covering and therefore an fpqc covering by Mathlib's topology inclusion. Apply the
finite-presentation clause of `lem-pc-fpqc-descent` to the canonical descent datum of
`M.restrict U.ι`: its only component is isomorphic to `(g^* M).restrict V.ι`.
Finally `g x' = x` gives membership in the chosen neighbourhoods. The residue-field
isomorphism hypothesis is retained but unused.
-/
theorem etale_module_finite_presentation_local
    {X X' : Scheme.{u}} (g : X' ⟶ X) (x : X) (x' : X')
    (_hx : g x' = x) [Etale g] [IsIso (g.residueFieldMap x')]
    (M : X.Modules) [M.IsQuasicoherent] :
    (∃ U : X.Opens, x ∈ U ∧ (M.over U).IsFinitePresentation) ↔
      (∃ U' : X'.Opens, x' ∈ U' ∧
        ((tensorPullback g).obj M |>.over U').IsFinitePresentation) := by
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction g
  let e := adj.leftAdjointUniq (pullbackPushforwardAdjunction g)
  have comparison (U : X.Opens) (V : X'.Opens) (h : V ≤ g ⁻¹ᵁ U) :
      (pullback (g.resLE U V h)).obj (M.restrict U.ι) ≅
        ((tensorPullback g).obj M).restrict V.ι :=
    (pullback (g.resLE U V h)).mapIso ((restrictFunctorIsoPullback U.ι).app M) ≪≫
      pullbackCompOfEq _ _ _ (g.resLE_comp_ι h) M ≪≫
      ((pullbackComp V.ι g).app M).symm ≪≫
      (pullback V.ι).mapIso (e.app M).symm ≪≫
      ((restrictFunctorIsoPullback V.ι).app _).symm
  constructor
  · rintro ⟨U, hxU, hU⟩
    have : (M.restrict U.ι).IsFinitePresentation := (finitePresentation_over_iff M U).1 hU
    refine ⟨g ⁻¹ᵁ U, ?_, (finitePresentation_over_iff _ _).2 ?_⟩
    · change g x' ∈ U
      rwa [_hx]
    · exact isFinitePresentation_of_iso (comparison U (g ⁻¹ᵁ U) le_rfl)
  · rintro ⟨V, hxV, hV⟩
    let U : X.Opens := ⟨g '' (V : Set X'), g.isOpenMap _ V.isOpen⟩
    have h : V ≤ g ⁻¹ᵁ U := fun y hy ↦ ⟨y, hy, rfl⟩
    let q : V.toScheme ⟶ U.toScheme := g.resLE U V h
    have hq : q ≫ U.ι = V.ι ≫ g := g.resLE_comp_ι h
    have : Surjective q := ⟨by
      intro y
      obtain ⟨z, hz, hzy⟩ := y.2
      refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
      exact (congrArg (fun f : V.toScheme ⟶ X ↦ f ⟨z, hz⟩) hq).trans hzy⟩
    have : Etale q := by dsimp [q]; infer_instance
    have : (((tensorPullback g).obj M).restrict V.ι).IsFinitePresentation :=
      (finitePresentation_over_iff _ _).1 hV
    have : ((pullback q).obj (M.restrict U.ι)).IsFinitePresentation :=
      isFinitePresentation_of_iso (comparison U V h).symm
    let f : PUnit.{1} → Scheme.{u} := fun _ ↦ V.toScheme
    let p : ∀ i, f i ⟶ U.toScheme := fun _ ↦ q
    have hp : Sieve.ofArrows f p ∈ Scheme.fpqcTopology U.toScheme := by
      apply Scheme.fppfTopology_le_fpqcTopology
      simpa only [Sieve.ofArrows, f, p, Presieve.ofArrows_pUnit] using
        Precoverage.generate_mem_toGrothendieck q.singleton_mem_fppfPrecoverage
    have hfin : (M.restrict U.ι).IsFinitePresentation :=
      isFinitePresentation_of_toDescentData_iso p hp
        ((modulesPseudofunctor.toDescentData p).obj (M.restrict U.ι))
        (M.restrict U.ι) ⟨Iso.refl _⟩ (fun _ ↦ by
          change ((pullback q).obj (M.restrict U.ι)).IsFinitePresentation
          infer_instance)
    refine ⟨U, ?_, (finitePresentation_over_iff M U).2 hfin⟩
    exact ⟨x', hxV, _hx⟩

end AlgebraicGeometry.Scheme.Modules
