/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus

import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.RingTheory.FiniteFreeMapResidueLocalization

/-! # Local lifting of arbitrary marked-fibre sections
Source: Stacks Project, Tag 0BF2, the degree-zero differential argument.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Every marked-fibre section lifts after shrinking the base around the marked point.
This asserts surjectivity of restriction, not existence of a generating section.
Source: Stacks Project, Tag 0BF2, the perfect-complex argument through d = 0.
(blueprint: lem-sc-picard-h1-base-descent-section-lifting)

Proof: Base change to W. The immersion identifies the marked residue fields, transporting
hLs and hH. Universal structure pushforward is preserved by this base change. Faithfully
flat descent makes the finite locally free modules in hLi invertible; trivialize them
on a common affine neighbourhood. Perfect direct-image base change and finite-free residue
models give bounded complexes with degree-zero term of rank one and all residue
differentials zero. The pullback maps can be represented by chain maps between these
finite projective complexes. Their degree-zero residue maps are isomorphisms. Shrink to
invert these maps. The joint degree-one map has injective residue map by hH; invert a
nonzero maximal minor to make it split injective. In rank zero it is already injective,
including the empty-family case. The target degree-zero differentials vanish since the
trivial descended bundles have H0 equal to O and its generator spans the degree-zero term
after shrinking. The chain-map equation forces the source differential to vanish.
Thus every fibre section lifts after further shrinking: write its scalar coefficient
in κ(w) as a fraction and invert its denominator, which is nonzero at w.
The residue fibre of V is canonically
isomorphic to the residue fibre of W; its inclusion j hits every point over w. Pullback
composition supplies e; the adjunction unit is the canonical section restriction map.
This proves the displayed restriction equation for every τ, without asserting that τ or
its lift generates. -/
theorem picard_h1_base_descent_section_lifting {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLi : ∀ i, ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        (Modules.tensorPullback (pullback.snd (fi i) k)).obj N))
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (hH : Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1 ↦ fun i ↦
      structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left) 1 x)) :
    ∀ τ : Γ((Modules.tensorPullback
      (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L, ⊤),
    ∃ (V : W.Opens) (hwV : w ∈ V),
      ∃ j : pullback f (W.fromSpecResidueField w ≫ k) ⟶ pullback f (V.ι ≫ k),
        (∀ x : (pullback f (V.ι ≫ k) : Scheme.{v}),
          (pullback.snd f (V.ι ≫ k)) x = (⟨w, hwV⟩ : V.toScheme) →
            ∃ y, j y = x) ∧
        ∃ e : (Modules.tensorPullback j).obj
          ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L) ≅
          (Modules.tensorPullback (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L,
            ∃ σ : Γ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L, ⊤),
              e.hom.app ⊤
                (((Modules.tensorPullback j).obj
                  ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).presheaf.map
                    (homOfLE j.preimage_top.ge).op
                      (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                        ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).val.app
                          (Opposite.op ⊤) σ)) = τ := by sorry

end AlgebraicGeometry.Scheme
