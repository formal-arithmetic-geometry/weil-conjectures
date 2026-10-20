/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Sheaf.Paper.DerivedHomMayerVietoris

/-! # Geometric naturality after passing to residue homology

Source: Stacks Project, Tags 0B91, 0BF2 and 01XK.
(blueprint: lem-sc-picard-residue-homology-geometric-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The target residue homology groups agree with their structure-sheaf fibre cohomology.
Source: Stacks Project, Tags 0B91, 0BF2, 01XK, 0097 and 010V.
(blueprint: new-picard-residue-homology-comparison-targets)

Proof: Fix i and write Li = ui(i)^* L. Pullback preserves invertibility, hence
Li is finitely presented and flat relative to the base because fi(i) is flat.
The retractions supplied by hC(i) make the section complex on the affine U a
bounded finite projective complex, so it is K-flat. Its termwise residue tensor
has degree-one homology equal to the explicit cycle/boundary quotient for C(i).
The equation hp identifies the residue field of p with that at w, and the
immersion k and hw identify this field with the residue field at s. Transport
along hCi(i) and apply arbitrary derived base change for the proper finitely
presented fi(i). Affine-base cohomology then identifies this homology with
H^1(Xi(i)_s, Li_s). The equality hui(i) induces the fibre map Xi(i)_s -> X_s.
Composition of tensor pullbacks identifies Li_s with the pullback of L_s
along that map; pulling back tau and using that pullback preserves the structure
sheaf gives Li_s isomorphic to the structure sheaf of Xi(i)_s. This yields the
required additive equivalence for each i. Choice assembles these equivalences
as a family; for n=0 the family is the unique function from the empty type.
No model or coefficient is defined by choosing a witness of mere existence. -/
theorem picard_residue_homology_geometric_comparison_targets
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    Nonempty (∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1) := by
  classical
  have he (i : Fin n) : Nonempty (affineResidueCycleHomology W U p (C i) ≃+
      Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1) := by
    let q := S.fromSpecResidueField s
    let r : pullback (fi i) q ⟶ pullback f q :=
      pullback.lift (pullback.fst (fi i) q ≫ ui i) (pullback.snd (fi i) q) (by
        rw [Category.assoc, hui i, pullback.condition])
    have hr : r ≫ pullback.fst f q = pullback.fst (fi i) q ≫ ui i := by
      simp [r]
    obtain ⟨a⟩ := Modules.nonempty_tensorPullbackComp (pullback.fst (fi i) q) (ui i)
    obtain ⟨b⟩ := Modules.nonempty_tensorPullbackComp r (pullback.fst f q)
    have : IsIso (Modules.tensorPullbackObjUnitToUnit r) :=
      (Modules.tensorPullbackObjUnitToUnit_isIso r).1
    let τi : (Modules.tensorPullback (pullback.fst (fi i) q)).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) q).ringCatSheaf :=
      (a.app L).symm ≪≫
        (eqToIso (congrArg (fun g ↦ (Modules.tensorPullback g).obj L) hr)).symm ≪≫
        b.app L ≪≫ (Modules.tensorPullback r).mapIso τ ≪≫
        asIso (Modules.tensorPullbackObjUnitToUnit r)
    have : ((Modules.tensorPullback (ui i)).obj L).IsInvertible :=
      ((Modules.invertible_pullback_tensor (ui i)).1 L).2
    exact picard_residue_homology_geometric_comparison_source (fi i)
      ((Modules.tensorPullback (ui i)).obj L) W k w s hw τi U hwU hU p hp
      (C i) (hC i) (hCi i)
  exact ⟨fun i ↦ (he i).some⟩

end Scheme

end AlgebraicGeometry
