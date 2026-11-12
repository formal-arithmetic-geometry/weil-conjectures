/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
import WeilConjectures.AlgebraicGeometry.AbelianVariety.ImmersionResiduePointIso
import WeilConjectures.AlgebraicGeometry.AbelianVariety.IdentifiedBaseFibreIso
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedResidueNormalization
import WeilConjectures.AlgebraicGeometry.Structure.StructureDerivedImageCohomologyNaturality

/-! Geometric compatibility for fixed residue models.

Source: Stacks Project, Tags 01IB, 064K, 06YJ and 0B91.
(blueprint: new-picard-derived-fibre-residue-geometric-compatibility)

Proof: Normalize the derived coefficient arrows by proper-flat base change and the
common fibre trivialization. Apply the affine-base Leray comparison to the resulting
structure-module arrows. Compose these equivalences with the supplied affine residue
comparisons.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] picardDerivedCoefficientMap relativeMVUnit
  Modules.canonicalSinglePullbackMap structureSheafCohomologyPullback
  Modules.tensorPullback Modules.tensorPullbackObj

private theorem map_square_apply
    {D : Type*} [Category* D] {R : Type*} [Ring R] (H : D ⥤ ModuleCat R)
    {A B A' B' : D} (u : A ⟶ B) (a : A ⟶ A') (b : B ⟶ B') (t : A' ⟶ B')
    (h : u ≫ b = a ≫ t) (z : H.obj A) :
    H.map b (H.map u z) = H.map t (H.map a z) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, h,
    Functor.map_comp, ConcreteCategory.comp_apply]

private theorem transport_square_apply
    {D : Type*} [Category* D] {R : Type*} [Ring R] (H : D ⥤ ModuleCat R)
    {A B A' B' : D} (u : A ⟶ B) (a : A ≅ A') (b : B ≅ B') (t : A' ⟶ B')
    (h : u ≫ b.hom = a.hom ≫ t)
    {M N P Q : Type*} [Add M] [Add N] [Add P] [Add Q]
    (eK : M ≃+ H.obj A) (eC : N ≃+ H.obj B) (φ : M → N)
    (hφ : ∀ z, eC (φ z) = H.map u (eK z))
    (e : H.obj A' ≃+ P) (ei : H.obj B' ≃+ Q) (g : P → Q)
    (hg : ∀ z, ei (H.map t z) = g (e z)) (z : M) :
    (eC.trans ((H.mapIso b).toLinearEquiv.toAddEquiv.trans ei)) (φ z) =
      g ((eK.trans ((H.mapIso a).toLinearEquiv.toAddEquiv.trans e)) z) := by
  change ei (H.map b.hom (eC (φ z))) = g (e (H.map a.hom (eK z)))
  rw [hφ]
  exact (congrArg ei (map_square_apply H u a.hom b.hom t h (eK z))).trans (hg _)

private theorem residue_fibre_isomorphisms
    {X S W : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    (k : W ⟶ S) [IsImmersion k] (w : W) (s : S) (hw : k w = s) :
    ∃ (r : Spec (W.residueField w) ≅ Spec (S.residueField s))
      (_hr : W.fromSpecResidueField w ≫ k = r.hom ≫ S.fromSpecResidueField s)
      (e : pullback (pullback.snd f k) (W.fromSpecResidueField w) ≅
        pullback f (S.fromSpecResidueField s))
      (ei : ∀ i, pullback (pullback.snd (fi i) k) (W.fromSpecResidueField w) ≅
        pullback (fi i) (S.fromSpecResidueField s)),
      (e.hom ≫ pullback.fst f (S.fromSpecResidueField s) =
        pullback.fst (pullback.snd f k) (W.fromSpecResidueField w) ≫ pullback.fst f k) ∧
      (e.hom ≫ pullback.snd f (S.fromSpecResidueField s) ≫ r.inv =
        pullback.snd (pullback.snd f k) (W.fromSpecResidueField w)) ∧
      (∀ i, (ei i).hom ≫ pullback.fst (fi i) (S.fromSpecResidueField s) =
        pullback.fst (pullback.snd (fi i) k) (W.fromSpecResidueField w) ≫
          pullback.fst (fi i) k) ∧
      (∀ i, (ei i).hom ≫ pullback.snd (fi i) (S.fromSpecResidueField s) ≫ r.inv =
        pullback.snd (pullback.snd (fi i) k) (W.fromSpecResidueField w)) := by
  classical
  obtain ⟨r, hr⟩ := immersion_residuePointIso k w s hw
  obtain ⟨e, hef, hes⟩ := identifiedBaseFibreIso f k
    (W.fromSpecResidueField w) (S.fromSpecResidueField s) r hr
  have hFi := fun i ↦ identifiedBaseFibreIso (fi i) k
    (W.fromSpecResidueField w) (S.fromSpecResidueField s) r hr
  choose ei heif heis using hFi
  exact ⟨r, hr, e, ei, hef, hes, heif, heis⟩

set_option maxHeartbeats 600000 in
-- Comparing the derived and concrete homology functors needs extra elaboration heartbeats.

/-- Degree-one derived fibre cohomology of the coefficient direct images is identified with
structure-sheaf cohomology of the fibres, compatibly with the coefficient arrows.
Source: Stacks Project, Tags 0B91, 0BF2 and 01XK.
(blueprint: new-picard-derived-fibre-residue-geometric-compatibility)

Proof: Apply derived residue normalization, then the affine-base structure-module
cohomology naturality theorem. Evaluate the normalization equation on homology and
sections; composition of additive equivalences gives the desired square. -/
theorem picard_derived_fibre_residue_geometric_compatibility
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)]
    [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [Modules.IsInvertible L]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf) :
    ∃ (e : derivedFiberCohomology W
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) 1 w ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (ei : ∀ i, derivedFiberCohomology W
        ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
              ((Modules.tensorPullback (ui i)).obj L)))) 1 w ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1),
      ∀ i z, ei i ((derivedFiberCohomologyFunctor W w 1).map
          (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) z) =
        structureSheafCohomologyPullback
          (((Over.pullback (S.fromSpecResidueField s)).map
            (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
              (ui i) (hui i))).left) 1 (e z) := by
  classical
  obtain ⟨r, hr, eF, eFi, heFfst, heFsnd, heFifst, heFisnd⟩ :=
    residue_fibre_isomorphisms f Xi fi k w s hw
  obtain ⟨a, ai, hj, hnorm⟩ := picard_derived_residue_normalization
    f Xi fi ui hui L W k (W.fromSpecResidueField w) (S.fromSpecResidueField s) r hr
    eF heFfst heFsnd eFi heFifst heFisnd τ
  let q := pullback.snd f (S.fromSpecResidueField s) ≫ r.inv
  let qi := fun i ↦ pullback.snd (fi i) (S.fromSpecResidueField s) ≫ r.inv
  let j := fun i ↦ ((Over.pullback (S.fromSpecResidueField s)).map
    (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings (Spec (W.residueField w)).toRingedSpace)) 1 ⋙
    SheafOfModules.evaluation (moduleRings (Spec (W.residueField w)).toRingedSpace) (.op ⊤)
  let e := structureDerivedImageCohomologyEquiv q
  let ei := fun i ↦ structureDerivedImageCohomologyTargetEquiv q (j i) (hj i)
  let d := (H.mapIso a).toLinearEquiv.toAddEquiv
  let di := fun i ↦ (H.mapIso (ai i)).toLinearEquiv.toAddEquiv
  refine ⟨d.trans e, fun i ↦ (di i).trans (ei i), ?_⟩
  intro i
  exact transport_square_apply H _ a (ai i) _ (hnorm i) (AddEquiv.refl _) (AddEquiv.refl _)
    ((derivedFiberCohomologyFunctor W w 1).map
      (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k)) (fun _ ↦ rfl) e (ei i)
    (structureSheafCohomologyPullback (j i) 1)
    (structure_derived_image_cohomology_naturality q (j i) (hj i))

end AlgebraicGeometry.Scheme
