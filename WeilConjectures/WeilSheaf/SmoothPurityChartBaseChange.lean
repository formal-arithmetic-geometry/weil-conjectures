/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityChartGeometry
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint

/-! # Geometric fibers of the smooth chart cover -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Geometric fiber as a functor on schemes over a field. -/
def purityGeometricFiber (k : Type u) [Field k] :
    Over (Spec (.of k)) ⥤ Over (Spec (.of (AlgebraicClosure k))) where
  obj X := Over.mk X.hom.geometricFiberToAlgebraicClosure
  map f := Over.homMk (Scheme.Hom.geometricFiberMap f.left (Over.w f))
    (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure f.left (Over.w f))
  map_id X := by
    ext1
    exact Scheme.Hom.geometricFiberMap_id
  map_comp f g := by
    ext1
    exact Scheme.Hom.geometricFiberMap_comp f.left g.left (Over.w f) (Over.w g)

variable {k : Type u} [Field k]

/-- Projection to the model over the original field. -/
def purityGeometricFiberProj (X : Over (Spec (.of k))) :
    ((purityGeometricFiber k).obj X).left ⟶ X.left := X.hom.geometricFiberProj

/-- Every morphism in the chart diagram has its canonical cartesian square. -/
lemma purityGeometricFiber_isPullback {X Y : Over (Spec (.of k))} (f : X ⟶ Y) :
    IsPullback (purityGeometricFiberProj X) ((purityGeometricFiber k).map f).left
      f.left (purityGeometricFiberProj Y) :=
  (Scheme.Hom.isPullback_geometricFiberMap f.left (Over.w f)).flip

instance (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType ((purityGeometricFiber k).obj X).hom :=
  inferInstanceAs (LocallyOfFiniteType X.hom.geometricFiberToAlgebraicClosure)

instance (X : Over (Spec (.of k))) [QuasiCompact X.hom] :
    QuasiCompact ((purityGeometricFiber k).obj X).hom :=
  inferInstanceAs (QuasiCompact X.hom.geometricFiberToAlgebraicClosure)

instance (X : Over (Spec (.of k))) [IsSeparated X.hom] :
    IsSeparated ((purityGeometricFiber k).obj X).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X.hom (Scheme.specAlgebraicClosure k).hom))

instance {X Y : Over (Spec (.of k))} (f : X ⟶ Y) [IsOpenImmersion f.left] :
    IsOpenImmersion ((purityGeometricFiber k).map f).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsOpenImmersion)
    f.left (Over.w f) inferInstance

instance {X Y : Over (Spec (.of k))} (f : X ⟶ Y) [Etale f.left] :
    Etale ((purityGeometricFiber k).map f).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Etale)
    f.left (Over.w f) inferInstance

instance {X Y : Over (Spec (.of k))} (f : X ⟶ Y) [IsProper f.left] :
    IsProper ((purityGeometricFiber k).map f).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
    f.left (Over.w f) inferInstance

/-- The field-extension map used by the chart argument is weakly étale. -/
lemma purity_weaklyEtale_specAlgebraicClosure [PerfectField k] :
    WeaklyEtale (Scheme.specAlgebraicClosure k).hom := by
  have : Algebra.IndEtale k (AlgebraicClosure k) :=
    Algebra.IndEtale.of_isSeparable k (AlgebraicClosure k)
  change WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
  infer_instance

instance [PerfectField k] (X : Over (Spec (.of k))) :
    WeaklyEtale (purityGeometricFiberProj X) := by
  have := purity_weaklyEtale_specAlgebraicClosure (k := k)
  change WeaklyEtale (pullback.fst X.hom (Scheme.specAlgebraicClosure k).hom)
  infer_instance

/-- A covering family on the model still covers after passage to geometric fibers. -/
lemma purityGeometricFiber_covers {ι : Type u} {X : Over (Spec (.of k))}
    {U : ι → Over (Spec (.of k))} (j : ∀ i, U i ⟶ X)
    (hj : ∀ x : X.left, ∃ (i : ι) (y : (U i).left), (j i).left y = x) :
    ∀ x : ((purityGeometricFiber k).obj X).left,
      ∃ (i : ι) (y : ((purityGeometricFiber k).obj (U i)).left),
        ((purityGeometricFiber k).map (j i)).left y = x := by
  intro x
  obtain ⟨i, y, hy⟩ := hj (purityGeometricFiberProj X x)
  obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
    (purityGeometricFiber_isPullback (j i)) y x hy
  exact ⟨i, z, hz⟩

variable {X Y : Over (Spec (.of k))} (f : X ⟶ Y) [Smooth f.left]

/-- The concrete smooth charts cover the geometric fiber of the source. -/
lemma puritySmoothChartAt_geometric_covers :
    ∀ x : ((purityGeometricFiber k).obj X).left,
      ∃ (i : X.left) (y : ((purityGeometricFiber k).obj (puritySmoothChartAt f i).sourceOver).left),
        ((purityGeometricFiber k).map (puritySmoothChartAt f i).inclusionOver).left y = x := by
  apply purityGeometricFiber_covers
  intro x
  obtain ⟨y, hy⟩ := puritySmoothChartAt_covers f x
  exact ⟨x, y, hy⟩

variable {f}

/-- The factorization survives base change as an equality of Over morphisms. -/
lemma PuritySmoothChart.factorization_geometric (c : PuritySmoothChart f) :
    (purityGeometricFiber k).map c.etaleOver ≫
        (purityGeometricFiber k).map c.openOver ≫
        (purityGeometricFiber k).map c.projectionOver =
      (purityGeometricFiber k).map c.inclusionOver ≫ (purityGeometricFiber k).map f := by
  rw [← Functor.map_comp, ← Functor.map_comp, c.factorization_over, Functor.map_comp]

end AlgebraicGeometry
