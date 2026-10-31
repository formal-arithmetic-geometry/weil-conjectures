/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueHomologyChosenGeometricData
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedFibreNaturality

/-! # Affine residue data for the chosen geometric maps

Source: Stacks Project, Tags 0B91, 0BF2, 01IB and 08CR.
(blueprint: lem-sc-picard-residue-homology-chosen-geometric-maps)

(blueprint: new-picard-residue-homology-chosen-geometric-fibre-data)

This intermediate statement packages affine residue data with the geometric fibre comparisons.
The enclosing theorem only composes additive equivalences. -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
  picardDerivedCoefficientMap structureSheafAb structureSheafCohomologyPullback

/-- The affine and geometric comparisons before their final composition. -/
structure PicardResidueHomologyGeometricData
    {I : Type u} {Ksrc A C : Type v} {Tgt B D P : I → Type v}
    (M : ∀ i, P i → Ksrc → Tgt i) (N : ∀ i, C → D i)
    [AddCommGroup Ksrc] [AddCommGroup A] [AddCommGroup C]
    [∀ i, AddCommGroup (Tgt i)] [∀ i, AddCommGroup (B i)]
    [∀ i, AddCommGroup (D i)] where
  eK : Ksrc ≃+ A
  eC : ∀ i, Tgt i ≃+ B i
  φ : ∀ i, P i
  e : A ≃+ C
  ei : ∀ i, B i ≃+ D i
  F : ∀ i, A → B i
  hdata : ∀ i z, eC i (M i (φ i) z) = F i (eK z)
  hgeom : ∀ i z, ei i (F i z) = N i (e z)

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- The dependent family of derived-category maps requires extra elaboration heartbeats.
/-- The lower data theorem packages the affine and geometric comparisons.

Proof: Apply the affine residue data theorem to choose eK, eC and chain maps.
Apply picard_derived_fibre_naturality to choose e and ei. Package both naturality
identities in the structure. The final additive-equivalence composition is proved by
the enclosing theorem. -/
theorem picard_residue_homology_chosen_geometric_fibre_data
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
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
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i)))
 :
    let H := derivedFiberCohomologyFunctor W w 1
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    let Ei := fun i ↦ (schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))
    Nonempty (PicardResidueHomologyGeometricData
      (Ksrc := affineResidueCycleHomology W U p K)
      (A := H.obj E) (C := Sheaf.H
        (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (Tgt := fun i ↦ affineResidueCycleHomology W U p (C i))
      (B := fun i ↦ H.obj (Ei i))
      (D := fun i ↦ Sheaf.H
        (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
      (P := fun i ↦ K ⟶ C i)
      (M := fun i ψ z ↦ affineResidueCycleHomologyMap ψ z)
      (N := fun i z ↦ structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
            (ui i) (hui i))).left) 1 z)) := by
  obtain ⟨eK, eC, φ, hdata⟩ := picard_residue_homology_chosen_geometric_data
    f Xi fi ui hui L W k w s hw τ U hwU hU p hp K hK hE C hC hCi
  obtain ⟨e, he⟩ := picard_derived_fibre_naturality
    f Xi fi ui hui L W k w s hw τ
  let ei : ∀ i, _ := fun i ↦ Classical.choose (he i)
  have hei : ∀ i z, ei i ((derivedFiberCohomologyFunctor W w 1).map
      (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) z) =
      structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
            (ui i) (hui i))).left) 1 (e z) := by
    intro i z
    exact Classical.choose_spec (he i) z
  exact ⟨⟨eK, eC, φ, e, ei, _, hdata, hei⟩⟩

end AlgebraicGeometry.Scheme
