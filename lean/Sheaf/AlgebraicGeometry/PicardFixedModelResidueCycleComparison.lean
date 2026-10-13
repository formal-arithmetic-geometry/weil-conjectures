/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.PicardDescendedFibreCoefficientTrivial
import Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality

/-! # Fixed Picard models: residue comparison on target cycles
Source: Stacks Project, Tag 0BF2 and Tag 0B91.
(blueprint: lem-sc-picard-fixed-model-residue-cycle-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 1500000 in
-- Elaborating the evaluated sheaf-module tensor maps requires many scalar identifications.
/-- Residue homology comparison on cycles, before extending to all degree-one vectors.
Source: Stacks Project, Tag 0BF2, functoriality of E to E_i; Tag 0B91, base change.
(blueprint: lem-sc-picard-fixed-model-residue-cycle-comparison)

Proof: Form the derived coefficient pullback arrows using the tensor pullback
adjunction, restrict to U, and conjugate by the chosen representing isomorphisms.
These choices give a_i independently of chain representatives. Apply the universal
structure unit at Spec kappa(s). If its source fibre were empty its pushforward
would be zero, contradicting the nonzero structure module of the field spectrum.
The descended finite locally free coefficient module has invertible pullback to
this nonempty fibre. FieldPullbackRankOneTrivial makes it rank one and trivial.
Choose the resulting source coefficient trivialization and pull it to every target;
this makes the maps on coefficients agree with structure-sheaf pullback.
Termwise residue tensor computes derived tensor because all models are bounded
and flat. The immersion identifies kappa(w) with kappa(s), and affine evaluation
identifies kappa(p) with kappa(w). Derived base change and affine cohomology
comparison identify model residue homology with geometric fibre cohomology.
Source minimality makes its degree-one term equal to its degree-one homology;
compose this identification with the tensor extension of e1 inverse to obtain α.
The target incoming differential is zero, so its degree-one homology is its
outgoing kernel Z_i. The comparison gives β_i on this kernel. For any chain
representative, the chain-map equation and source minimality put its image in Z_i.
Naturality of derived base change and affine cohomology comparison give the stated
equality on cycles. No complement, projection, or product map is constructed here.
An empty family leaves only the source comparison; rank zero gives zero source
cohomology. The supplied target trivializations are not chosen independently:
using pullbacks of the source trivialization is what preserves naturality. -/
theorem picard_fixed_model_residue_cycle_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (m : ℕ) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
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
    (hCnegative : ∀ i j, j < 0 → IsZero ((C i).X j))
    (hCzero : ∀ i, (C i).d 0 1 = 0)
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i)))
    (hreszero :
      let p := RingHom.ker (W.evaluation U w hwU).hom
      letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
      ∀ j : ℤ,
        (show (K.X j).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
          (K.X (j + 1)).val.obj (.op (Over.mk (𝟙 U))) from
            ((K.d j (j + 1)).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField =
          0) :
    let p := RingHom.ker (W.evaluation U w hwU).hom
    letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
    let Z := fun i ↦ LinearMap.ker
      ((show ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
        ((C i).X 2).val.obj (.op (Over.mk (𝟙 U))) from
          (((C i).d 1 2).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField)
    ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i))
      (β : ∀ i, Z i →+ Sheaf.H (structureSheafAb
        (pullback (fi i) (S.fromSpecResidueField s))) 1),
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
      let b := (((φ.f 1).val.app (.op (Over.mk (𝟙 U)))).hom).comp e1.symm.toLinearMap
      ∀ z, ∃ hz : b.baseChange p.ResidueField z ∈ Z i,
        β i ⟨b.baseChange p.ResidueField z, hz⟩ =
          structureSheafCohomologyPullback
            (((Over.pullback (S.fromSpecResidueField s)).map
              (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                (ui i) (hui i))).left) 1 (α z) := by
  classical
  let τ := Classical.choice (picard_descended_fibre_coefficient_trivial f hO L s hLs)
  let comparison :=
    picard_residue_cycles_geometric_naturality f Xi fi ui hui L W k w s hw τ
      U hwU hU htrivial K hK hnegative hE C hC hCnegative hCzero hCi
  obtain ⟨γ, a, β, hsurj, hker, hnatural⟩ := comparison
  let p := RingHom.ker (W.evaluation U w hwU).hom
  let : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
  let dK (j l : ℤ) :=
    (show (K.X j).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
      (K.X l).val.obj (.op (Over.mk (𝟙 U))) from
        ((K.d j l).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField
  let ZK := LinearMap.ker (dK 1 2)
  have hd01 : dK 0 1 = 0 := hreszero 0
  have hd12 : dK 1 2 = 0 := hreszero 1
  have hinj : Function.Injective γ := by
    apply (injective_iff_map_eq_zero γ).mpr
    intro x hx
    have hb : ∃ y, dK 0 1 y = x.val := (hker x).mp hx
    let y := Classical.choose hb
    have hy := Classical.choose_spec hb
    apply Subtype.ext
    change x.val = 0
    change dK 0 1 y = x.val at hy
    rw [hd01] at hy
    exact hy.symm
  let toCycles : (p.ResidueField ⊗[Γ(W, U)]
      (K.X 1).val.obj (.op (Over.mk (𝟙 U)))) ≃+ ZK :=
    { toFun := fun x ↦ ⟨x, by
        change dK 1 2 x = 0
        rw [hd12]
        rfl⟩
      invFun := fun x ↦ x.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let coords := (e1.symm.baseChange Γ(W, U) p.ResidueField).toAddEquiv
  let α := coords.trans (toCycles.trans (AddEquiv.ofBijective γ ⟨hinj, hsurj⟩))
  refine ⟨α, a, β, ?_⟩
  intro i φ hφ
  dsimp only
  intro z
  let F : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
      ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))) :=
    ((φ.f 1).val.app (.op (Over.mk (𝟙 U)))).hom
  let dC := ((show ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
    ((C i).X 2).val.obj (.op (Over.mk (𝟙 U))) from
      (((C i).d 1 2).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField)
  let D1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
      (K.X 2).val.obj (.op (Over.mk (𝟙 U))) :=
    ((K.d 1 2).val.app (.op (Over.mk (𝟙 U)))).hom
  let D2 : ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
      ((C i).X 2).val.obj (.op (Over.mk (𝟙 U))) :=
    (((C i).d 1 2).val.app (.op (Over.mk (𝟙 U)))).hom
  let F2 : (K.X 2).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
      ((C i).X 2).val.obj (.op (Over.mk (𝟙 U))) :=
    ((φ.f 2).val.app (.op (Over.mk (𝟙 U)))).hom
  have hsection := congrArg (fun t : K.X 1 ⟶ (C i).X 2 ↦
    (t.val.app (.op (Over.mk (𝟙 U)))).hom) (φ.comm 1 2)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp] at hsection
  have hsec : D2.comp F = F2.comp D1 := hsection
  have hcomm : dC.comp (F.baseChange p.ResidueField) =
      (F2.baseChange p.ResidueField).comp (dK 1 2) := by
    change (D2.baseChange p.ResidueField).comp (F.baseChange p.ResidueField) =
      (F2.baseChange p.ResidueField).comp (D1.baseChange p.ResidueField)
    exact (LinearMap.baseChange_comp F D2).symm.trans
      ((congrArg (fun q ↦ q.baseChange p.ResidueField) hsec).trans
        (LinearMap.baseChange_comp D1 F2))
  have hz : dC ((F.comp e1.symm.toLinearMap).baseChange p.ResidueField z) = 0 := by
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply, ← LinearMap.comp_apply, hcomm]
    rw [hd12]
    simp
  refine ⟨hz, ?_⟩
  have hy : dC ((F.baseChange p.ResidueField) (coords z)) = 0 := by
    change dC ((F.baseChange p.ResidueField)
      (e1.symm.toLinearMap.baseChange p.ResidueField z)) = 0
    simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using hz
  have heq := hnatural i φ hφ (toCycles (coords z)) hy
  have hcycle :
      (⟨(F.comp e1.symm.toLinearMap).baseChange p.ResidueField z, hz⟩ :
        LinearMap.ker dC) = ⟨(F.baseChange p.ResidueField) (coords z), hy⟩ := by
    apply Subtype.ext
    exact LinearMap.congr_fun (LinearMap.baseChange_comp e1.symm.toLinearMap F) z
  exact (congrArg (β i) hcycle).trans heq

end AlgebraicGeometry.Scheme
