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

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
import Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative
/-! # Fixed-affine models used in the Picard comparison

Source: Stacks Project, Tag 0BF2.
(blueprint: lem-sc-picard-fixed-model-residue-chain-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 600000 in
-- Elaborating the chosen derived models and their residue tensor comparisons needs extra fuel.
/-- The residue maps of chain representatives agree with geometric pullback on H-one.
Source: Stacks Project, Tag 0BF2, chain maps and their fibre comparison; Tags 08CR and 0B91.
(blueprint: lem-sc-picard-fixed-model-residue-chain-comparison)

Proof: Form the canonical derived coefficient pullback arrows from Rf_* L to each
R(fi)_* ui^*L over W and restrict them to U. Conjugate by the supplied derived model
isomorphisms. The affine perfect-map representative theorem lifts each arrow to an
actual chain map φ from K to C_i. The finite-free term ranks of K equal its residue
Betti dimensions. Over the residue field the equality of every term dimension with
its homology dimension forces both adjacent differential ranks to vanish, hence all
differentials vanish. Thus the residue degree-one term of K equals its H-one.
The source descent and universal structure adjunction unit imply a trivial source
bundle on the nonempty fibre: the unit rules out an empty fibre, and the finite locally
free descended bundle has rank one by invertibility after pullback. Choose a source
trivialization. Derived base change, affine cohomology comparison and the immersion
residue-field isomorphism identify its H-one with H^1(X_s,O), giving α.
Each C_i is connective with zero degree-zero differential, so its residue H-one is
the kernel of its degree-one differential. Choose a vector-space projection from the
whole residue degree-one term onto this kernel. Identify that kernel with H^1(Xi_s,O)
using base change and the pullback of the chosen source fibre trivialization.
This choice identifies every coefficient pullback on the fibre with the canonical
structure-module pullback, and gives γ_i. The target trivializations over U are
used to construct the normalized targets, not to fix their fibre identifications.
The chain equation and
source residue minimality put the image of φ^1 in the kernel, where the projection
is the identity. Naturality of canonical base change and of the affine cohomology
comparison gives the displayed equality. The source basis e1 is arbitrary and is
incorporated through its inverse. No target degree-one freeness or H-one injectivity
is used. Evaluate each degree-one chain component on sections and compose it with
e1 inverse to define t_i. The degree-zero chain equation and the zero target
bottom differential imply t_i(e1(d_K(e0 inverse(a))))=0 for every a.
Take the product of the section maps to obtain t. For gamma, tensor each coordinate
projection and compose with its residue map, then take the product. This proves
the displayed joint equality. Empty index sets give the unique family; a zero
source rank gives zero H-one. -/
theorem picard_fixed_model_residue_chain_comparison
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
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) j w)))))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
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
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    let p := RingHom.ker (W.evaluation U w hwU).hom
    letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
    ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (t : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)]
        (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U)))))
      (γ : (p.ResidueField ⊗[Γ(W, U)]
          (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))))) →+
        (∀ i, Sheaf.H (structureSheafAb
          (pullback (fi i) (S.fromSpecResidueField s))) 1)),
      (∀ a, t (e1 ((K.d 0 1).val.app
        (.op (Over.mk (𝟙 U))) (e0.symm a))) = 0) ∧
      ∀ z, γ (t.baseChange p.ResidueField z) = fun i ↦
        structureSheafCohomologyPullback
          (((Over.pullback (S.fromSpecResidueField s)).map
            (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
              (ui i) (hui i))).left) 1 (α z) := by
  classical
  obtain ⟨α, a, γ, hγ⟩ :=
    picard_fixed_model_residue_derived_comparison
      f Xi fi ui hui hO L W k w s hw hLs U hwU hU htrivial m K hK hnegative hrank e1 hE C
      hC hCnegative hCzero hCi
  have hφ : ∀ i, ∃ φ : K ⟶ C i, DerivedCategory.Q.map φ = a i :=
    fun i ↦ perfect_affine_map_representative W U hU K (C i) hK (hC i) (a i)
  let φ : ∀ i, K ⟶ C i := fun i ↦ Classical.choose (hφ i)
  have hφeq : ∀ i, DerivedCategory.Q.map (φ i) = a i :=
    fun i ↦ Classical.choose_spec (hφ i)
  let t : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)]
      (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U)))) :=
    LinearMap.pi (fun i ↦
      (((φ i).f 1).val.app (.op (Over.mk (𝟙 U)))).hom.comp e1.symm.toLinearMap)
  refine ⟨α, t, γ, ?_, hγ φ hφeq⟩
  intro x
  ext i
  have hc : K.d 0 1 ≫ (φ i).f 1 = 0 := by
    rw [← (φ i).comm 0 1, hCzero i, comp_zero]
  have he := congrArg
    (fun q ↦ (q.val.app (.op (Over.mk (𝟙 U)))) (e0.symm x)) hc
  have hz : (0 : K.X 0 ⟶ (C i).X 1).val = 0 := rfl
  simpa [t, SheafOfModules.comp_val, PresheafOfModules.comp_app, hz] using he

end AlgebraicGeometry.Scheme
