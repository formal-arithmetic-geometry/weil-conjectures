/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality

/-! # Geometric comparison on residue cycles, before minimality -/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

set_option Elab.async false in
-- Preserve the original interface, including hypotheses unnecessary for this comparison.
set_option linter.unusedVariables false in
set_option linter.style.haveILetI false in
set_option maxHeartbeats 600000 in
-- The interface and its specialization include chosen derived localizations.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Residue cycles map naturally to geometric fibre cohomology, and the source
comparison is surjective with kernel exactly the residue boundaries.
Source: Stacks Project, Tag 0B91 (derived base change), Tag 0BF2 (functoriality),
and the affine-base cohomology comparison of Tag 01XK.
(blueprint: lem-sc-picard-residue-cycles-geometric-naturality)

Proof: Use the coefficient adjunction unit for each ui to obtain the canonical
pullback arrow on direct images. Restrict to U and conjugate by the representing
isomorphisms hE and hCi, giving a_i in the derived category. Strictly perfect
models consist of flat terms, so ordinary termwise residue tensor computes their
derived residue tensor. Affine evaluation identifies kappa(p) with kappa(w),
and the immersion identifies kappa(w) with kappa(s). Apply arbitrary derived
base change to these identifications. Affine cohomology identifies degree-one
homology with cohomology of the geometric fibre coefficient. Trivialize the
source coefficient using τ and every target coefficient using the pullback of
τ along ui_s; independently supplied trivializations are unnecessary for this
comparison. Compose the cycle-to-homology quotient with these identifications
to define γ and β_i. The source cycle quotient is surjective, and its kernel is
exactly the image of the incoming residue differential, giving the two source
assertions without assuming either source differential vanishes. For a chain
representative of a_i, its homology map agrees with the localized arrow. Apply
naturality of derived base change and affine cohomology to obtain the equation
on source cycles and their target images. No basis, minimality, projection, or
extension to a full degree-one term is involved. For n=0 the target assertions
are vacuous; nonzero source boundaries are explicitly retained in the kernel. -/
theorem picard_residue_cycles_geometric_naturality
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
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
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
    let ZK := LinearMap.ker
      ((show (K.X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
        (K.X 2).val.obj (.op (Over.mk (𝟙 U))) from
          ((K.d 1 2).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField)
    let Z := fun i ↦ LinearMap.ker
      ((show ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
        ((C i).X 2).val.obj (.op (Over.mk (𝟙 U))) from
          (((C i).d 1 2).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField)
    ∃ (γ : ZK →+ Sheaf.H
        (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i))
      (β : ∀ i, Z i →+ Sheaf.H (structureSheafAb
        (pullback (fi i) (S.fromSpecResidueField s))) 1),
      Function.Surjective γ ∧
      (∀ x : ZK, γ x = 0 ↔ ∃ y, ((show (K.X 0).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
        (K.X 1).val.obj (.op (Over.mk (𝟙 U))) from
          ((K.d 0 1).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField) y = x.val) ∧
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
        ∀ (x : ZK) (hy :
          ((((φ.f 1).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange
            p.ResidueField) x.val ∈ Z i),
          β i ⟨_, hy⟩ = structureSheafCohomologyPullback
            (((Over.pullback (S.fromSpecResidueField s)).map
              (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                (ui i) (hui i))).left) 1 (γ x) := by
  clear htrivial hnegative hCnegative hCzero
  let p := RingHom.ker (W.evaluation U w hwU).hom
  letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
  have hgeom :=
    picard_residue_homology_geometric_naturality.{v} f Xi fi ui hui L W k w s hw τ
      U hwU hU p rfl K hK hE C hC hCi
  refine Exists.elim hgeom ?_
  intro eK heK
  refine Exists.elim heK ?_
  intro eC heC
  refine Exists.elim heC ?_
  intro a hnatural
  let qK := affineResidueCycleClass W U p K
  let γ := eK.toAddMonoidHom.comp qK
  let β := fun i ↦ (eC i).toAddMonoidHom.comp (affineResidueCycleClass W U p (C i))
  refine ⟨γ, a, β, ?_, ?_, ?_⟩
  · exact eK.surjective.comp (affineResidueCycleClass_surjective_kernel W U p K).1
  · intro x
    change eK (qK x) = 0 ↔ _
    exact eK.map_eq_zero_iff.trans
      ((affineResidueCycleClass_surjective_kernel W U p K).2 x)
  · intro i φ hφ x hy
    have hclass := hnatural i φ hφ (qK x)
    exact (congrArg (eC i)
      (affineResidueCycleHomologyMap_class (W := W) (U := U) (p := p) φ x)).symm.trans hclass

end AlgebraicGeometry.Scheme
