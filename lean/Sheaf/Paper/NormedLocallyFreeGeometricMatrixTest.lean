/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Instances.Matrix
import Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension
import Sheaf.CategoryTheory.MonoidalFiniteFreeTransport
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.TotallyDisconnectedCoefficientRealization
import Sheaf.Paper.NormalizedContinuousSetComparisonCoherence
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Determinant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Geometric matrix detection for locally finite free normed coefficients

Source: Hemo--Richarz--Scholbach, Example 3.1 and Section 3; the continuous
matrix inverse and cover descent argument in
(blueprint: lem-sfb-normed-locally-free-geometric-matrix-test).

The coefficient field and schemes occupy a common compatible universe `u`;
abelian sheaves have coefficients in `u + 1`. Matrices use the existing canonical
continuous realization. Bijectivity of the underlying global-section map expresses
invertibility of the F-linear map: its scalar action is by constant sections of F.
No completeness, noetherianity, or stratification hypothesis occurs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical finite-free comparison for the recorded ringed module inverse image.
Source: Hemo--Richarz--Scholbach, Example 3.1, and the finite-free transport in step 3
(blueprint: lem-sfb-normed-locally-free-geometric-matrix-test).
The biproduct comparison uses the regular coefficient comparison; its extension of
scalars is identified with restriction along the inverse coefficient isomorphism. -/
noncomputable def matrixTestFreePullbackIso
    (F : Type u) [NormedField F] {X Y : Scheme.{u}} (p : Y ⟶ X) (n : ℕ) :
    (CondensedRing.upperStar (condensedFieldCoefficientRingObj F) p).obj
        (Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) X) n) ≅
      Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) Y) n :=
  (CondensedRing.upperStar (condensedFieldCoefficientRingObj F) p).mapBiproduct
      (fun _ : Fin n ↦ Mod.regular
        (condensedRingObj (condensedFieldCoefficientRingObj F) X)) ≪≫
    biproduct.mapIso (fun _ : Fin n ↦
      (Mod.extendScalarsIsoComapInv
        (condensedPullbackHom (condensedFieldCoefficientRingObj F) p)).app
          (((upperStar Ab.{u + 1} p).mapMod
            (condensedRingObj (condensedFieldCoefficientRingObj F) X)).obj
              (Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj F) X))) ≪≫
        Mod.regularIsoOfIsIso (condensedPullbackHom (condensedFieldCoefficientRingObj F) p))

/-- Pull back a finite-free arrow in the canonical transported standard bases.
Source: Hemo--Richarz--Scholbach, Example 3.1, matrix evaluation step 3
(blueprint: lem-sfb-normed-locally-free-geometric-matrix-test). -/
noncomputable def matrixTestFreePullbackMap
    (F : Type u) [NormedField F] {X Y : Scheme.{u}} (p : Y ⟶ X) {n m : ℕ}
    (d : Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) X) n ⟶
      Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) X) m) :
    Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) Y) n ⟶
      Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) Y) m :=
  (matrixTestFreePullbackIso F p n).inv ≫
    (CondensedRing.upperStar (condensedFieldCoefficientRingObj F) p).map d ≫
      (matrixTestFreePullbackIso F p m).hom

/-- The continuous matrix of the actual pulled-back arrow, in those standard bases.
Source: Hemo--Richarz--Scholbach, Example 3.1, matrix evaluation step 3
(blueprint: lem-sfb-normed-locally-free-geometric-matrix-test). -/
noncomputable def matrixTestPullbackMatrix
    (F : Type u) [NormedField F] [TotallyDisconnectedSpace F]
    {X Y : Scheme.{u}} (p : Y ⟶ X) {n m : ℕ}
    (d : Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) X) n ⟶
      Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) X) m) :
    Matrix (Fin m) (Fin n) C(Y, F) :=
  continuousFieldPresentationMatrix F Y (condensedFieldContinuousMapIso F Y).hom.hom
    (matrixTestFreePullbackMap F p d)

/-- Geometric invertibility gives a common finite-free cover, canonical continuous
matrices, geometric evaluation, and restriction-compatible adjugate inverses.

Source: Hemo--Richarz--Scholbach, Example 3.1 and Section 3; agent determinant,
adjugate and covering descent argument
(blueprint: lem-sfb-normed-locally-free-geometric-matrix-test).

Proof:
1. Use det-def-sfb-constructible-local-model and the field clause of
lem-sfb-scalar-finite-free-resolutions: each finitely presented scalar model is finite
free. Apply lem-sfb-constant-finite-free-presentation-extension and refine the two
covers by fibre products. Use lem-weil-proetale-weakly-etale-localization and
lem-sfb-proetale-object-inverse-image-restriction to identify restriction and module
inverse image. The normalized continuous realization identifies the coefficient
comparison on every object with precomposition.
2. The internal/sectionwise equivalence
(def-weil-pbc-internal-abelian-sheaf-module-equivalence) and finite-free matrix
calculus (lem-sfb-ringed-site-free-matrix-scalar-extension) identify each arrow with
its continuous matrix, acting sectionwise by multiplication. The coefficient
realization respects addition, multiplication, finite products and the unit by
lem-sfb-totally-disconnected-coefficient-realization and
lem-sfb-normalized-continuous-set-comparison-coherence.
3. Module inverse image is additive and preserves finite biproducts
(det-prop-sfb-module-pullback-exact-main, lem-sfb-monoidal-finite-free-transport).
In transported standard bases each entry pulls back by precomposition. On Spec k
it is constant with value at the image point. Composition of module inverse images
identifies its global sections with the map in the hypothesis.
4. For every point of a nonempty cover member choose an algebraic closure of its
residue field (lem-pc-algebraic-closure-exists-unique, def-weil-geometric-point).
The evaluated rectangular matrix is invertible, so invariance of finite basis
cardinality (def-weil-vector-space-dimension) makes the ranks equal. The determinant
criterion (lem-weil-endomorphism-invertible-iff-det-nonzero) makes its determinant
nonzero everywhere. This chooses points on cover members and needs no lifting
of an already fixed geometric point through the cover.
5. Apply lem-sfb-continuous-adjugate-inverse to obtain the continuous pointwise
adjugate inverse. The finite-free Hom bijection turns it into g. Its two inverse
identities persist after every restriction, since all entries are precomposed.
For rank zero the determinant is one and all matrices are empty. On an empty
member both sheaves are zero; g exists without any equality of displayed ranks.
6. The local inverses agree on overlaps by uniqueness of inverses. Glue their
underlying maps by lem-pe-set-sheaf-cover-descent. Additivity, scalar linearity and
the inverse identities hold locally, hence globally. Transport back through the
internal/sectionwise module equivalence. The empty scheme is included: its sheaves
are zero and the same gluing argument applies. -/
theorem normed_locallyFree_geometric_matrix_test
    (F : Type u) [NormedField F] [TotallyDisconnectedSpace F] (T : Scheme.{u})
    (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (condensedFieldCoefficientRingObj F) T))
    (hM : HasFiniteConstantLocalModel (condensedFieldCoefficientRingObj F) T M)
    (hN : HasFiniteConstantLocalModel (condensedFieldCoefficientRingObj F) T N)
    (h : M ⟶ N)
    (hy : ∀ (k : Type u) [Field k] [IsAlgClosed k] (y : Spec (.of k) ⟶ T),
      Function.Bijective
        (((CondensedRing.upperStar (condensedFieldCoefficientRingObj F) y).map h).hom.hom.app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))) :
    IsIso h ∧
      ∃ (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage T) (n m : 𝒰.I₀ → ℕ)
        (eM : ∀ j : 𝒰.I₀,
          (CondensedRing.upperStar (condensedFieldCoefficientRingObj F) (𝒰.f j)).obj M ≅
            Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) (𝒰.X j))
              (n j))
        (eN : ∀ j : 𝒰.I₀,
          (CondensedRing.upperStar (condensedFieldCoefficientRingObj F) (𝒰.f j)).obj N ≅
            Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj F) (𝒰.X j))
              (m j)),
        ∀ j : 𝒰.I₀,
          ∃ (d : Mod.finiteFree
                (condensedRingObj (condensedFieldCoefficientRingObj F) (𝒰.X j)) (n j) ⟶
              Mod.finiteFree
                (condensedRingObj (condensedFieldCoefficientRingObj F) (𝒰.X j)) (m j))
            (g : Mod.finiteFree
                (condensedRingObj (condensedFieldCoefficientRingObj F) (𝒰.X j)) (m j) ⟶
              Mod.finiteFree
                (condensedRingObj (condensedFieldCoefficientRingObj F) (𝒰.X j)) (n j))
            (A : Matrix (Fin (m j)) (Fin (n j)) C(𝒰.X j, F))
            (B : Matrix (Fin (n j)) (Fin (m j)) C(𝒰.X j, F)),
            d = (eM j).inv ≫
                (CondensedRing.upperStar (condensedFieldCoefficientRingObj F) (𝒰.f j)).map h ≫
                  (eN j).hom ∧
            A = continuousFieldPresentationMatrix F (𝒰.X j)
                (condensedFieldContinuousMapIso F (𝒰.X j)).hom.hom d ∧
            B = continuousFieldPresentationMatrix F (𝒰.X j)
                (condensedFieldContinuousMapIso F (𝒰.X j)).hom.hom g ∧
            d ≫ g = 𝟙 _ ∧ g ≫ d = 𝟙 _ ∧
            (∀ (k : Type u) [Field k] [IsAlgClosed k]
                (z : Spec (.of k) ⟶ 𝒰.X j) (x : Spec (.of k)) (a : Fin (m j)) (b : Fin (n j)),
              matrixTestPullbackMatrix F z d a b x = A a b (z x)) ∧
            (∀ V : (𝒰.X j).ProEt,
              matrixTestPullbackMatrix F V.hom d = A.map
                  (fun a ↦ a.comp V.hom.base.hom) ∧
              matrixTestPullbackMatrix F V.hom g = B.map
                  (fun b ↦ b.comp V.hom.base.hom) ∧
              matrixTestFreePullbackMap F V.hom d ≫
                  matrixTestFreePullbackMap F V.hom g = 𝟙 _ ∧
              matrixTestFreePullbackMap F V.hom g ≫
                  matrixTestFreePullbackMap F V.hom d = 𝟙 _) ∧
            (Nonempty (𝒰.X j) → ∃ e : m j = n j,
              (∀ x : 𝒰.X j,
                ((A.map (fun a ↦ a x)).submatrix (Fin.cast e.symm) id).det ≠ 0) ∧
              ∀ x : 𝒰.X j,
                (B.map (fun b ↦ b x)).submatrix id (Fin.cast e.symm) =
                  (((A.map (fun a ↦ a x)).submatrix (Fin.cast e.symm) id).det)⁻¹ •
                    ((A.map (fun a ↦ a x)).submatrix (Fin.cast e.symm) id).adjugate) := by
  sorry

end AlgebraicGeometry.ProEtale
