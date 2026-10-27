/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.PluckerDeterminantLocusCharts
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.FiniteFreeModuleStalkEquiv
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.LinearAlgebra.Matrix.LeftInverseMinors

/-! # Normalized Plücker quotient charts and their gluing

Source: Stacks Project, Constructions, Tag 089T, normalized quotient subfunctors,
open pivot loci, and the sheaf-gluing paragraph; explicit determinant-coordinate
completion in the DAG (blueprint: lem-sfb-plucker-chart-quotient-gluing).
Frames are actual isomorphisms of module sheaves. Matrices use the existing free-sheaf
matrix construction and the canonical global-sections isomorphism of an open subscheme.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.PluckerDeterminantLocus

namespace AlgebraicGeometry.Plucker

/-- Restrict Q118's normalized localization matrix, via the canonical section map, to W.
Source: Stacks, Tag 089T, normalized quotient charts
(blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
noncomputable def matrixOn {N r : ℕ} (I : Index N r)
    (W : (Proj (quotientGrade N r)).Opens)
    (h : W ≤ Proj.basicOpen (quotientGrade N r)
      (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))) :
    Matrix (Fin (r + 1)) (Fin N) Γ(Proj (quotientGrade N r), W) :=
  ((normalizedMatrix I).map (Proj.awayToSection (quotientGrade N r)
    (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I)))).map
      ((Proj (quotientGrade N r)).presheaf.map (homOfLE h).op)

/-- The ordered K-column matrix of the normalized I-matrix restricted to W.
Source: Stacks, Tag 089T, changes of normalized frames
(blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
noncomputable def pivot {N r : ℕ} (I K : Index N r)
    (W : (Proj (quotientGrade N r)).Opens)
    (h : W ≤ Proj.basicOpen (quotientGrade N r)
      (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) Γ(Proj (quotientGrade N r), W) :=
  (matrixOn I W h).submatrix id (columns K)

/-- Restrict a quotient map to U, identifying its source with the standard free sheaf.
Source: Stacks, Tag 089T (blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
noncomputable def quotientOn {X : Scheme.{u}} {N : ℕ} {Q : X.Modules}
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (U : X.Opens) :
    SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q.restrict U.ι :=
  (restrictFreeIso U.ι _).inv ≫ (restrictFunctor U.ι).map q

/-- The actual inclusion of the ordered pivot summands.
Source: Stacks, Tag 089T, s_i (blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
noncomputable def inclusion {X : Scheme.{u}} {N : ℕ} {r : ℕ} (I : Index N r) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r + 1))) ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) :=
  SheafOfModules.freeMap (fun a ↦ ULift.up (columns I a.down))

/-- The intrinsic pivot-frame locus, defined before asserting its openness.
Source: Stacks, Tag 089T, U_i (blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
def pivotLocus {X : Scheme.{u}} {N : ℕ} {r : ℕ} {Q : X.Modules}
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (I : Index N r) : Set X :=
  {x | IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map (inclusion I ≫ q))}

/-- A frame is normalized when the pivot inclusion splits the displayed local quotient.
Source: Stacks, Tag 089T (blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
def NormalizedFrame {X : Scheme.{u}} {N : ℕ} {r : ℕ} {Q : X.Modules}
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (I : Index N r) (U : X.Opens)
    (φ : Q.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1)))) : Prop :=
  inclusion I ≫ quotientOn q U ≫ φ.hom = 𝟙 _

/-- The matrix of q in a specified local frame, with entries in O_X(U).
Source: Stacks, Tag 089T (blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
noncomputable def quotientMatrix {X : Scheme.{u}} {N : ℕ} {r : ℕ} {Q : X.Modules}
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (U : X.Opens)
    (φ : Q.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1)))) :
    Matrix (Fin (r + 1)) (Fin N) Γ(X, U) :=
  ((freeMatrix (quotientOn q U ≫ φ.hom)).map U.topIso.hom).submatrix ULift.up ULift.up

/-- Restriction of a frame to a smaller open, with all canonical comparisons displayed.
Source: Stacks, Tag 089T (blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
noncomputable def frameOn {X : Scheme.{u}} {r : ℕ} {Q : X.Modules}
    {U : X.Opens} (φ : Q.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1))))
    (W : X.Opens) (h : W ≤ U) : Q.restrict W.ι ≅
      SheafOfModules.free (R := W.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1))) :=
  restrictCompIso Q U.ι (X.homOfLE h) W.ι (X.homOfLE_ι h) ≪≫
    (restrictFunctor (X.homOfLE h)).mapIso φ ≪≫ restrictFreeIso (X.homOfLE h) _

/-- The matrix changing coordinates from the U-frame to the V-frame on W.
Source: Stacks, Tag 089T (blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
noncomputable def frameChange {X : Scheme.{u}} {r : ℕ} {Q : X.Modules}
    {U V : X.Opens}
    (φ : Q.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1))))
    (ψ : Q.restrict V.ι ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1))))
    (W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) Γ(X, W) :=
  ((freeMatrix ((frameOn φ W hU).inv ≫ (frameOn ψ W hV).hom)).map W.topIso.hom).submatrix
    ULift.up ULift.up

/-- Pivot loci, unique normalized frames, and changes of frame for an arbitrary quotient.
This is a predicate packaging the corresponding clauses, not an extra hypothesis.
Source: Stacks, Tag 089T (blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
def QuotientCharts {X : Scheme.{u}} {N : ℕ} {r : ℕ} {Q : X.Modules}
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (U : Index N r → X.Opens)
    (φ : ∀ I, Q.restrict (U I).ι ≅
      SheafOfModules.free (R := (U I).toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1)))) :
    Prop :=
  (∀ I, (U I : Set X) = pivotLocus q I) ∧ (⨆ I, U I) = ⊤ ∧
    (∀ I, NormalizedFrame q I (U I) (φ I) ∧
      ∀ ψ, NormalizedFrame q I (U I) ψ → ψ = φ I) ∧
    (∀ (I K : Index N r) (W : X.Opens) (hI : W ≤ U I) (hK : W ≤ U K),
      quotientMatrix q W (frameOn (φ K) W hK) =
        ((quotientMatrix q W (frameOn (φ I) W hI)).submatrix id (columns K))⁻¹ *
          quotientMatrix q W (frameOn (φ I) W hI) ∧
      frameChange (φ I) (φ K) W hI hK =
        ((quotientMatrix q W (frameOn (φ I) W hI)).submatrix id (columns K))⁻¹)

/-- The complete pivot-locus and matrix compatibility assertion for a specified pullback
map. In the theorem this map is the explicit coproduct map on pulled-back generators.
Source: Stacks, Tag 089T (blueprint: lem-sfb-plucker-chart-quotient-gluing). -/
def PullbackCharts {X Y : Scheme.{u}} {N : ℕ} {r : ℕ} {Q : Y.Modules}
    (q : SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (U : Index N r → Y.Opens)
    (φ : ∀ I, Q.restrict (U I).ι ≅
      SheafOfModules.free (R := (U I).toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1))))
    (f : X ⟶ Y)
    (p : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶
      (tensorPullback f).obj Q) : Prop :=
  Epi p ∧ ((tensorPullback f).obj Q).IsFiniteLocallyFreeOfRank (r + 1) ∧
    ∃ ψ : ∀ I, ((tensorPullback f).obj Q).restrict (f ⁻¹ᵁ U I).ι ≅
        SheafOfModules.free (R := (f ⁻¹ᵁ U I).toScheme.ringCatSheaf)
          (ULift.{u} (Fin (r + 1))),
      (∀ I, (f ⁻¹ᵁ U I : Set X) = pivotLocus p I) ∧
      (∀ I, NormalizedFrame p I (f ⁻¹ᵁ U I) (ψ I) ∧
        quotientMatrix p (f ⁻¹ᵁ U I) (ψ I) = (quotientMatrix q (U I) (φ I)).map (f.app (U I)))

/-- Normalized quotient matrices give the transition cocycle and the glued universal
quotient, and every locally free quotient has compatible open pivot charts.

Source: Stacks, Tag 089T, normalized quotient subfunctors and sheaf gluing, with the
explicit determinant-coordinate completion in the DAG
(blueprint: lem-sfb-plucker-chart-quotient-gluing).

Proof, following the eight steps of the node:
1. The determinant-locus chart lemma gives det M_J = p_J/p_I. On an overlap,
   p_K/p_I and p_I/p_K are inverse sections. The adjugate identity inverts D_IK.
2. Set W = D_IK^(-1) M^(I). Determinant multiplication gives its J-minor p_J/p_K.
   Its K-columns are the identity. Replacing one such columns by columns j expresses
   W_aj as the appropriate signed minor, exactly the defining entry of M^(K).
   Repetitions give zero and no nonunit is cancelled.
3. Applying this twice on a triple overlap gives two matrices taking M^(I) to M^(L).
   Their equality follows by taking the identity I-columns. D_II = 1 gives g_II = 1.
4. Glue the free rank-r sheaves using g_IK by glue-sheaves-of-modules. The local
   quotient maps agree, hence glue. Their pivot inclusions are right inverses, giving
   surjectivity locally and therefore as a sheaf morphism.
5. In a local trivialization of an arbitrary Q, the I-frame locus is the basic open
   of the determinant of its I-columns matrix. The adjugate identity proves the frame
   criterion, and changes of trivialization multiply this determinant by a unit.
6. At a stalk the surjective quotient matrix has a right inverse. Cauchy--Binet
   expresses 1 as a sum of maximal minors times coefficients. Some minor is outside
   the maximal ideal of the local ring, so these pivot opens cover.
7. The pivot map b_I = q s_I is invertible on its frame locus. The frame b_I^(-1)
   gives the unique normalized matrix b_I^(-1) q. On overlaps b_I^(-1) b_K is the
   K-column matrix, so changing frames multiplies on the left by its inverse.
8. The tensor-pullback unit sends every generator to 1 tensor that generator.
   Pullback therefore acts entrywise on matrices and minors. A local stalk ring map
   preserves and reflects units, so the pulled-back pivot locus is exactly the inverse
   image. The pulled-back pivot frame gives precisely the pulled-back normalized entries,
   and the pulled-back splittings prove that the quotient remains surjective.
The proof uses the node's matrix-adjugate, Cramer-determinant, sheaf-gluing, basic-open,
finite-free-stalk, stalk-exactness, left-inverse-minors and local-unit dependencies. -/
theorem chart_quotient_gluing (N r : ℕ) (_hrN : r + 1 < N) :
    (∀ (I : Index N r) (W : (Proj (quotientGrade N r)).Opens)
      (hI : W ≤ Proj.basicOpen (quotientGrade N r)
        (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))),
      (matrixOn I W hI).submatrix id (columns I) = 1) ∧
    (∀ (I K : Index N r) (W : (Proj (quotientGrade N r)).Opens)
      (hI : W ≤ Proj.basicOpen (quotientGrade N r)
        (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I)))
      (hK : W ≤ Proj.basicOpen (quotientGrade N r)
        (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X K))),
      IsUnit (pivot I K W hI).det ∧
      (pivot I K W hI).det =
        (Proj (quotientGrade N r)).presheaf.map (homOfLE hI).op
          (Proj.awayToSection (quotientGrade N r)
            (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))
            (fraction I (columns K))) ∧
      matrixOn K W hK = (pivot I K W hI)⁻¹ * matrixOn I W hI) ∧
    (∀ (I K L : Index N r) (W : (Proj (quotientGrade N r)).Opens)
      (hI : W ≤ Proj.basicOpen (quotientGrade N r)
        (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I)))
      (hK : W ≤ Proj.basicOpen (quotientGrade N r)
        (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X K)))
      (_hL : W ≤ Proj.basicOpen (quotientGrade N r)
        (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X L))),
      (pivot I L W hI)⁻¹ = (pivot K L W hK)⁻¹ * (pivot I K W hI)⁻¹ ∧
      (pivot I I W hI)⁻¹ = 1) ∧
    (∃ (Q : (Proj (quotientGrade N r)).Modules)
      (q : SheafOfModules.free (R := (Proj (quotientGrade N r)).ringCatSheaf)
        (ULift.{0} (Fin N)) ⟶ Q),
      Epi q ∧ Q.IsFiniteLocallyFreeOfRank (r + 1) ∧
      ∃ φ : ∀ I : Index N r,
          Q.restrict (Proj.basicOpen (quotientGrade N r)
            (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))).ι ≅
          SheafOfModules.free (R := (Proj.basicOpen (quotientGrade N r)
            (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))).toScheme.ringCatSheaf)
            (ULift.{0} (Fin (r + 1))),
        (∀ I,
          quotientMatrix q (Proj.basicOpen (quotientGrade N r)
            (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))) (φ I) =
            (normalizedMatrix I).map (Proj.awayToSection (quotientGrade N r)
              (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))) ∧
          NormalizedFrame q I (Proj.basicOpen (quotientGrade N r)
            (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))) (φ I)) ∧
        (∀ (I K : Index N r) (W : (Proj (quotientGrade N r)).Opens)
          (hI : W ≤ Proj.basicOpen (quotientGrade N r)
            (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I)))
          (hK : W ≤ Proj.basicOpen (quotientGrade N r)
            (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X K))),
          frameChange (φ I) (φ K) W hI hK = (pivot I K W hI)⁻¹)) ∧
    (∀ (T : Scheme.{u}) (Q : T.Modules)
      (q : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q),
      Epi q → Q.IsFiniteLocallyFreeOfRank (r + 1) →
      ∃ (U : Index N r → T.Opens)
        (φ : ∀ I, Q.restrict (U I).ι ≅
          SheafOfModules.free (R := (U I).toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1)))),
        QuotientCharts q U φ ∧
        ∀ (T' : Scheme.{u}) (f : T' ⟶ T),
          PullbackCharts q U φ f
            (Sigma.desc (fun i ↦ homOfGlobalSection ((tensorPullback f).obj Q)
              (((tensorPullbackSectionAdjunction f).unit.app Q).app ⊤
                ((SheafOfModules.freeHomEquiv Q q i).val (op ⊤)))))) := by
  sorry

end AlgebraicGeometry.Plucker
