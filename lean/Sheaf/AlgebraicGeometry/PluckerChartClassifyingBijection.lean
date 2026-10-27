module

public import Sheaf.AlgebraicGeometry.PluckerChartQuotientGluing
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison
import WeilConjectures.Topology.GlueSheavesOfModules
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing
import Sheaf.AlgebraicGeometry.GradedProjQuotientTwistComparison
import Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts

/-! # Classification by the normalized Plücker charts

Source: Stacks Project, constructions.tex, Tags 089T and 01NE, and the explicit
normalized determinant-coordinate completion in the DAG
(blueprint: lem-sfb-plucker-chart-classifying-bijection).

Scalar extension along the canonical ring isomorphism ℤ → ULift ℤ places the recorded
integer graded rings in any universe. It changes neither their equations nor their
coordinates, and permits all test schemes in that universe.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.PluckerDeterminantLocus
open scoped TensorProduct

namespace AlgebraicGeometry.Plucker

/-- The polynomial grading after the canonical universe extension of ℤ.
Source: Stacks 01NE, polynomial Proj (blueprint: lem-sfb-plucker-chart-classifying-bijection).
-/
noncomputable def largePolynomialGrade (N r d : ℕ) :
    Submodule (ULift.{u} ℤ) ((ULift.{u} ℤ) ⊗[ℤ] PolynomialRing N r) :=
  (MvPolynomial.homogeneousSubmodule (Index N r) ℤ d).baseChange (ULift.{u} ℤ)

/-- The actual quotient grading after the same canonical universe extension.
Source: Stacks 089T, determinant presentation completion
(blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable def largeGrade (N r d : ℕ) :
    Submodule (ULift.{u} ℤ) ((ULift.{u} ℤ) ⊗[ℤ] CoordinateRing N r) :=
  (quotientGrade N r d).baseChange (ULift.{u} ℤ)

/-- Scalar extension preserves the recorded polynomial grading.
Source: Stacks 01NE (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable instance largePolynomialGradedRing (N r : ℕ) :
    GradedRing (largePolynomialGrade.{u} N r) := GradedAlgebra.baseChange _

/-- Scalar extension preserves the recorded quotient grading.
Source: Stacks 089T (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable instance largeGradedRing (N r : ℕ) :
    GradedRing (largeGrade.{u} N r) := GradedAlgebra.baseChange _

/-- The canonical degree-preserving inclusion of the original quotient coordinates.
Source: Stacks 089T, scalar extension of coordinates
(blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable def largeInclusion (N r : ℕ) :
    quotientGrade N r →+*ᵍ largeGrade.{u} N r where
  __ := (Algebra.TensorProduct.includeRight :
    CoordinateRing N r →ₐ[ℤ] (ULift.{u} ℤ) ⊗[ℤ] CoordinateRing N r).toRingHom
  map_mem hx := Submodule.tmul_mem_baseChange_of_mem _ hx

/-- The actual scalar extension of the graded quotient map B → B/H.
Source: Stacks 089T, determinant presentation, and 01N0, quotient Proj
(blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable def largeQuotientMap (N r : ℕ) :
    largePolynomialGrade.{u} N r →+*ᵍ largeGrade.{u} N r :=
  (GradedAlgHom.liftEquiv (MvPolynomial.homogeneousSubmodule (Index N r) ℤ)
    (largeGrade.{u} N r)
    { toAlgHom := (Algebra.TensorProduct.includeRight :
        CoordinateRing N r →ₐ[ℤ] (ULift.{u} ℤ) ⊗[ℤ] CoordinateRing N r).comp
          (Ideal.Quotient.mkₐ ℤ (relationsIdeal N r))
      map_mem := fun hx ↦ Submodule.tmul_mem_baseChange_of_mem _
        ((quotientMap N r).map_mem hx) }).toGradedRingHom

/-- The scalar-extended quotient map is still surjective.
Source: Stacks 01N0, the quotient presentation in the node
(blueprint: lem-sfb-plucker-chart-classifying-bijection).
Proof: ℤ → ULift ℤ is surjective, so every tensor in the target is 1 ⊗ a.
Lift a through B → B/H; then 1 ⊗ its lift maps to that tensor. This uses no flatness
or cancellation and applies to the actual quotient ideal, without saturation. -/
theorem largeQuotientMap_surjective (N r : ℕ) :
    Function.Surjective (largeQuotientMap.{u} N r) := sorry

/-- The canonical quotient-Proj map, in the test schemes' universe.
Source: Stacks 01N0 (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable def largeImmersion (N r : ℕ) :
    Proj (largeGrade.{u} N r) ⟶ Proj (largePolynomialGrade.{u} N r) :=
  Proj.map (largeQuotientMap.{u} N r)
    (GradedRingHom.irrelevant_le_map_of_surjective (largeQuotientMap_surjective N r))

/-- The pivot open in the canonical universe copy of the determinant Proj.
Source: Stacks 089T (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable def largeChart {N r : ℕ} (I : Index N r) :
    (Proj (largeGrade.{u} N r)).Opens :=
  Proj.basicOpen (largeGrade.{u} N r)
    (largeInclusion.{u} N r (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I)))

/-- The ratio p_J/p_I as a section, using the recorded ordered fraction, not a new ratio.
Source: Stacks 089T, 01M4 (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable def largeRatio {N r : ℕ} (I : Index N r) (t : Fin (r + 1) → Fin N) :
    Γ(Proj (largeGrade.{u} N r), largeChart.{u} I) :=
  Proj.awayToSection (largeGrade.{u} N r)
    (largeInclusion.{u} N r (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I)))
    (HomogeneousLocalization.Away.map (largeInclusion.{u} N r)
      (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I)) (fraction I t))

/-- The normalized matrix in the canonical universe copy, restricted to an open W.
Source: Stacks 089T (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable def largeMatrixOn {N r : ℕ} (I : Index N r)
    (W : (Proj (largeGrade.{u} N r)).Opens) (h : W ≤ largeChart.{u} I) :
    Matrix (Fin (r + 1)) (Fin N) Γ(Proj (largeGrade.{u} N r), W) :=
  fun a j ↦ (Proj (largeGrade.{u} N r)).presheaf.map (homOfLE h).op
    (largeRatio.{u} I (Function.update (columns I) a j))

/-- The labeled degree-one section of O(1) on the polynomial Proj model.
Source: Stacks 01NE (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable def largeCoordinate {N r : ℕ} (J : Index N r) :
    Γ(Proj.twist (largePolynomialGrade.{u} N r) 1, ⊤) :=
  (Proj.unitToTwist (𝒜 := largePolynomialGrade.{u} N r)
    (Submodule.tmul_mem_baseChange_of_mem (1 : ULift.{u} ℤ)
      (MvPolynomial.X_mem_homogeneousSubmodule_one ℤ J))).app ⊤
        (1 : Γ(Proj (largePolynomialGrade.{u} N r), ⊤))

/-- Ordered maximal wedges of the quotient generators, as actual exterior-sheaf sections.
Source: Stacks 01NE and 089T (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
noncomputable def quotientWedge {T : Scheme.{u}} {N r : ℕ} {Q : T.Modules}
    (q : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (J : Index N r) : Γ(exteriorSheaf Q (r + 1), ⊤) :=
  exteriorSheafSection Q (r + 1) ⊤
    (fun a ↦ (SheafOfModules.freeHomEquiv Q q (ULift.up (columns J a))).val (op ⊤))

/-- A morphism classifies a quotient when the pulled-back universal quotient is isomorphic
on every labeled generator. Equality on generators is exactly preservation of the quotient.
Source: Stacks 089T (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
def Classifies {X T : Scheme.{u}} {N : ℕ} {QX : X.Modules} {Q : T.Modules}
    (qX : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ QX)
    (q : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (b : T ⟶ X) : Prop :=
  ∃ e : (tensorPullback b).obj QX ≅ Q, ∀ i : ULift.{u} (Fin N),
    e.hom.app ⊤ (((tensorPullbackSectionAdjunction b).unit.app QX).app ⊤
      ((SheafOfModules.freeHomEquiv QX qX i).val (op ⊤))) =
        (SheafOfModules.freeHomEquiv Q q i).val (op ⊤)

/-- The determinant quotient-line pair classified by a projective morphism.
Source: Stacks 01NE (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
def DeterminantClassifies {T : Scheme.{u}} {N r : ℕ} {Q : T.Modules}
    (q : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (a : T ⟶ Proj (largePolynomialGrade.{u} N r)) : Prop :=
  ∃ e : (tensorPullback a).obj (Proj.twist (largePolynomialGrade.{u} N r) 1) ≅
      exteriorSheaf Q (r + 1),
    ∀ J : Index N r, e.hom.app ⊤
      (((tensorPullbackSectionAdjunction a).unit.app
        (Proj.twist (largePolynomialGrade.{u} N r) 1)).app ⊤ (largeCoordinate.{u} J)) =
          quotientWedge q J

/-- Exact pivot inverse images, minor ratios in any local frame, and normalized entries.
The inverse of the pivot determinant is used only on the pivot locus, where it is a unit.
Source: Stacks 089T and 01M4 (blueprint: lem-sfb-plucker-chart-classifying-bijection). -/
def ClassifyingChartFormula {T : Scheme.{u}} {N r : ℕ} {Q : T.Modules}
    (q : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
    (b : T ⟶ Proj (largeGrade.{u} N r)) : Prop :=
  ∀ I : Index N r, (b ⁻¹ᵁ largeChart.{u} I : Set T) = pivotLocus q I ∧
    ∀ (V : T.Opens) (φ : Q.restrict V.ι ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1))))
      (hV : V ≤ b ⁻¹ᵁ largeChart.{u} I),
      IsUnit ((quotientMatrix q V φ).submatrix id (columns I)).det ∧
      (∀ J : Index N r, b.appLE (largeChart.{u} I) V hV (largeRatio.{u} I (columns J)) =
        ((quotientMatrix q V φ).submatrix id (columns J)).det *
          Ring.inverse ((quotientMatrix q V φ).submatrix id (columns I)).det) ∧
      (∀ (a : Fin (r + 1)) (j : Fin N),
        b.appLE (largeChart.{u} I) V hV (largeRatio.{u} I (Function.update (columns I) a j)) =
          (((quotientMatrix q V φ).submatrix id (columns I))⁻¹ * quotientMatrix q V φ) a j)

set_option maxHeartbeats 800000 in
-- The clauses compare several explicit tensor-pullback and scalar-extension interfaces.
/-- The normalized universal quotient gives the natural classification, the actual
scheme-theoretic factorization of the determinant map, and the labeled determinant line.
Positive rank is written r+1. The quotient and polynomial rings are the canonical scalar
extensions along ℤ ≅ ULift ℤ; thus the test scheme universe is arbitrary.

Source: Stacks Project, constructions.tex, Tags 089T and 01NE, with the determinant-chart
completion in the node (blueprint: lem-sfb-plucker-chart-classifying-bijection).

Proof, in the nine steps of the node:
1. The pivot opens from lem-sfb-plucker-chart-quotient-gluing cover T. Apply
   lem-sc-exterior-sheaf-local-free-comparison and lem-weil-pbc-exterior-power-free-basis:
   the wedge of the pivot generators freely generates the top exterior sheaf on each
   such open, including empty and nonaffine opens. These sections generate the line.
2. Expand the ordered wedges in any frame. Alternation removes repeated rows and
   the Leibniz formula gives the maximal minors. The adjugate identity and
   lem-sfb-matrix-cramer-determinant-identities give the normalized minor ratios and
   single-replacement entries, without cancellation at zero divisors.
3. The section-preserving projective-space-functor-of-points theorem supplies the unique
   quotient-line map a. The sections-morphism-to-proj-polynomial-ring theorem computes
   its pivot inverse images and ratios.
4. The polynomial chart isomorphisms of lem-sfb-plucker-determinant-locus-charts send
   the off-pivot generators to the normalized entries. The affine-target correspondence
   gives local scheme maps even when the source pivot opens are not affine. The overlap
   matrix identity of chart-quotient-gluing makes them agree; scheme-morphism-gluing
   produces b and the displayed chart formulas.
5. The chart formulas for the quotient Proj map, from
   lem-sfb-graded-proj-quotient-twist-comparison, give b followed by j equal to a.
   Every factor has the same inverse images and the same single-replacement generators,
   so affine-target injectivity and gluing prove unique scheme-theoretic factorization.
6. Match pulled-back pivot bases to the original quotient's pivot bases. Their overlap
   matrices agree, so lem-weil-pbc-glue-sheaves-of-modules glues these maps and their
   inverses. They preserve each standard generator, giving Classifies.
7. For any b, its pulled-back pivot charts recover its original coordinate maps.
   Affine-target injectivity and gluing give the inverse identity for every morphism.
8. An isomorphism preserving the quotient preserves normalized entries; pulling back a
   quotient pulls back those entries. Uniqueness gives invariance and naturality. Along
   with steps 6 and 7 this gives mutually inverse natural bijections on quotient classes,
   without choosing class representatives.
9. Apply the projective-space universal pair to qX. Its classifying map is the identity
   by step 7, hence its projective map is j. The resulting isomorphism sends each pulled
   coordinate to precisely its ordered generator wedge, proving the final clause.
All constructions commute with the canonical scalar extension ℤ ≅ ULift ℤ used above. -/
theorem chart_classifying_bijection (N r : ℕ) (_hrN : r + 1 < N)
    (QX : (Proj (largeGrade.{u} N r)).Modules)
    (qX : SheafOfModules.free (R := (Proj (largeGrade.{u} N r)).ringCatSheaf)
      (ULift.{u} (Fin N)) ⟶ QX)
    (_hqX : Epi qX) (_hQX : QX.IsFiniteLocallyFreeOfRank (r + 1))
    (φX : ∀ I : Index N r, QX.restrict (largeChart.{u} I).ι ≅
      SheafOfModules.free (R := (largeChart.{u} I).toScheme.ringCatSheaf)
        (ULift.{u} (Fin (r + 1))))
    (_hφX : ∀ I, quotientMatrix qX (largeChart.{u} I) (φX I) =
      largeMatrixOn.{u} I (largeChart.{u} I) le_rfl)
    (_hchange : ∀ (I K : Index N r) (W : (Proj (largeGrade.{u} N r)).Opens)
      (hI : W ≤ largeChart.{u} I) (hK : W ≤ largeChart.{u} K),
      frameChange (φX I) (φX K) W hI hK =
        ((largeMatrixOn.{u} I W hI).submatrix id (columns K))⁻¹) :
    (∀ (T : Scheme.{u}) (Q : T.Modules)
      (q : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q),
      Epi q → Q.IsFiniteLocallyFreeOfRank (r + 1) →
      (exteriorSheaf Q (r + 1)).IsInvertible ∧
      (∀ t : T, ∃ J : Index N r,
        t ∈ nonvanishingLocus (exteriorSheaf Q (r + 1)) (quotientWedge q J)) ∧
      ∃! a : T ⟶ Proj (largePolynomialGrade.{u} N r),
        DeterminantClassifies q a ∧
        (∀ a' : T ⟶ Proj (largePolynomialGrade.{u} N r),
          DeterminantClassifies q a' → a' = a) ∧
        (∃! b : T ⟶ Proj (largeGrade.{u} N r), b ≫ largeImmersion.{u} N r = a) ∧
        (∀ b : T ⟶ Proj (largeGrade.{u} N r), b ≫ largeImmersion.{u} N r = a →
          Classifies qX q b ∧ ClassifyingChartFormula q b)) ∧
    (∀ (T : Scheme.{u}) (Q : T.Modules)
      (q : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q),
      Epi q → Q.IsFiniteLocallyFreeOfRank (r + 1) →
      ∃! b : T ⟶ Proj (largeGrade.{u} N r), Classifies qX q b) ∧
    (∀ (T : Scheme.{u}) (b : T ⟶ Proj (largeGrade.{u} N r)),
      ((tensorPullback b).obj QX).IsFiniteLocallyFreeOfRank (r + 1) ∧
      ∃ p : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶
          (tensorPullback b).obj QX,
        (∀ i : ULift.{u} (Fin N), (SheafOfModules.freeHomEquiv _ p i).val (op ⊤) =
          ((tensorPullbackSectionAdjunction b).unit.app QX).app ⊤
            ((SheafOfModules.freeHomEquiv QX qX i).val (op ⊤))) ∧
        Epi p ∧ ∀ c : T ⟶ Proj (largeGrade.{u} N r), Classifies qX p c ↔ c = b) ∧
    (∀ (T : Scheme.{u}) (Q Q' : T.Modules)
      (q : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q)
      (q' : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q')
      (e : Q ≅ Q'), q ≫ e.hom = q' →
      ∀ b b' : T ⟶ Proj (largeGrade.{u} N r),
        Classifies qX q b → Classifies qX q' b' → b = b') ∧
    (∀ (T T' : Scheme.{u}) (f : T' ⟶ T) (Q : T.Modules)
      (q : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q),
      Epi q → Q.IsFiniteLocallyFreeOfRank (r + 1) →
      ∀ (b : T ⟶ Proj (largeGrade.{u} N r)), Classifies qX q b →
      ∀ p : SheafOfModules.free (R := T'.ringCatSheaf) (ULift.{u} (Fin N)) ⟶
          (tensorPullback f).obj Q,
        (∀ i : ULift.{u} (Fin N), (SheafOfModules.freeHomEquiv _ p i).val (op ⊤) =
          ((tensorPullbackSectionAdjunction f).unit.app Q).app ⊤
            ((SheafOfModules.freeHomEquiv Q q i).val (op ⊤))) →
        Epi p ∧ ((tensorPullback f).obj Q).IsFiniteLocallyFreeOfRank (r + 1) ∧
        Classifies qX p (f ≫ b) ∧
        ∀ c : T' ⟶ Proj (largeGrade.{u} N r), Classifies qX p c → c = f ≫ b) ∧
    (∃ κ : Proj (largePolynomialGrade.{u} N r) ≅
        ProjectiveSpace (ULift.{u} (Index N r)) (Spec (.of (ULift.{u} ℤ))),
      (∃ θ : (tensorPullback κ.hom).obj
          (ProjectiveSpace.twist (ULift.{u} (Index N r)) (Spec (.of (ULift.{u} ℤ))) 1) ≅
            Proj.twist (largePolynomialGrade.{u} N r) 1,
        ∀ J : Index N r, θ.hom.app ⊤
          (((tensorPullbackSectionAdjunction κ.hom).unit.app
            (ProjectiveSpace.twist (ULift.{u} (Index N r)) (Spec (.of (ULift.{u} ℤ))) 1)).app
              ⊤ (ProjectiveSpace.twistOneSection (ULift.{u} (Index N r))
                (Spec (.of (ULift.{u} ℤ))) (ULift.up J))) = largeCoordinate.{u} J) ∧
      (∃ e : (tensorPullback (largeImmersion.{u} N r ≫ κ.hom)).obj
          (ProjectiveSpace.twist (ULift.{u} (Index N r)) (Spec (.of (ULift.{u} ℤ))) 1) ≅
            exteriorSheaf QX (r + 1),
        ∀ J : Index N r, e.hom.app ⊤
          (((tensorPullbackSectionAdjunction (largeImmersion.{u} N r ≫ κ.hom)).unit.app
            (ProjectiveSpace.twist (ULift.{u} (Index N r)) (Spec (.of (ULift.{u} ℤ))) 1)).app
              ⊤ (ProjectiveSpace.twistOneSection (ULift.{u} (Index N r))
                (Spec (.of (ULift.{u} ℤ))) (ULift.up J))) = quotientWedge qX J)) := sorry

end AlgebraicGeometry.Plucker
