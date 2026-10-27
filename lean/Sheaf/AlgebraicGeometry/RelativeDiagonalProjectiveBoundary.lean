module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Reduced projective boundaries for relative diagonal torus actions

Source: Stacks Project, Tags 034E, 056G, 01J3, 01J4 and 0356, followed by Laurent
coefficient extraction (blueprint: lem-sfb-relative-diagonal-projective-boundary).

The split torus is the existing Hopf spectrum of the group algebra of the character lattice.
The chart formulas specify the diagonal action on schemes, including nonreduced test schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry.RelativeDiagonalProjectiveBoundary

variable (A : Type u) [CommRing A] (r n : ℕ)

/-- The total-degree Proj, with its existing structure map to Spec A.
Source: Stacks, projective-space charts
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
abbrev projective : Over (Spec (.of A)) :=
  Over.mk (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A)

/-- The split torus, using the existing diagonalizable-group construction on Z^r.
The harmless universe lift does not alter the character lattice, including in rank zero.
Source: the Laurent Hopf algebra in the node
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
abbrev torus : Grp (Over (Spec (.of A))) :=
  ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))

/-- The standard projective chart D_+(z_i).
Source: Stacks, projective-space charts
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
abbrev chart (i : ULift.{u} (Fin (n + 1))) : (projective A n).left.Opens :=
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (n + 1))) (R := A)
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule _ A) (MvPolynomial.X i)

/-- The actual regular function z_j/z_i in the standard chart.
Source: the graded-localization construction of Proj
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
def ratio (i j : ULift.{u} (Fin (n + 1))) : Γ((projective A n).left, chart A n i) :=
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (n + 1))) (R := A)
  Proj.awayToSection _ _ (MvPolynomial.awayXRatio A i j)

/-- The Laurent character t^m as a global section on the existing Hopf spectrum.
Source: the Laurent basis in the node
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
def character (m : Fin r → ℤ) : Γ((torus A r).X.left, ⊤) :=
  (Scheme.ΓSpecIso (.of (AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ))))).inv
    (AddMonoidAlgebra.single (ULift.up m) 1)

/-- The polynomial coaction, written in R[Z^r], canonically A[Z^r] tensor_A R.
It fixes A and sends z_i to t^(w_i) z_i by actual polynomial evaluation.
Source: the coordinate substitution in the node
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
def coaction (w : ULift.{u} (Fin (n + 1)) → (Fin r → ℤ)) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) A →ₐ[A]
      AddMonoidAlgebra (MvPolynomial (ULift.{u} (Fin (n + 1))) A)
        (ULift.{u} (Fin r → ℤ)) :=
  MvPolynomial.aeval (fun i ↦ AddMonoidAlgebra.single (ULift.up (w i)) (MvPolynomial.X i))

/-- Scheme-theoretic specification of the diagonal action: standard charts are preserved,
and on each chart z_j/z_i pulls back to t^(w_j-w_i) z_j/z_i. These formulas together
with being over Spec A determine the action, rather than merely its geometric points.
Source: the homogeneous coordinate coaction and its localization in the node
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
def IsDiagonal (w : ULift.{u} (Fin (n + 1)) → (Fin r → ℤ))
    (a : ModObj (torus A r).X (projective A n)) : Prop :=
  ∀ i : ULift.{u} (Fin (n + 1)),
    ∃ h : (snd (torus A r).X (projective A n)).left ⁻¹ᵁ chart A n i =
        a.smul.left ⁻¹ᵁ chart A n i,
      ∀ j : ULift.{u} (Fin (n + 1)),
        a.smul.left.appLE (chart A n i)
            ((snd (torus A r).X (projective A n)).left ⁻¹ᵁ chart A n i) h.le
            (ratio A n i j) =
          (fst (torus A r).X (projective A n)).left.appLE ⊤
              ((snd (torus A r).X (projective A n)).left ⁻¹ᵁ chart A n i)
              (by simp) (character A r (w j - w i)) *
            (snd (torus A r).X (projective A n)).left.app (chart A n i) (ratio A n i j)

/-- The existing reduced induced closed subscheme over Spec A, with no new choice of data.
Source: Stacks, Tags 01J3 and 01J4
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
def reducedClosed (C : TopologicalSpace.Closeds (projective A n).left) :
    Over (Spec (.of A)) :=
  Over.mk ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ (projective A n).hom)

/-- The canonical closed inclusion of the reduced induced subscheme.
Source: Stacks, Tags 01J3 and 01J4
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
def inclusion (C : TopologicalSpace.Closeds (projective A n).left) :
    reducedClosed A n C ⟶ projective A n :=
  Over.homMk (Scheme.IdealSheafData.vanishingIdeal C).subschemeι

/-- The degree-d boundary ideal, as the precise chartwise vanishing predicate. The fraction
is formed in homogeneous localization and then restricted by the actual closed immersion.
Source: the definition of I(B)_d in the node
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
def Vanishes (C : TopologicalSpace.Closeds (projective A n).left) (d : ℕ)
    (f : MvPolynomial (ULift.{u} (Fin (n + 1))) A) : Prop :=
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (n + 1))) (R := A)
  ∃ hf : f.IsHomogeneous d, ∀ i : ULift.{u} (Fin (n + 1)),
    (inclusion A n C).left.app (chart A n i)
      (Proj.awayToSection _ _ (HomogeneousLocalization.Away.mk _
        (MvPolynomial.X_mem_homogeneousSubmodule_one A i) d f (by simpa using hf))) = 0

/-- The reduced closure of the given locally closed immersion, defined by the existing
vanishing ideal of its topological closure.
Source: Stacks, Tags 01J3 and 01J4
(blueprint: lem-sfb-relative-diagonal-projective-boundary). -/
def closureSet {W : Over (Spec (.of A))} (j : W ⟶ projective A n) :
    TopologicalSpace.Closeds (projective A n).left :=
  TopologicalSpace.Closeds.closure (Set.range j.left)

/-- The reduced closure and boundary are invariant, and every weight component of a
homogeneous boundary equation still vanishes on the boundary, with the specified coaction.
Source: Stacks, Tags 034E, 056G, 01J3, 01J4 and 0356, and Laurent coefficient extraction
(blueprint: lem-sfb-relative-diagonal-projective-boundary).

Proof:
1. Factor the locally closed immersion through an open in which it is closed. Reduced
induced uniqueness identifies W with the open complement of the boundary in its reduced
closure (lem-weil-pbc-reduced-induced-closed-subscheme). The standard polynomial charts
show that closure and boundary are locally of finite type, hence locally Noetherian.
2. The torus projection onto either reduced closed scheme is a smooth Laurent extension.
By lem-trf-smooth-reduced-dense-pullback its source is reduced, and the pullback of W is
open dense in the pullback of its closure. This uses reducedness of these schemes, not A.
3. The product automorphism (t,x) ↦ (t,t*x), with inverse (t,x) ↦ (t,t^(-1)*x), preserves
T×W, hence its closure T×Z and its difference T×B. Closed-immersion base change identifies
these subsets with the corresponding fibre products.
4. Reduced-source factorization through the reduced closed schemes gives their actions
(lem-weil-pbc-reduced-source-factors-through-closed-subscheme). Monicity of closed
immersions gives the action identities and equivariance of all inclusions.
5. On B intersect D_+(z_i), the action sends z_j/z_i to t^(w_j-w_i) z_j/z_i.
Its Laurent coordinate ring has its free monomial basis over the chart quotient ring,
even when that ring has zero divisors. This is the affine fibre-product tensor description.
6. Pull back f/z_i^d=0 and compare the distinct Laurent coefficients t^(m-d*w_i).
Each coefficient f_m/z_i^d is zero. Repeat on every chart. Multiplicativity of the
coordinate coaction gives coaction(f_m)=t^m*f_m.
7. The same formulas apply to zero chart rings, empty W or B, d=0, r=0 and n=0.
No finite freeness of the vanishing submodule and no reducedness of A are used. -/
theorem relative_diagonal_projective_boundary [IsNoetherianRing A]
    (w : ULift.{u} (Fin (n + 1)) → (Fin r → ℤ))
    (a : ModObj (torus A r).X (projective A n)) (ha : IsDiagonal A r n w a)
    (W : Over (Spec (.of A))) [IsReduced W.left]
    (j : W ⟶ projective A n) [IsImmersion j.left]
    (aW : ModObj (torus A r).X W)
    (hj : aW.smul ≫ j = (𝟙 (torus A r).X ⊗ₘ j) ≫ a.smul) :
    ∃ (B : TopologicalSpace.Closeds (projective A n).left),
      (B : Set (projective A n).left) =
        closure (Set.range j.left) \ Set.range j.left ∧
      ∃ (aZ : ModObj (torus A r).X (reducedClosed A n (closureSet A n j)))
        (aB : ModObj (torus A r).X (reducedClosed A n B))
        (jW : W ⟶ reducedClosed A n (closureSet A n j))
        (jB : reducedClosed A n B ⟶ reducedClosed A n (closureSet A n j)),
        IsOpenImmersion jW.left ∧ IsClosedImmersion jB.left ∧
        jW ≫ inclusion A n (closureSet A n j) = j ∧
        jB ≫ inclusion A n (closureSet A n j) = inclusion A n B ∧
        Set.range jW.left = (Set.range jB.left)ᶜ ∧
        aZ.smul ≫ inclusion A n (closureSet A n j) =
          (𝟙 (torus A r).X ⊗ₘ inclusion A n (closureSet A n j)) ≫ a.smul ∧
        aB.smul ≫ inclusion A n B =
          (𝟙 (torus A r).X ⊗ₘ inclusion A n B) ≫ a.smul ∧
        aW.smul ≫ jW = (𝟙 (torus A r).X ⊗ₘ jW) ≫ aZ.smul ∧
        aB.smul ≫ jB = (𝟙 (torus A r).X ⊗ₘ jB) ≫ aZ.smul ∧
        ∀ (d : ℕ) (f : MvPolynomial (ULift.{u} (Fin (n + 1))) A),
          Vanishes A n B d f → ∀ m : Fin r → ℤ,
            Vanishes A n B d (MvPolynomial.weightedHomogeneousComponent w m f) ∧
            coaction A r n w (MvPolynomial.weightedHomogeneousComponent w m f) =
              AddMonoidAlgebra.single (ULift.up m)
                (MvPolynomial.weightedHomogeneousComponent w m f) := by
  sorry

end AlgebraicGeometry.RelativeDiagonalProjectiveBoundary
