/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.SnapperNumericalPolynomial

/-! # Hilbert polynomials in flat projective families

Source: Stacks Project, Tags 0B9T, 08AC, 08AE
(blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality).

Coordinate pieces use the homogeneous ideal of equations vanishing on every standard
chart. Thus their construction also applies to the empty closed subscheme. The auxiliary
definitions make the eventual-coordinate-dimension clause explicit, without selecting a
polynomial from an unproved existence assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Filter

noncomputable section

namespace AlgebraicGeometry.ProjectiveHilbertPolynomial

/-- The degree-d equations: homogeneous polynomials whose dehomogenizations restrict to
zero on each standard chart of the embedded scheme. The span expresses their k-submodule
without postponing any construction. The vanishing condition is itself linear, so the
span introduces no additional equations.
Source: Stacks, Tag 03GL (blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality). -/
def equations (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))) (d : ℕ) :
    Submodule k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k d) :=
  Submodule.span k {p | ∀ a : ULift.{u} (Fin (n + 1)),
    i.app (ProjectiveSpace.standardOpen _ (Spec (.of k)) a)
      (ProjectiveSpace.chartRingEquiv _ k a (MvPolynomial.dehomogenizeX k a p.val)) = 0}

/-- The homogeneous degree-d piece of the coordinate ring of the embedded scheme.
Source: Stacks, Tag 03GL (blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality). -/
def coordinatePiece (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))) (d : ℕ) : Type u :=
  (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k d) ⧸ equations k n i d

/-- The coordinate Hilbert function, defined by the actual quotient vector spaces.
Source: Stacks, Tag 08AE (blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality). -/
def coordinateDimension (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))) (d : ℕ) : ℕ :=
  Module.finrank k
    ((MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k d) ⧸ equations k n i d)

/-- Being the polynomial eventually equal to the dimensions of homogeneous pieces.
Source: Stacks, Tags 08AC, 08AE
(blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality). -/
def IsCoordinatePolynomial (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))) (P : Polynomial ℚ) : Prop :=
  ∀ᶠ d : ℕ in atTop, P.eval (d : ℚ) = (coordinateDimension k n i d : ℚ)

/-- The induced embedding after any base change, from the projective-space pullback
universal property; it is not an arbitrary map to projective space.
Source: Stacks, Tag 01W6
(blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality). -/
def baseChangeEmbedding {T Z T' : Scheme.{u}} (n : ℕ)
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (h : T' ⟶ T) :
    pullback (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)) h ⟶
      ℙ(ULift.{u} (Fin (n + 1)); T') :=
  ProjectiveSpace.liftBaseChange
    (pullback.snd (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)) h)
    (pullback.fst (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)) h ≫ i)
    ((pullback.condition).symm.trans (Category.assoc _ _ _).symm)

/-- The geometric point defined by the chosen algebraic closure of the residue field.
Source: Stacks, Tag 02H5
(blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality). -/
def geometricPoint (T : Scheme.{u}) (t : T) :
    Spec (.of (AlgebraicClosure (T.residueField t))) ⟶ T :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t)))) ≫
      T.fromSpecResidueField t

/-- Euler characteristic of the restricted twist, using the embedding's structural
morphism to give the scheme its field action, and the recorded tensor pullback.
Source: Stacks, Tags 08AC, 08AE
(blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality). -/
def twistEuler (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))) (d : ℤ) : ℤ :=
  letI : X.Over (Spec (.of k)) := ⟨i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ _)⟩
  ((Scheme.Modules.tensorPullback i).obj
    (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)).eulerChar k

/-- The fibre Hilbert polynomials exist uniquely, are numerical, have degree at most n,
give every integer twist Euler characteristic, vary locally constantly, and commute with
arbitrary base change. The zero-polynomial criterion includes empty fibres.
Source: Stacks, Tags 0B9T, 08AC, 08AE
(blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality).

Proof (for stage 3):
1. The embedding makes the structural morphism projective and proper
   (def-pc-projective-morphism, lem-pc-projective-proper). Field fibres are Noetherian
   (lem-weil-pbc-finite-type-over-noetherian), and their structure sheaves are coherent
   (pqf-lem-coherent-ft-locnoeth). Closed embeddings survive base change
   (lem-weil-pbc-closed-immersion-base-change).
2. The twists of def-pc-projective-space-twist have rank-one local bases and transition
   functions (z_i/z_j)^d. Tensor pullback preserves these bases and functions. The stalks
   are copies of structure stalks, so the twists are finitely presented and base flat.
3. Apply lem-sfb-proper-flat-sheaf-euler-local-constancy to every integer twist. This gives
   locally constant Euler functions, invariant under arbitrary base change, in particular
   passage to geometric field points.
4. Apply lem-sc-snapper-numerical-polynomial to the structure module and O(1). Its signed
   powers are O(d). The homogeneous ideal theorem
   lem-sfb-projective-closed-subscheme-homogeneous-ideal and the comparison
   lem-sfb-projective-coordinate-ring-euler-polynomial identify the eventual coordinate
   dimensions with this numerical polynomial. Infinite-root uniqueness identifies it
   independently of the homogeneous coordinate presentation.
5. Coordinate dimensions are between zero and binomial(d+n,n). The leading term of a
   nonzero eventual polynomial is positive, so this growth bound forces degree at most n.
6. An empty fibre has zero cohomology. Conversely zero polynomial forces every sufficiently
   high coordinate piece to vanish, hence a power of each coordinate vanishes. All standard
   Proj charts are empty (def-pc-proj), so the fibre is empty.
7. Intersect neighbourhoods where the n+1 Euler functions at 0,...,n are constant. Their
   values determine polynomials of degree at most n, proving local constancy also at zero.
8. Identify the relative-Proj projective space with its polynomial-coordinate model by
   their identical standard affine charts; this supplies the over-isomorphism e.
   For h:T'→T compose the geometric point of T' with h. Fibre-product pasting
   (def-pc-fibre-product) identifies its pullback with the iterated geometric fibre. Step 3
   identifies all integer Euler values, so uniqueness identifies the polynomials. -/
theorem flat_projective_hilbert_polynomial_locality {T Z : Scheme.{u}} (n : ℕ)
    (i : Z ⟶ RelativeProjectiveSpace.scheme T n) [IsClosedImmersion i]
    [Flat (i ≫ RelativeProjectiveSpace.π T n)]
    [LocallyOfFinitePresentation (i ≫ RelativeProjectiveSpace.π T n)]
    [QuasiCompact (i ≫ RelativeProjectiveSpace.π T n)]
    [QuasiSeparated (i ≫ RelativeProjectiveSpace.π T n)] :
    ∃ P : T → Polynomial ℚ, IsLocallyConstant P ∧
      ∃ e : RelativeProjectiveSpace.scheme T n ≅ ℙ(ULift.{u} (Fin (n + 1)); T),
        e.hom ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T) = RelativeProjectiveSpace.π T n ∧
      (∀ t : T,
        (∀ Q : Polynomial ℚ,
          IsCoordinatePolynomial (AlgebraicClosure (T.residueField t)) n
            (baseChangeEmbedding n (i ≫ e.hom) (geometricPoint T t)) Q ↔ Q = P t) ∧
        (∀ d : ℤ, ∃ z : ℤ, (P t).eval (d : ℚ) = (z : ℚ)) ∧
        ((P t) ≠ 0 → (P t).natDegree ≤ n) ∧
        (∀ d : ℤ, (P t).eval (d : ℚ) =
          (twistEuler (AlgebraicClosure (T.residueField t)) n
            (baseChangeEmbedding n (i ≫ e.hom) (geometricPoint T t)) d : ℚ)) ∧
        (P t = 0 ↔ IsEmpty ↥
          (pullback ((i ≫ e.hom) ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)) (geometricPoint T t)))) ∧
      (∀ (T' : Scheme.{u}) (h : T' ⟶ T) (t' : T') (Q : Polynomial ℚ),
        IsCoordinatePolynomial (AlgebraicClosure (T'.residueField t')) n
          (baseChangeEmbedding n (baseChangeEmbedding n (i ≫ e.hom) h) (geometricPoint T' t')) Q ↔
            Q = P (h t')) := by
  sorry

/-- Over any field, the coordinate Hilbert polynomial exists uniquely and vanishes
exactly for the empty projective scheme, without reducedness or nonemptiness hypotheses.
Source: Stacks, Tags 08AC, 08AE
(blueprint: lem-sfb-flat-projective-hilbert-polynomial-locality).

Proof (for stage 3): use the homogeneous-ideal presentation of
lem-sfb-projective-closed-subscheme-homogeneous-ideal and the Euler comparison of
lem-sfb-projective-coordinate-ring-euler-polynomial. Snapper's theorem gives the numerical
polynomial at every integer. The monomial count bounds its degree by n. Uniqueness follows
from infinitely many eventual values. If the polynomial is zero, all sufficiently high
coordinate pieces vanish, so each coordinate has a zero power and every standard Proj
chart is empty. Conversely the empty scheme has zero coordinate pieces and cohomology.
This is precisely the field argument in steps 1, 4, 5, 6 of the node's proof. -/
theorem projective_field_hilbert_polynomial (k : Type u) [Field k] (n : ℕ)
    {X : Scheme.{u}} (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)))
    [IsClosedImmersion i] :
    ∃ P : Polynomial ℚ,
      (∀ Q : Polynomial ℚ, IsCoordinatePolynomial k n i Q ↔ Q = P) ∧
      (∀ d : ℤ, ∃ z : ℤ, P.eval (d : ℚ) = (z : ℚ)) ∧
      (P ≠ 0 → P.natDegree ≤ n) ∧
      (∀ d : ℤ, P.eval (d : ℚ) = (twistEuler k n i d : ℚ)) ∧
      (P = 0 ↔ IsEmpty X) := by
  sorry

end AlgebraicGeometry.ProjectiveHilbertPolynomial
