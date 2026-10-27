module

public import Sheaf.RingTheory.SupportedHomogeneousDivision
public import Sheaf.RingTheory.FormalInitialDiagram
public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Exact block coefficient projection

Source: the full-column, simultaneous-earlier-test refinement of Bierstone--Milman,
Invent. Math. 128 (1997), Lemma 9.12, (9.13), Definition 9.14, pp.280--281;
ILO VIII 2.3.11--2.3.13 is the route reference.
(blueprint: lem-trf-exact-block-coefficient-projection).

Finite rows record the regular coefficient extractions of the given old projection.
Their entries are regular functions; the columns and all resulting series are full series.
Vertices are written in the ordered Taylor variables W,T. Original variables among W
are retained, and extra coefficient coordinates are padded by zero. Degree cutoffs index
blocks without requiring a nonempty previous block.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry.HilbertCoefficient

/-- Evaluate the finite coefficient rows of the old projection after coefficient transport.
Source: the regular coefficient extractions in BM 9.12/(9.13), refined simultaneously
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockOperator {t : ℕ} {R : Type u} [CommRing R]
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ R)
    {A : Type v} [CommRing A] (φ : R →+* A)
    (H : MvPowerSeries (Fin t) A) : MvPowerSeries (Fin t) A :=
  fun δ ↦ (K δ).sum fun η c ↦ φ c * MvPowerSeries.coeff η H

/-- Restrict an exponent to a set of transverse variables in their original order.
Source: the earlier coefficient tests in BM (9.13)
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockRestrictExponent {t : ℕ} (S : Finset (Fin t)) (δ : Fin t →₀ ℕ) :
    Fin t →₀ ℕ := δ.filter (· ∈ S)

/-- The full coefficient of the S-monomial eta, as a series in the other variables.
It is embedded back with zero S-exponents; it is never truncated.
Source: the earlier coefficient tests in BM (9.13)
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockSlice {t : ℕ} {A : Type u} [CommRing A]
    (S : Finset (Fin t)) (η : Fin t →₀ ℕ) (H : MvPowerSeries (Fin t) A) :
    MvPowerSeries (Fin t) A :=
  fun δ ↦ if blockRestrictExponent S δ = 0 then MvPowerSeries.coeff (δ + η) H else 0

/-- Transverse and coefficient parts of an exponent in the W-before-T ordering.
Source: the Taylor order in BM 9.12--9.14
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockTExponent {m t : ℕ} (δ : Fin (m + t) →₀ ℕ) : Fin t →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j ↦ δ (Fin.natAdd m j))

/-- Coefficient part of an exponent in the W-before-T ordering.
Source: the Taylor order in BM 9.12--9.14
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockWExponent {m t : ℕ} (δ : Fin (m + t) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j ↦ δ (Fin.castAdd t j))

/-- Flatten an iterated formal series without exchanging the coordinate order.
Source: the full Taylor expansions in BM 9.12--9.14
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockFlatten {m t : ℕ} {L : Type u} [CommRing L]
    (H : MvPowerSeries (Fin t) (MvPowerSeries (Fin m) L)) :
    MvPowerSeries (Fin (m + t)) L :=
  fun δ ↦ MvPowerSeries.coeff (blockWExponent δ)
    (MvPowerSeries.coeff (blockTExponent δ) H)

/-- Apply the genuine coefficient Taylor map to a full formal family.
Source: BM 9.12--9.14, regular Taylor coefficients
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockTaylor {m t : ℕ} {R L : Type u} [CommRing R] [CommRing L]
    (τ : R →+* MvPowerSeries (Fin m) L) (H : MvPowerSeries (Fin t) R) :
    MvPowerSeries (Fin (m + t)) L :=
  blockFlatten (MvPowerSeries.map τ H)

/-- Essential transverse variables in the degree prefix, retaining their original order.
Source: supported homogeneous division and BM (9.13)
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockVariables {m t s : ℕ} (α : Fin s → Fin (m + t) →₀ ℕ) (h : ℕ) :
    Finset (Fin t) := by
  classical
  exact Finset.univ.filter fun j ↦ ∃ i : Fin s, (α i).degree ≤ h ∧
    blockTExponent (α i) j ≠ 0

/-- A forbidden prefix exponent, including the bounded degree and essential support.
Source: the prefix diagrams and tests in BM (9.13)
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockForbidden {m t s : ℕ} (α : Fin s → Fin (m + t) →₀ ℕ)
    (Q h : ℕ) (η : Fin t →₀ ℕ) : Prop :=
  η.degree ≤ Q ∧ blockRestrictExponent (blockVariables α h) η = η ∧
    η ∈ MonomialDiagram.generated
      (fun i : {i : Fin s // (α i).degree ≤ h} ↦ blockTExponent (α i.val))

/-- Passing all tests strictly before a degree block.
Source: the simultaneous earlier tests in the refinement of BM (9.13)
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockOldKernel {m t s : ℕ} {A : Type u} [CommRing A]
    (α : Fin s → Fin (m + t) →₀ ℕ) (Q d : ℕ)
    (H : MvPowerSeries (Fin t) A) : Prop :=
  ∀ h : ℕ, h < d → ∀ η : Fin t →₀ ℕ, blockForbidden α Q h η →
    blockSlice (blockVariables α h) η H = 0

/-- A first monomial passes the old tests if none of its prefix restrictions is forbidden.
Source: leading-exponent invariant of BM 9.12/(9.13)
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockOldMonomial {m t s : ℕ} (α : Fin s → Fin (m + t) →₀ ℕ)
    (Q d : ℕ) (μ : Fin (m + t) →₀ ℕ) : Prop :=
  ∀ h : ℕ, h < d → ¬ blockForbidden α Q h
    (blockRestrictExponent (blockVariables α h) (blockTExponent μ))

/-- The new finite coefficient-test set, subtracting the extended previous prefix diagram.
Source: the set E in the full-column refinement of BM (9.13)
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockNewExponent {m t s : ℕ} (α : Fin s → Fin (m + t) →₀ ℕ)
    (Q d : ℕ) (γ : Fin t →₀ ℕ) : Prop :=
  γ.degree ≤ Q ∧
    (∃ i : Fin s, (α i).degree ≤ d ∧ blockTExponent (α i) ≤ γ) ∧
    ¬ ∃ i : Fin s, (α i).degree < d ∧ blockTExponent (α i) ≤ γ

/-- The prescribed full projected correction column. The finite sum selects the unique
first-dividing vertex; no choice of a formal series or truncation occurs.
Source: BM 9.12--9.14, with simultaneous old tests
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockColumn {m t s : ℕ} {R : Type u} [CommRing R]
    (α : Fin s → Fin (m + t) →₀ ℕ) (d : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) R)
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ R) (γ : Fin t →₀ ℕ) :
    MvPowerSeries (Fin t) R := by
  classical
  exact ∑ i : Fin s,
    if (α i).degree = d ∧ blockTExponent (α i) ≤ γ ∧
        γ - blockTExponent (α i) ∈
          MonomialDiagram.quotientSupport (fun j ↦ blockTExponent (α j)) i then
      blockOperator K (RingHom.id R)
        (MvPowerSeries.monomial (γ - blockTExponent (α i)) 1 * f i)
    else 0

/-- The coefficient matrix of the actual full columns.
Source: B_eta,gamma in BM (9.13), with projected columns
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockMatrix {m t s : ℕ} {R : Type u} [CommRing R]
    (α : Fin s → Fin (m + t) →₀ ℕ) (d : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) R)
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ R) (E : Finset (Fin t →₀ ℕ)) :
    Matrix E E R :=
  fun η γ ↦ MvPowerSeries.coeff η.val (blockColumn α d f K γ.val)

/-- The prescribed projection after transport to any coefficient ring. On the determinant
open the nonsingular inverse is the adjugate divided by the same single determinant.
Source: BM Definition 9.14, with full projected correction columns
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockProjection {m t s : ℕ} {R : Type u} [CommRing R]
    (α : Fin s → Fin (m + t) →₀ ℕ) (d : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) R)
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ R) (E : Finset (Fin t →₀ ℕ))
    {A : Type v} [CommRing A] (φ : R →+* A)
    (H : MvPowerSeries (Fin t) A) : MvPowerSeries (Fin t) A := by
  classical
  exact blockOperator K φ H - ∑ γ : E,
    MvPowerSeries.C
      ((@Inv.inv (Matrix E E A) (Matrix.inv (n := E) (α := A))
        (fun η γ : E ↦ φ (blockMatrix α d f K E η γ))).mulVec
          (fun η : E ↦ MvPowerSeries.coeff η.val (blockOperator K φ H)) γ) *
      MvPowerSeries.map φ (blockColumn α d f K γ.val)

/-- The retained prefix and projected later generators.
Source: BM Definition 9.14, prefix-preserving replacement
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockReplacement {m t s : ℕ} {R : Type u} [CommRing R]
    (α : Fin s → Fin (m + t) →₀ ℕ) (d : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) R)
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ R) (E : Finset (Fin t →₀ ℕ))
    {A : Type v} [CommRing A] (φ : R →+* A) (i : Fin s) :
    MvPowerSeries (Fin t) A :=
  if (α i).degree ≤ d then MvPowerSeries.map φ (f i)
  else blockProjection α d f K E φ (MvPowerSeries.map φ (f i))

/-- The geometric and old-projection hypotheses, with the given regular operator recorded
coefficient by coefficient. The prefix diagram uses the existing supported-division notions.
Source: BM 9.12--9.14 and the simultaneous-old-tests refinement
(blueprint: lem-trf-exact-block-coefficient-projection). -/
structure ExactBlockInput {k : Type u} [Field k] [CharZero k]
    (C : Scheme.{u}) (m t s Q d : ℕ)
    (α : Fin s → Fin (m + t) →₀ ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(C, ⊤))
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ Γ(C, ⊤)) where
  affine : IsAffine C
  coordinates : MvPolynomial (Fin m) k →+* Γ(C, ⊤)
  etale : Etale (C.toSpecΓ ≫ Spec.map (CommRingCat.ofHom coordinates))
  smooth : Smooth (C.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (coordinates.comp MvPolynomial.C)))
  finiteType : LocallyOfFiniteType (C.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (coordinates.comp MvPolynomial.C))) ∧
    QuasiCompact (C.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (coordinates.comp MvPolynomial.C)))
  center : C
  taylor : Γ(C, ⊤) →+* MvPowerSeries (Fin m) (C.residueField center)
  taylor_spec : isTaylorMap coordinates (C.Γevaluation center).hom taylor
  originalVariables : ℕ
  originalCoordinates : Fin originalVariables ↪o Fin (m + t)
  originalVertices : Fin s → Fin originalVariables →₀ ℕ
  vertex_eq : ∀ i : Fin s, α i = Finsupp.mapDomain originalCoordinates (originalVertices i)
  monotone : MonomialDiagram.IsMonotone (MonomialDiagram.generated originalVertices)
  vertices : MonomialDiagram.IsOrderedVertexFamily
    (MonomialDiagram.generated originalVertices) originalVertices
  block_exists : ∃ i : Fin s, (α i).degree = d
  prefix_has_no_W : ∀ i : Fin s, (α i).degree ≤ d → blockWExponent (α i) = 0
  essential_T : ∀ j : Fin t, j ∈ blockVariables α d
  normalized : ∀ i : Fin s,
    MonomialDiagram.IsFirstExponent (blockTaylor taylor (f i)) (α i) ∧
      MvPowerSeries.coeff (α i) (blockTaylor taylor (f i)) = 1
  old_image : ∀ H : MvPowerSeries (Fin t) Γ(C, ⊤),
    blockOldKernel α Q d (blockOperator K (RingHom.id Γ(C, ⊤)) H)
  old_fixed : ∀ H : MvPowerSeries (Fin t) Γ(C, ⊤), blockOldKernel α Q d H →
    blockOperator K (RingHom.id Γ(C, ⊤)) H = H
  complement_linear : ∀ G H : MvPowerSeries (Fin t) Γ(C, ⊤),
    (∀ η : Fin t →₀ ℕ, MvPowerSeries.coeff η G ≠ 0 →
      ∀ h : ℕ, h < d → blockRestrictExponent (blockVariables α h) η = 0) →
    blockOperator K (RingHom.id Γ(C, ⊤)) (G * H) =
      G * blockOperator K (RingHom.id Γ(C, ⊤)) H
  fixes_later : ∀ i : Fin s, d ≤ (α i).degree →
    blockOperator K (RingHom.id Γ(C, ⊤)) (f i) = f i
  old_ideal : ∀ H : MvPowerSeries (Fin t) Γ(C, ⊤),
    blockOperator K (RingHom.id Γ(C, ⊤)) H - H ∈
      Ideal.span {F | ∃ i : Fin s, (α i).degree < d ∧ F = f i}
  old_first : ∀ H : MvPowerSeries (Fin t) (MvPowerSeries (Fin m)
      (C.residueField center)), ∀ μ : Fin (m + t) →₀ ℕ,
    MonomialDiagram.IsFirstExponent (blockFlatten H) μ → blockOldMonomial α Q d μ →
    MonomialDiagram.IsFirstExponent (blockFlatten (blockOperator K taylor H)) μ

/-- The single determinant open, defined before any coefficient projection is evaluated.
Source: BM (9.13), full-column matrix
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def exactBlockOpen {m t s : ℕ} {C : Scheme.{u}}
    (α : Fin s → Fin (m + t) →₀ ℕ) (d : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(C, ⊤))
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ Γ(C, ⊤))
    (E : Finset (Fin t →₀ ℕ)) : C.Opens := by
  classical
  exact C.basicOpen (Matrix.det (blockMatrix α d f K E))

/-- Canonical restriction of regular coefficients from C to an open V.
Source: regularity on the single determinant open in BM (9.13)
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def blockRestriction (C : Scheme.{u}) (V : C.Opens) : Γ(C, ⊤) →+* Γ(C, V) :=
  (C.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom

/-- The projection, ideal, and unchanged derivative identities over a coefficient ring.
Source: BM 9.12--9.14, full-column simultaneous-tests refinement
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def ExactBlockOver {m t s : ℕ} {R : Type u} [CommRing R]
    (α : Fin s → Fin (m + t) →₀ ℕ) (Q d : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) R)
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ R)
    (E : Finset (Fin t →₀ ℕ)) {B : Type v} [CommRing B] (φ : R →+* B) : Prop :=
  IsUnit (Matrix.det (fun η γ : E ↦ φ (blockMatrix α d f K E η γ))) ∧
  (∀ H G : MvPowerSeries (Fin t) B,
    blockProjection α d f K E φ (H + G) =
      blockProjection α d f K E φ H + blockProjection α d f K E φ G) ∧
  (∀ (r : B) (H : MvPowerSeries (Fin t) B),
    blockProjection α d f K E φ (r • H) = r • blockProjection α d f K E φ H) ∧
  (∀ H : MvPowerSeries (Fin t) B,
    blockOldKernel α Q d (blockProjection α d f K E φ H) ∧
    ∀ η : Fin t →₀ ℕ, blockForbidden α Q d η →
      MvPowerSeries.coeff η (blockProjection α d f K E φ H) = 0) ∧
  (∀ H : MvPowerSeries (Fin t) B, blockOldKernel α Q d H →
    (∀ η : Fin t →₀ ℕ, blockForbidden α Q d η → MvPowerSeries.coeff η H = 0) →
    blockProjection α d f K E φ H = H) ∧
  (∀ H : MvPowerSeries (Fin t) B,
    blockProjection α d f K E φ (blockProjection α d f K E φ H) =
      blockProjection α d f K E φ H) ∧
  (∀ H : MvPowerSeries (Fin t) B, blockProjection α d f K E φ H - H ∈
    Ideal.span {F | ∃ i : Fin s, (α i).degree ≤ d ∧ F = MvPowerSeries.map φ (f i)}) ∧
  Ideal.span (Set.range (blockReplacement α d f K E φ)) =
    Ideal.span (Set.range fun i : Fin s ↦ MvPowerSeries.map φ (f i)) ∧
  (∀ (i : Fin s) (β : Fin t →₀ ℕ), (α i).degree ≤ d →
    iteratedPartial β (blockReplacement α d f K E φ i) =
      iteratedPartial β (MvPowerSeries.map φ (f i))) ∧
  (∀ (r : ℕ) (pick : Fin r → Fin s) (β : Fin r → Fin t →₀ ℕ)
      (coordIndex : Fin r → Fin t), (∀ j : Fin r, (α (pick j)).degree < d) →
    (fun i j : Fin r ↦ MvPowerSeries.constantCoeff
      (MvPowerSeries.pderiv B (coordIndex j)
        (iteratedPartial (β i) (blockReplacement α d f K E φ (pick i))))) =
    (fun i j : Fin r ↦ MvPowerSeries.constantCoeff
      (MvPowerSeries.pderiv B (coordIndex j)
        (iteratedPartial (β i) (MvPowerSeries.map φ (f (pick i)))))))

/-- Regularity and the identities on the specified open, without a further shrinking.
Source: BM (9.13)--(9.14), full-column simultaneous-tests refinement
(blueprint: lem-trf-exact-block-coefficient-projection). -/
def ExactBlockOnOpen {m t s : ℕ} {C : Scheme.{u}}
    (α : Fin s → Fin (m + t) →₀ ℕ) (Q d : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(C, ⊤))
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ Γ(C, ⊤))
    (E : Finset (Fin t →₀ ℕ)) (V : C.Opens) : Prop :=
  (∃ L : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ Γ(C, V),
    ∀ H : MvPowerSeries (Fin t) Γ(C, V),
      blockOperator L (RingHom.id Γ(C, V)) H =
        blockProjection α d f K E (blockRestriction C V) H) ∧
  ExactBlockOver α Q d f K E (blockRestriction C V)

/-- Exact coefficient elimination by full projected columns on one determinant open.

Source: BM Lemma 9.12, (9.13), Definition 9.14, pp.280--281; the agent refinement
retains simultaneous earlier tests. ILO VIII 2.3.11--2.3.13 is the route reference.
(blueprint: lem-trf-exact-block-coefficient-projection).

Proof plan from the accepted node:
1. Assign each new exponent to its first dividing vertex, necessarily in the new block;
its monomial passes every previous test (supported homogeneous division).
2. Multiply the normalized full generator by that monomial and apply the old projection.
Its first exponent is unchanged; its old tests vanish and its difference is in the old ideal.
3. Order E by degree lexicographic order. B(a) is triangular with diagonal one; invert
B on D(det B) using the adjugate identity, including the empty matrix.
4. The finite solve v(PH)=v(P^-H)-BB^{-1}v(P^-H)=0 kills the new tests. Full correction
columns and the old image lie in every previous kernel. On the common kernel the formula
is the identity. Coefficient rows prove regularity and linearity on this single open.
5. The difference from the identity is a combination of unchanged prefix generators.
6. Apply lem-trf-shift-filtered-matrix-inverse to the Taylor coefficient matrix, whose
columns start at (0,gamma). Every contributing correction term is strictly after the first
monomial when it passes the tests, so that first exponent survives without tail truncation.
7. Incomparability of the vertices supplies this hypothesis for the later generators.
Their replacements differ by prefix-generator combinations, hence give the same ideal;
all old generators remain literally equal, so every earlier derivative equation and its
Jacobian is unchanged. These identities persist in every Taylor ring at every point.
8. For E empty the finite sum vanishes. Every formula commutes with field extension;
the leading coefficients equal to one stay one. This includes the first block and t=0.
-/
theorem exactBlockCoefficientProjection {k : Type u} [Field k] [CharZero k]
    {C : Scheme.{u}} {m t s Q d : ℕ}
    (α : Fin s → Fin (m + t) →₀ ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(C, ⊤))
    (K : (Fin t →₀ ℕ) → (Fin t →₀ ℕ) →₀ Γ(C, ⊤))
    (A : ExactBlockInput (k := k) C m t s Q d α f K)
    (E : Finset (Fin t →₀ ℕ)) (hE : ∀ γ : Fin t →₀ ℕ, γ ∈ E ↔ blockNewExponent α Q d γ) :
    (∀ γ : E, (∃! p : Fin s × (Fin t →₀ ℕ),
      (α p.1).degree = d ∧ p.2 ∈
        MonomialDiagram.quotientSupport (fun j ↦ blockTExponent (α j)) p.1 ∧
      γ.val = blockTExponent (α p.1) + p.2) ∧
      ∀ p : Fin s × (Fin t →₀ ℕ), (α p.1).degree = d →
        p.2 ∈ MonomialDiagram.quotientSupport (fun j ↦ blockTExponent (α j)) p.1 →
        γ.val = blockTExponent (α p.1) + p.2 →
        blockColumn α d f K γ.val = blockOperator K (RingHom.id Γ(C, ⊤))
          (MvPowerSeries.monomial p.2 1 * f p.1)) ∧
    (∀ γ : E, blockOldKernel α Q d (blockColumn α d f K γ.val) ∧
      (∃ p : Fin s × (Fin t →₀ ℕ), (α p.1).degree = d ∧
        γ.val = blockTExponent (α p.1) + p.2 ∧
        blockColumn α d f K γ.val - MvPowerSeries.monomial p.2 1 * f p.1 ∈
          Ideal.span {F | ∃ i : Fin s, (α i).degree < d ∧ F = f i}) ∧
      MonomialDiagram.IsFirstExponent (blockTaylor A.taylor (blockColumn α d f K γ.val))
        (Finsupp.mapDomain (Fin.natAdd m) γ.val)) ∧
    (∀ η γ : E, Finsupp.DegLex (· < ·) (· < ·) η.val γ.val →
      C.Γevaluation A.center (blockMatrix α d f K E η γ) = 0) ∧
    (∀ γ : E, C.Γevaluation A.center (blockMatrix α d f K E γ γ) = 1) ∧
    A.center ∈ exactBlockOpen α d f K E ∧
    ExactBlockOnOpen α Q d f K E (exactBlockOpen α d f K E) ∧
    (∀ (L : Type (max u v)) [Field L] (ι : C.residueField A.center →+* L),
      ExactBlockOver α Q d f K E ((MvPowerSeries.map ι).comp A.taylor) ∧
      (∀ H : MvPowerSeries (Fin t) (MvPowerSeries (Fin m) L),
        ∀ μ : Fin (m + t) →₀ ℕ,
        MonomialDiagram.IsFirstExponent (blockFlatten H) μ →
        blockOldMonomial α Q d μ → ¬ blockForbidden α Q d (blockTExponent μ) →
        MonomialDiagram.IsFirstExponent
          (blockFlatten (blockProjection α d f K E ((MvPowerSeries.map ι).comp A.taylor) H))
          μ) ∧
      (∀ i : Fin s, MonomialDiagram.IsFirstExponent
        (blockFlatten (blockReplacement α d f K E ((MvPowerSeries.map ι).comp A.taylor) i))
        (α i))) ∧
    (∀ (V : C.Opens) (b : C) (hb : b ∈ V), V ≤ exactBlockOpen α d f K E →
      ∀ (L : Type (max u v)) [Field L] (ι : C.residueField b →+* L)
        (τ : Γ(C, V) →+* MvPowerSeries (Fin m) L),
      (∀ r : Γ(C, V), MvPowerSeries.constantCoeff (τ r) =
        ι ((C.residue b) (C.presheaf.germ V b hb r))) →
      (∀ z : k, τ (blockRestriction C V (A.coordinates (MvPolynomial.C z))) =
        MvPowerSeries.C (ι (C.Γevaluation b (A.coordinates (MvPolynomial.C z))))) →
      (∀ j : Fin m, τ (blockRestriction C V (A.coordinates (MvPolynomial.X j))) =
        MvPowerSeries.C (ι (C.Γevaluation b (A.coordinates (MvPolynomial.X j)))) +
          MvPowerSeries.X j) →
      ExactBlockOver α Q d f K E (ι.comp (C.Γevaluation b).hom) ∧
        ExactBlockOver α Q d f K E (τ.comp (blockRestriction C V))) ∧
    (E = ∅ → ∀ {B : Type u} [CommRing B] (φ : Γ(C, ⊤) →+* B)
      (H : MvPowerSeries (Fin t) B), blockProjection α d f K E φ H = blockOperator K φ H) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
