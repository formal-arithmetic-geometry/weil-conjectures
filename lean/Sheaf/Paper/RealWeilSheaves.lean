/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q159
-/
module

public import Sheaf.Paper.RealSheavesSetup
public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup
public import Mathlib.CategoryTheory.Localization.Construction
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import Sheaf.RepresentationTheory.ProfiniteStableLattice
import WeilConjectures.RepresentationTheory.IntegralModel

/-! # Weil sheaves and representations on the real-sheaf curve

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-weil;
Deligne, Weil II (1.1.1), (1.1.10)--(1.1.13), and Stanford L19, pp. 3--5
(blueprint: sk-d-real-weil).

The Weil group, its topology, local Frobenius, lisse representations and actual
etale lisse Weil pairs are the existing dependency declarations. The additional
constructible objects retain one global compatible system and one global rational
Weil isomorphism. A single finite stratification of the arithmetic curve trivializes
its integral model stratumwise. The Weil isomorphism need not preserve that model.

## Main definitions and statements

* `RealSheaves.ConstructibleWeilSheaf`: finite-coefficient representatives of global pairs.
* `AlgebraicGeometry.WeilGroup.isLisse_iff_finiteModel`: the finite-model criterion,
  with a geometric stable lattice and no condition on its degree-one operator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace RealSheaves

/-- Reuse the finite-field datum with precisely the fields already fixed in Setup.
Source: blueprint sk-d-real-weil, standing setup (blueprint: sk-d-real-weil). -/
def Setup.weilFieldDatum (D : Setup.{u, v}) : WeilConjectures.FiniteFieldDatum.{u} where
  p := D.p
  a := D.a
  q := D.q
  prime := D.p_prime
  exponent_pos := D.a_pos
  cardinality_eq := rfl
  k₀ := D.k₀
  card_base := Nat.card_eq_fintype_card.trans D.card_eq
  k := D.k

/-- Geometric Galois Frobenius on the actual chosen geometric fibre, with inverse
q-power action on the closure. Source: Weil II (1.1.7), (1.1.10)
(blueprint: sk-d-real-weil). -/
def Setup.weilFrobenius (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) :
    D.geometricCurve C₀ ≅ D.geometricCurve C₀ :=
  @WeilConjectures.FiniteFieldDatum.geometricFrobenius D.weilFieldDatum
    (Over.mk (C₀ ↘ Spec (.of D.k₀))) hC.2.2.2.1 hC.2.2.2.2.1

/-- Scalar localization of global inverse systems: invert multiplication by powers
of the uniformizer. The zero and uniformizer-torsion objects are thereby killed;
no integral Frobenius-stable lattice is imposed.
Source: Weil II (1.1.1) c) (blueprint: sk-d-real-weil). -/
def weilDiagramDenominators (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) : MorphismProperty (Scheme.AdicIntegralDiagramOfUniverses l E Y) :=
  fun F G f ↦ ∃ (e : F ≅ G) (n : ℕ),
    f = Padic.coefficientExtensionUniformizer l E ^ n • e.hom

/-- The rational category of global systems, formed before restricting to strata.
Objects are unchanged and all uniformizer powers act invertibly on morphisms.
Source: Weil II (1.1.1) c) (blueprint: sk-d-real-weil). -/
abbrev WeilRationalDiagrams (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) := (weilDiagramDenominators l E Y).Localization

/-- Restrict the entire inverse system along a scheme morphism, including its
transition maps, using the existing etale inverse-image functor.
Source: Weil II (1.1.1) b), (1.1.12) (blueprint: sk-d-real-weil). -/
def weilDiagramPullback (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y Z : Scheme.{u}} (f : Z ⟶ Y) :
    Scheme.AdicIntegralDiagramOfUniverses l E Y ⥤
      Scheme.AdicIntegralDiagramOfUniverses l E Z :=
  (Functor.whiskeringRight _ _ _).obj
    (Etale.upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) f)

/-- A single global system is adic and lisse of finite rank on the geometric fibres
of one finite locally closed stratification of C_0. In particular the transition
maps induce the stipulated reduction isomorphisms on every geometric stalk.
Source: Weil II (1.1.1) b), (1.1.12) (blueprint: sk-d-real-weil). -/
def IsConstructibleWeilDiagram (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))]
    (E : Type u) [Field E] [Algebra ℚ_[D.l] E] [FiniteDimensional ℚ_[D.l] E]
    (F : Scheme.AdicIntegralDiagramOfUniverses D.l E (D.geometricCurve C₀)) : Prop :=
  ∃ S : C₀.FiniteLocallyClosedStratification, ∀ i : Fin S.n,
    Scheme.IsLisseIntegralDiagramOfUniverses D.l E
      (pullback (S.immersion i)
        (pullback.fst (C₀ ↘ Spec (.of D.k₀))
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
      ((weilDiagramPullback D.l E
        (pullback.snd (S.immersion i)
          (pullback.fst (C₀ ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))).obj F)

/-- A global constructible adic Weil pair, presented at one common finite coefficient
field containing the sheaf and its Weil isomorphism. The latter is in the rational
category, so its integral model is not required to be Frobenius-stable. The witness
of constructibility restricts this global object; it does not supply independent
objects on the strata. Small coefficient models allow arbitrary closure universe v.
Source: Weil II (1.1.1) b)--d), (1.1.10)(i), (1.1.12)
(blueprint: sk-d-real-weil). -/
structure ConstructibleWeilSheaf (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) where
  /-- A common finite field of definition inside the fixed coefficient closure. -/
  coefficient : WeilConjectures.AlgebraicallyClosedCoefficients.Index D.l D.Qbar
  /-- One global compatible system, using the canonical small coefficient model. -/
  integral : Scheme.AdicIntegralDiagramOfUniverses D.l
    (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} D.l D.Qbar coefficient)
    (D.geometricCurve C₀)
  /-- One finite stratification of C_0 makes its geometric restrictions lisse. -/
  constructible : IsConstructibleWeilDiagram D C₀
    (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} D.l D.Qbar coefficient)
    integral
  /-- The global isomorphism Phi_C^* F ≅ F, after killing uniformizer torsion. -/
  frobenius :
    (weilDiagramDenominators D.l
      (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} D.l D.Qbar coefficient)
      (D.geometricCurve C₀)).Q.obj
        ((weilDiagramPullback D.l
          (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u}
            D.l D.Qbar coefficient) (D.weilFrobenius C₀ hC).hom).obj integral) ≅
    (weilDiagramDenominators D.l
      (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} D.l D.Qbar coefficient)
      (D.geometricCurve C₀)).Q.obj integral

end RealSheaves

namespace AlgebraicGeometry.WeilGroup

/-- Lissity in every basis, with the spectral l-adic topology on the fixed closure.
The index type may be infinite; its universe is that of V. This extends the existing
finite-basis predicate without excluding arbitrary-dimensional representations.
Source: blueprint sk-d-real-weil, definition of lisse representations;
Weil II (1.1.6), (1.1.10) (blueprint: sk-d-real-weil). -/
def IsLisseInEveryBasis
    {K : Type u} [Field K] [Finite K] {C₀ : Scheme.{u}}
    {p : C₀ ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p)
    (l : ℕ) [Fact l.Prime] (Q : Type v) [Field Q] [Algebra ℚ_[l] Q]
    [IsAlgClosure ℚ_[l] Q] {V : Type w} [AddCommGroup V] [Module Q V]
    (ρ : Representation Q W.carrier V) : Prop :=
  letI := spectralNorm.nontriviallyNormedField ℚ_[l] Q
  ∀ (ι : Type w) (b : Module.Basis ι Q V) (i j : ι),
    Continuous fun g : W.geometric ↦ b.repr (ρ g (b j)) i

-- Algebraic embeddings preserve the spectral norm because they preserve minimal polynomials.
private theorem spectral_isometry
    (l : ℕ) [Fact l.Prime] {E : Type*} [Field E] [Algebra ℚ_[l] E]
    [Algebra.IsAlgebraic ℚ_[l] E] {F : Type*} [Field F] [Algebra ℚ_[l] F]
    [Algebra.IsAlgebraic ℚ_[l] F] (f : E →ₐ[ℚ_[l]] F) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] F
    Isometry f := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let := spectralNorm.nontriviallyNormedField ℚ_[l] F
  apply AddMonoidHomClass.isometry_of_norm f
  intro x
  change spectralNorm ℚ_[l] F (f x) = spectralNorm ℚ_[l] E x
  unfold spectralNorm
  rw [minpoly.algHom_eq f f.injective]

private theorem spectral_continuous_iff
    (l : ℕ) [Fact l.Prime] {E : Type*} [Field E] [Algebra ℚ_[l] E]
    [Algebra.IsAlgebraic ℚ_[l] E] {F : Type*} [Field F] [Algebra ℚ_[l] F]
    [Algebra.IsAlgebraic ℚ_[l] F] (f : E →ₐ[ℚ_[l]] F)
    {X : Type*} [TopologicalSpace X] (g : X → E) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] F
    Continuous (f ∘ g) ↔ Continuous g := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let := spectralNorm.nontriviallyNormedField ℚ_[l] F
  exact (spectral_isometry l f).comp_continuous_iff

private theorem matrix_stable_lattice
    (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {n : ℕ}
    (σ : Representation E G (Fin n → E)) :
    (letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
     ∀ i j : Fin n, Continuous fun g : G ↦
       LinearMap.toMatrix (Pi.basisFun E (Fin n)) (Pi.basisFun E (Fin n)) (σ g) i j) →
    ∃ Λ : Submodule (Padic.coefficientExtensionIntegers l E) (Fin n → E),
      Nonempty (Module.Basis (Fin n) (Padic.coefficientExtensionIntegers l E) Λ) ∧
      Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      ∀ (g : G) (x : Λ), σ g (x : Fin n → E) ∈ Λ := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  intro hcont
  let τ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).toMonoidHom.comp
      σ.asGroupHom
  have ht : moduleTopology E (Fin n → E) =
      (inferInstance : TopologicalSpace (Fin n → E)) :=
    (eq_moduleTopology E (Fin n → E)).symm
  have hact : letI : TopologicalSpace (Fin n → E) := moduleTopology E (Fin n → E)
      Continuous fun z : G × (Fin n → E) ↦ τ z.1 z.2 := by
    rw [ht]
    apply continuous_pi
    intro i
    have heval (g : G) (x : Fin n → E) :
        τ g x i = ∑ j, (LinearMap.toMatrix (Pi.basisFun E (Fin n))
          (Pi.basisFun E (Fin n)) (σ g) i j) * x j := by
      change σ g x i = _
      simpa only [Pi.basisFun_repr, Matrix.mulVec, dotProduct] using
        congrFun (LinearMap.toMatrix_mulVec_repr
          (Pi.basisFun E (Fin n)) (Pi.basisFun E (Fin n)) (σ g) x).symm i
    simp_rw [heval]
    exact continuous_finsetSum _ fun j _ ↦
      ((hcont i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  obtain ⟨Λ, hfg, hspan, hfree, hrank, hstable, -⟩ :=
    Padic.exists_stable_lattice l E G (Fin n → E) τ hact
  let := hfree
  have : Module.Finite (Padic.coefficientExtensionIntegers l E) Λ :=
    Module.Finite.of_fg hfg
  refine ⟨Λ, ⟨Module.finBasisOfFinrankEq _ _ ?_⟩, hspan, ?_⟩
  · simpa using hrank
  · intro g x
    exact (hstable g).subset ⟨x, x.2, rfl⟩

private theorem compact_matrix_field
    (l : ℕ) [Fact l.Prime] (Q : Type*) [Field Q] [Algebra ℚ_[l] Q]
    [IsAlgClosure ℚ_[l] Q] {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {n : ℕ}
    (φ : G →* Matrix (Fin n) (Fin n) Q) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] Q
    (∀ i j, Continuous fun g ↦ φ g i j) →
    ∃ E : IntermediateField ℚ_[l] Q, FiniteDimensional ℚ_[l] E ∧
      ∀ g i j, φ g i j ∈ E := by
  classical
  let := spectralNorm.nontriviallyNormedField ℚ_[l] Q
  intro hφ
  let e := IsAlgClosure.equiv ℚ_[l] Q (PadicAlgCl l)
  have he : Isometry e := spectral_isometry l e.toAlgHom
  obtain ⟨E₀, hE₀, hmem⟩ := PadicAlgCl.exists_finiteDimensional_forall_mem l
    (e.toAlgHom.mapMatrix.toMonoidHom.comp φ)
    (fun i j ↦ he.continuous.comp (hφ i j))
  let E := E₀.map e.symm.toAlgHom
  have : FiniteDimensional ℚ_[l] E₀ := hE₀
  have hE : FiniteDimensional ℚ_[l] E :=
    Module.Finite.equiv (E₀.equivMap e.symm.toAlgHom).toLinearEquiv
  refine ⟨E, hE, fun g i j ↦ ?_⟩
  exact ⟨e (φ g i j), hmem g i j, e.symm_apply_apply _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The existing predicate is exactly the every-basis predicate in finite dimension.
Source: blueprint sk-d-real-weil, matrix-coefficient clause (blueprint: sk-d-real-weil).
Proof: an arbitrary basis of a finite-dimensional space has a finite index set.
Expand each of its vectors in a finite basis and each coordinate form in the dual
finite basis. Every new coefficient is a finite sum of fixed scalar multiples of
the finite-basis coefficients. Continuity is preserved by these operations. The
spectral topology on the canonical closure is its existing l-adic topology, by
uniqueness of the extension of the p-adic absolute value. The converse uses the
finite bases among all bases. This also includes the empty basis of the zero space. -/
theorem isLisse_iff_everyBasis
    {K : Type u} [Field K] [Finite K] {C₀ : Scheme.{u}}
    {p : C₀ ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p)
    (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V) :
    W.IsLisse l ρ ↔ W.IsLisseInEveryBasis l (PadicAlgCl l) ρ := by
  constructor
  · intro h ι b i j
    exact h.continuous_apply (b.coord i) (b j)
  · intro h
    constructor
    intro n b i j
    have hh := h (ULift.{u} (Fin n)) (b.reindex Equiv.ulift.symm) ⟨i⟩ ⟨j⟩
    simpa only [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply] using hh

set_option backward.isDefEq.respectTransparency.types false in
/-- The finite-coefficient criterion for lisse Weil representations. The E-action is
an action of the whole Weil group; continuity and lattice invariance concern only
its geometric subgroup. No invariance under the degree-one operator is required.
Source: Stanford Weil II L19, Proposition 1.1.9 and pp. 4--5;
Weil II (1.1.6), (1.1.10) (blueprint: sk-d-real-weil).

Proof: first identify Q with the canonical algebraic closure over Q_l. Uniqueness
of the extended absolute value makes this an isometry for the spectral topologies.
Choose a basis and apply lem-real-compact-matrix-coefficient-descent to its
continuous geometric matrices, then transport its finite field back to Q.
Compactness comes from lem-galois-aut-profinite.
Adjoin the finitely many entries of the degree-one matrix and its inverse. Every
Weil element is a geometric element times a power of that lift, so all matrices
then lie in this one finite extension E. They define the displayed E-model.
The geometric matrix entries are continuous in the subspace topology on E; in
finite dimension this is joint continuity for the spectral module topology.
Apply lem-pod-profinite-stable-lattice to obtain a full free geometric stable
integer lattice of rank n. Conversely, extend scalars in the displayed model;
its continuous geometric matrices are continuous over Qbar. In a different basis
conjugation by a fixed invertible matrix preserves continuity of each entry.
This proves both implications, including n=0, without making the lift integral. -/
theorem isLisse_iff_finiteModel
    {K : Type u} [Field K] [Finite K] {C₀ : Scheme.{u}}
    {p : C₀ ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p)
    (l : ℕ) [Fact l.Prime] (Q : Type v) [Field Q] [Algebra ℚ_[l] Q]
    [IsAlgClosure ℚ_[l] Q] {V : Type w} [AddCommGroup V] [Module Q V]
    [FiniteDimensional Q V] (ρ : Representation Q W.carrier V) :
    W.IsLisseInEveryBasis l Q ρ ↔
      ∃ (E : IntermediateField ℚ_[l] Q)
        (_ : FiniteDimensional ℚ_[l] E) (n : ℕ)
        (b : Module.Basis (Fin n) Q V)
        (σ : Representation E W.carrier (Fin n → E)),
        (∀ (w : W.carrier) (i j : Fin n),
          LinearMap.toMatrix b b (ρ w) i j =
            algebraMap E Q
              (LinearMap.toMatrix (Pi.basisFun E (Fin n)) (Pi.basisFun E (Fin n))
                (σ w) i j)) ∧
        (letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
         ∀ i j : Fin n, Continuous fun g : W.geometric ↦
           LinearMap.toMatrix (Pi.basisFun E (Fin n)) (Pi.basisFun E (Fin n))
             (σ g) i j) ∧
        ∃ Λ : Submodule (Padic.coefficientExtensionIntegers l E) (Fin n → E),
          Nonempty (Module.Basis (Fin n) (Padic.coefficientExtensionIntegers l E) Λ) ∧
          Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
          ∀ (g : W.geometric) (x : Λ), σ g (x : Fin n → E) ∈ Λ := by
  classical
  let := spectralNorm.nontriviallyNormedField ℚ_[l] Q
  constructor
  · intro hρ
    let n := Module.finrank Q V
    let b := Module.finBasis Q V
    let A : W.carrier →* Matrix (Fin n) (Fin n) Q :=
      (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ
    have hA (i j : Fin n) : Continuous fun g : W.geometric ↦ A g i j := by
      have hh := hρ (ULift.{w} (Fin n)) (b.reindex Equiv.ulift.symm) ⟨i⟩ ⟨j⟩
      have heq (g : W.geometric) : A g i j = b.repr (ρ g (b j)) i :=
        LinearMap.toMatrixAlgEquiv_apply b (ρ g) i j
      simp_rw [heq]
      apply hh.congr
      intro g
      rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
      rfl
    obtain ⟨E₀, hE₀, hgeom⟩ := compact_matrix_field l Q
      (A.comp W.geometric.subtype) hA
    let γ := W.frobeniusLift
    let T : Set Q := Set.range fun t : Bool × Fin n × Fin n ↦
      A (if t.1 then γ else γ⁻¹) t.2.1 t.2.2
    have : Finite T := Set.finite_range _
    let E₁ := IntermediateField.adjoin ℚ_[l] T
    have : FiniteDimensional ℚ_[l] E₀ := hE₀
    have : FiniteDimensional ℚ_[l] E₁ :=
      IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
    obtain ⟨E, hE, hE₀E, hE₁E⟩ : ∃ E : IntermediateField ℚ_[l] Q,
        FiniteDimensional ℚ_[l] E ∧ E₀ ≤ E ∧ E₁ ≤ E :=
      ⟨E₀ ⊔ E₁, inferInstance, le_sup_left, le_sup_right⟩
    have : FiniteDimensional ℚ_[l] E := hE
    let S : Subgroup W.carrier :=
      { carrier := {g | (∀ i j, A g i j ∈ E) ∧ ∀ i j, A g⁻¹ i j ∈ E}
        one_mem' := by
          change (∀ i j, A 1 i j ∈ E) ∧ ∀ i j, A (1⁻¹) i j ∈ E
          rw [inv_one, map_one]
          constructor <;> intro i j <;> by_cases h : i = j <;>
            simp only [Matrix.one_apply, h, ite_true, ite_false] <;>
            first | exact E.one_mem | exact E.zero_mem
        mul_mem' := by
          intro g h hg hh
          constructor
          · intro i j
            rw [map_mul, Matrix.mul_apply]
            exact E.sum_mem fun k _ ↦ E.mul_mem (hg.1 i k) (hh.1 k j)
          · intro i j
            rw [mul_inv_rev, map_mul, Matrix.mul_apply]
            exact E.sum_mem fun k _ ↦ E.mul_mem (hh.2 i k) (hg.2 k j)
        inv_mem' := by
          intro g hg
          constructor
          · exact hg.2
          · intro i j
            rw [inv_inv]
            exact hg.1 i j }
    have hγ : γ ∈ S := by
      constructor
      · intro i j
        exact hE₁E
          (IntermediateField.subset_adjoin _ _ ⟨(true, i, j), rfl⟩)
      · intro i j
        exact hE₁E
          (IntermediateField.subset_adjoin _ _ ⟨(false, i, j), rfl⟩)
    have hP (g : W.geometric) : (g : W.carrier) ∈ S := by
      exact ⟨fun i j ↦ hE₀E (hgeom g i j),
        fun i j ↦ hE₀E (hgeom g⁻¹ i j)⟩
    have hall (g : W.carrier) (i j : Fin n) : A g i j ∈ E := by
      let d := Multiplicative.toAdd (W.deg g)
      have hc : g * (γ ^ d)⁻¹ ∈ W.geometric := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, W.deg_frobeniusLift,
          ← ofAdd_zsmul, smul_eq_mul, mul_one]
        exact mul_inv_cancel _
      have hm := S.mul_mem (hP ⟨_, hc⟩) (S.zpow_mem hγ d)
      simpa only [inv_mul_cancel_right] using hm.1 i j
    let A' : W.carrier →* Matrix (Fin n) (Fin n) E :=
      { toFun g i j := ⟨A g i j, hall g i j⟩
        map_one' := by
          apply Matrix.ext
          intro i j
          apply Subtype.ext
          simp [Matrix.one_apply, apply_ite]
        map_mul' g h := by
          apply Matrix.ext
          intro i j
          apply Subtype.ext
          simp [Matrix.mul_apply] }
    let σ : Representation E W.carrier (Fin n → E) :=
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun E (Fin n))).symm.toMonoidHom.comp A'
    have hσ (g : W.carrier) :
        LinearMap.toMatrix (Pi.basisFun E (Fin n)) (Pi.basisFun E (Fin n)) (σ g) =
          A' g := by
      exact (LinearMap.toMatrixAlgEquiv (Pi.basisFun E (Fin n))).apply_symm_apply _
    have hcont : letI : TopologicalSpace E :=
        (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace
        ∀ i j : Fin n, Continuous fun g : W.geometric ↦
          LinearMap.toMatrix (Pi.basisFun E (Fin n)) (Pi.basisFun E (Fin n)) (σ g) i j := by
      intro i j
      apply (spectral_continuous_iff l E.val _).mp
      have heq (g : W.geometric) : E.val
          (LinearMap.toMatrix (Pi.basisFun E (Fin n)) (Pi.basisFun E (Fin n)) (σ g) i j) =
            A g i j := by
        rw [hσ]
        rfl
      simpa only [Function.comp_def, heq] using hA i j
    refine ⟨E, inferInstance, n, b, σ, ?_, hcont, ?_⟩
    · intro g i j
      rw [hσ]
      rfl
    · exact matrix_stable_lattice l E (σ.comp W.geometric.subtype) hcont
  · rintro ⟨E, hE, n, b, σ, hσ, hcont, Λ, hb, hspan, hstable⟩
    have : FiniteDimensional ℚ_[l] E := hE
    have hA (i j : Fin n) : Continuous fun g : W.geometric ↦
        LinearMap.toMatrix b b (ρ g) i j := by
      simp_rw [hσ]
      exact (spectral_continuous_iff l E.val _).mpr (hcont i j)
    intro ι c i j
    let φ := c.coord i
    let v := c j
    have key (g : W.geometric) : φ (ρ g v) =
        ∑ k, φ (b k) * ∑ t, LinearMap.toMatrix b b (ρ g) k t * b.repr v t := by
      conv_lhs => rw [← b.sum_repr (ρ g v)]
      simp only [map_sum, map_smul, smul_eq_mul, ← LinearMap.toMatrix_mulVec_repr b b,
        Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
    change Continuous fun g : W.geometric ↦ φ (ρ g v)
    simp_rw [key]
    exact continuous_finsetSum _ fun k _ ↦ continuous_const.mul <|
      continuous_finsetSum _ fun t _ ↦ (hA k t).mul continuous_const

end AlgebraicGeometry.WeilGroup
