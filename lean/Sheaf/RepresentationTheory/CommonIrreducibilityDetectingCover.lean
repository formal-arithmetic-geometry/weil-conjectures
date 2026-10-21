/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.GaloisLisseCorrespondenceData
public import Sheaf.Paper.LisseAdicFiberFunctors
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.RepresentationTheory.Irreducible
public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.CategoryTheory.Galois.AutProfinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import WeilConjectures.RepresentationTheory.FiniteMatrixWitness
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import Sheaf.CategoryTheory.Galois.GaloisTransitive

/-! # A common finite etale cover detecting irreducibility

Source: blueprint main-20261015, sec-deligne-laumon-general,
proof of lem-zl-curve-testing-irreducibility, first six sentences
(blueprint: lem-zl-common-irreducibility-detecting-cover).

The model structure merely bundles the existential coefficient, representation and lattice
witnesses. Its vector space is in coordinates; no basis of a given stalk is prescribed.
The stalk action is specified through the existing evaluation-normalized correspondence.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- The finite coefficient model, stable full lattice, uniformizer and positive reduction
level in the detecting-cover assertion. All fields are actual data or their properties.
Source: blueprint main-20261015, proof of lem-zl-curve-testing-irreducibility,
first six sentences (blueprint: lem-zl-common-irreducibility-detecting-cover). -/
structure IrreducibilityDetectingModel (l : ℕ) [Fact l.Prime]
    (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]
    (G : ProfiniteGrp.{u}) where
  /-- Finite extension inside the fixed algebraic closure. -/
  E : Padic.FiniteCoefficientFields l K
  /-- Dimension of the coordinate vector space. -/
  rank : ℕ
  /-- The finite-dimensional representation. -/
  ρ : G →* ((Fin rank → E.val) ≃ₗ[E.val] (Fin rank → E.val))
  /-- Joint continuity for the canonical l-adic vector-space topology. -/
  continuous : Representation.IsContinuousCoefficient l E.val G (Fin rank → E.val) ρ
  /-- Integral lattice in the coordinate vector space. -/
  lattice : Submodule (Padic.coefficientExtensionIntegers l E.val) (Fin rank → E.val)
  /-- Finite generation over the integers. -/
  finite : lattice.FG
  /-- Freeness over the integers. -/
  free : Module.Free (Padic.coefficientExtensionIntegers l E.val) lattice
  /-- Fullness over the coefficient field. -/
  full : Submodule.span E.val (lattice : Set (Fin rank → E.val)) = ⊤
  /-- Stability under every group element. -/
  stable : ∀ g : G, (ρ g) '' (lattice : Set (Fin rank → E.val)) = lattice
  /-- A uniformizer, rather than an arbitrary element of the integers. -/
  uniformizer : Padic.coefficientExtensionIntegers l E.val
  /-- The uniformizer generates the maximal ideal. -/
  generates : Ideal.span ({uniformizer} : Set (Padic.coefficientExtensionIntegers l E.val)) =
    Padic.coefficientExtensionMaximalIdeal l E.val
  /-- The reduction level. -/
  N : ℕ
  /-- The reduction level is positive. -/
  positive : 1 ≤ N

/-- A finite family of irreducible lisse sheaves has a common detecting cover, including
the empty family. Irreducibility of sheaves is expressed by nonzeroness and the dichotomy
for every lisse subobject. The kernel formula is written elementwise: triviality on
`L / uniformizer^N L` means that every `ρ(g)v - v` is `uniformizer^N w` with `w ∈ L`.
The correspondence witnesses identify the action with the natural geometric stalk action.

Source: blueprint main-20261015, proof of lem-zl-curve-testing-irreducibility,
first six sentences (blueprint: lem-zl-common-irreducibility-detecting-cover).

Proof: (1) Descend each coefficient pair and use cor-galois-lisse-representations to
obtain a finite-dimensional continuous representation and its equivariant stalk comparison.
(2) The exact equivalence preserves nonzero simple objects. Every invariant subspace
descends to a finite extension by taking the finitely many coordinates of an echelon basis;
its action is continuous because its matrix entries are linear combinations of the original
entries. Thus irreducibility here includes every invariant vector subspace.
(3) lem-galois-aut-profinite makes the fundamental group compact.
(4) lem-weil-l-adic-extension-integers-dvr and lem-pod-profinite-stable-lattice give a stable
full free lattice. Apply lem-zl-finite-matrix-irreducibility to an integral basis. Equivalently,
if its witness uses another lattice D, choose a with uniformizer^a L contained in D contained
in uniformizer^(-a) L and increase its level m to N = m + 2a.
(5) lem-weil-valued-dvr-finite-quotients makes each lattice quotient finite. Evaluation on a
lattice basis makes its reduction action continuous, since uniformizer powers are open.
(6) Take the image of the product of these reduction actions. This gives the surjective
continuous q and precisely the intersection of kernels; the empty product is trivial.
(7) cor-galois-open-subgroups realizes the open kernel by a connected finite etale cover.
lem-fet-galois-category, lem-galois-finite-etale-connected-object and lem-galois-transitive
identify its fibre with the regular quotient set by the orbit of a point with this stabilizer.
(8) If q(H) is the whole quotient, H has the full image in every reduction. The finite matrix
witness then gives irreducibility after scalar extension. No closedness of H is needed. -/
theorem exists_common_irreducibility_detecting_cover
    (X : Scheme.{u}) [ConnectedSpace X] [IsNoetherian X] [X.IsSeparated]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (l : ℕ) [Fact l.Prime] [∀ z : X, Invertible (l : X.residueField z)]
    (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber x) G]
    (r : ℕ) (F : Fin r → LisseAlgebraicSheaf l X K)
    (hF : ∀ j : Fin r, ¬ IsZero (F j) ∧
      ∀ (A : LisseAlgebraicSheaf l X K) (f : A ⟶ F j), Mono f → IsZero A ∨ IsIso f) :
    ∃ (c : GaloisLisseFiniteCorrespondence x G)
      (d : GaloisLisseAdicCorrespondence x G c l K)
      (M : Fin r → IrreducibilityDetectingModel l K G),
      (∀ j : Fin r, ∃ e : (K ⊗[(M j).E.val] (Fin (M j).rank → (M j).E.val)) ≃ₗ[K]
          ((lisseAlgebraicFiberFunctor l X x K).obj (F j)),
        ∀ (g : G) (v : K ⊗[(M j).E.val] (Fin (M j).rank → (M j).E.val)),
          e (Representation.coefficientScalarExtension (M j).E.val K G
            (Fin (M j).rank → (M j).E.val) (M j).ρ g v) =
          d.τA.hom.app (F j) (((d.eA.functor.obj (F j)).obj.ρ g)
            (d.τA.inv.app (F j) (e v)))) ∧
      ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (q : G →* Q),
        @Continuous G Q inferInstance ⊥ q ∧ Function.Surjective q ∧
        (∀ g : G, q g = 1 ↔ ∀ (j : Fin r) (v : Fin (M j).rank → (M j).E.val),
          v ∈ (M j).lattice → ∃ w ∈ (M j).lattice,
            (M j).ρ g v - v = ((M j).uniformizer.val ^ (M j).N) • w) ∧
        (∃ T : X.FiniteEtale, ConnectedSpace T.obj.left ∧
          ∃ e : ((FiniteEtale.fiber x).obj T) ≃ Q,
            ∀ (g : G) (t : (FiniteEtale.fiber x).obj T), e (g • t) = q g * e t) ∧
        ∀ H : Subgroup G, q '' (H : Set G) = Set.univ → ∀ j : Fin r,
          Representation.IsIrreducible
            (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
              ((Representation.coefficientScalarExtension (M j).E.val K G
                (Fin (M j).rank → (M j).E.val) (M j).ρ).comp H.subtype)) := by
  sorry

end AlgebraicGeometry.Scheme
