/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FieldSmoothDuality.CondensedFieldSmoothDuality
import WeilConjectures.DeligneLaumon.CondensedWeil.ConnectedAffineCurveLocalQuotient
import WeilConjectures.DeligneLaumon.CondensedWeil.ScalarRestrictedQuotientSpectrum

/-! Connected native affine-curve endpoint used by the finite-component argument. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedWeil

/-- The geometrically connected affine-curve endpoint for the actual condensed module.

Source: latest blueprint, sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/
lem-a1-affine-hc2-pure.proof.md, its three paragraphs, and
lem-a1-geometric-coinvariants-pure.proof.md
(blueprint: lem-zl-native-connected-affine-hc2-spectrum).

Proof: Let V be the geometric generic fibre of the native lisse module, with its
geometric monodromy action, and put W = V modulo the span of gv-v for geometric g.
The span is stable under the Weil group since the geometric subgroup is normal.
Thus W is a quotient Weil representation with trivial geometric subgroup, and every
degree-one Weil lift induces the same invertible operator A on W.

The native lisse-monodromy identification of ordinary sections with geometric invariants,
applied to the underived dual, and the smooth-curve compact-support duality identify
H_c^2 with W(-1).  The identification is equivariant for the canonical geometric
Frobenius: dualizing the residual action on the invariant dual gives A on W, and the
negative Tate line contributes the scalar q.  The compact-support and point-insertion
comparisons identify this action with compactCohomologyFrobenius for the given
compactification, not merely with a conjugate chosen operator.

The curve is nonempty and of finite type, so choose a closed point x of degree d>0.
The quotient from its geometric fibre to W intertwines its local Frobenius with A^d.
For an eigenvalue lambda of A, lambda^d is an eigenvalue of A^d and hence of that local
Frobenius: in a basis extending a basis of the invariant kernel the matrix is block
upper triangular. Punctual purity of weight zero gives norm(iota(lambda^d))=1.
Multiplicativity of the norm and injectivity of the positive d-th power on nonnegative
reals give norm(iota(lambda))=1.  Finally the eigenvalues of q A are q lambda, of norm q.
These arguments use no diagonalizability.  When W=0 there are no eigenvalues, so the
conclusion is vacuous.  Transport through the specified linear equivalence gives the
assertion for the lifted scalar field CohomologyScalar. The geometric quotient is
provided by connected_affine_curve_local_quotient; the proved scalar-restriction lemma
performs the entire subsequent eigenvalue and norm calculation. -/
theorem connected_affine_curve_hc2_spectrum
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] [IsAffine Y₀.left]
    [SmoothOfRelativeDimension 1 Y₀.hom]
    [GeometricallyConnected Y₀.hom]
    (N : WeilModule D ell Y₀)
    (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) N.carrier)
    (iota : PadicAlgCl ell →+* ℂ)
    (hPure : Pure D ell Y₀ N iota 0)
    (d₀ : Compactification Y₀.hom) :
    ∀ α : CohomologyScalar.{u} ell,
      Module.End.HasEigenvalue
          ((compactCohomologyFrobenius D ell Y₀ d₀ N 2).hom) α →
        ‖iota α.down‖ = (Nat.card D.k₀ : ℝ) := by
  obtain ⟨x, ix, hix, hV, π, hπ, hπF⟩ :=
    connected_affine_curve_local_quotient D ell hell Y₀ N hN d₀
  let : FiniteDimensional (PadicAlgCl ell) (closedFiber D ell Y₀ N x ix hix) := hV
  intro α hα
  let : Module (PadicAlgCl ell) (compactH D ell Y₀ d₀ N 2) :=
    (unliftCompactH D ell Y₀ d₀ N).isModule
  have hα' : Module.End.HasEigenvalue
      (unliftCompactFrobenius D ell Y₀ d₀ N).hom α.down := by
    obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := (v : unliftCompactH D ell Y₀ d₀ N))
    refine Module.End.hasEigenvector_iff.2 ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    change (compactCohomologyFrobenius D ell Y₀ d₀ N 2).hom v =
      (ULift.up α.down : CohomologyScalar.{u} ell) • v
    simpa using hv
  exact norm_eigenvalue_of_scalar_restricted_local_quotient
    (unliftCompactH D ell Y₀ d₀ N) (unliftCompactFrobenius D ell Y₀ d₀ N).hom
    π hπ (Nat.card D.k₀) (localClosedPointDegree D Y₀ x) Nat.card_pos
    (localClosedPointDegree_pos D Y₀ x) (closedOperator D ell Y₀ N x ix hix).hom hπF
    iota (fun β hβ ↦ by simpa using hPure x ix hix β hβ) α.down hα'

end WeilConjectures.CondensedWeil
