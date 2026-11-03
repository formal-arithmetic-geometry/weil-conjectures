/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FieldSmoothDuality.CondensedFieldSmoothDuality
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! The geometric quotient underlying the connected affine-curve endpoint. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedWeil

/-- Canonical scalar restriction from the section-universe lift to Qbar_ell.
Source: the scalar convention of native compact cohomology
(blueprint: lem-zl-native-connected-affine-local-quotient). -/
abbrev unliftCompactH (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (d₀ : Compactification Y₀.hom) (N : WeilModule D ell Y₀) :=
  (ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.symm.toRingHom : PadicAlgCl ell →+* CohomologyScalar.{u} ell)).obj
      (compactH D ell Y₀ d₀ N 2)

/-- Change scalars on an endomorphism without unfolding its underlying cohomology object.
Source: functorial scalar restriction of the native operator
(blueprint: lem-zl-native-connected-affine-local-quotient). -/
abbrev unliftScalarEnd (ell : ℕ) [Fact ell.Prime]
    (V : ModuleCat.{u + 1} (CohomologyScalar.{u} ell)) (F : End V) :=
  (ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.symm.toRingHom : PadicAlgCl ell →+* CohomologyScalar.{u} ell)).map F

/-- Scalar restriction of the actual compact-cohomology operator.
Source: functorial scalar restriction of the native operator
(blueprint: lem-zl-native-connected-affine-local-quotient). -/
abbrev unliftCompactFrobenius (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (d₀ : Compactification Y₀.hom) (N : WeilModule D ell Y₀) :=
  unliftScalarEnd ell (compactH D ell Y₀ d₀ N 2)
    (compactCohomologyFrobenius D ell Y₀ d₀ N 2)

/-- The geometric coinvariant quotient, with local Frobenius return.

Source: latest blueprint, sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/
lem-a1-affine-hc2-pure.proof.md and lem-a1-geometric-coinvariants-pure.proof.md
(blueprint: lem-zl-native-connected-affine-local-quotient).

Proof: Let V be a geometric fibre and P its geometric monodromy group. Put
R=span{gv-v : g in P, v in V}. The annihilator of R in the finite-dimensional dual
V^* is exactly the invariant dual: a functional annihilates every gv-v if and only
if it is P-invariant. Thus W=V/R is canonically dual to (V^*)^P, and V to W is
surjective. Native monodromy identifies ordinary sections of the underived dual
coefficient with (V^*)^P, respecting evaluation and its contragredient Weil action.
Degree-zero ordinary cohomology is that section space, via the derived adjunction
and the degree-zero single-complex comparison.

Choose a basis of the one-dimensional negative Tate value line. Smooth curve duality
then identifies H_c^2 with the dual of the preceding section space. Equivalently, the
quotient map is characterized by pairing pi(v) against a dual section s as s(v) times
that Tate basis. Perfectness makes this map onto: its transpose is the injective
inclusion of invariant dual sections into V^*. The geometric subgroup is normal,
so R is Weil-stable. Write A for the residual degree-one action on W and T for the
action on invariant dual sections. Contragredience gives T=(A^{-1})^*. The native
Frobenius pairing equation B(Fh,Ts)=q B(h,s) therefore gives F=qA under the specified
identification. Here q=Nat.card D.k0. Point insertion and compactification exchange
are those defining the native pairing and operators, so this is an equality with
compactCohomologyFrobenius itself. Canonical ULift scalar restriction preserves it.

The curve is nonempty. A maximal ideal of a nonempty affine open gives a closed
point x with finite residue field over D.k0; algebraic closedness of D.k supplies
a compatible residue-field embedding. Its geometric fibre V_x is finite-dimensional
by a finite-free local trivialization. A geometric fibre path identifies V_x with V;
compose with the preceding quotient and cohomology identification to obtain pi.
A different path changes this map by geometric monodromy, which is trivial on W.
The native local-return comparison identifies the actual closedOperator with a Weil
lift of degree d=localClosedPointDegree D Y0 x. Since W has trivial geometric action,
that lift acts by A^d: divide it by the d-th power of a degree-one lift to obtain a
geometric element. Consequently pi F_x=A^d pi. Substituting A=q^{-1}F proves the
exact displayed equation. No purity or spectral assertion is used, and a zero
coefficient gives the surjection from zero to zero. -/
theorem connected_affine_curve_local_quotient
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] [IsAffine Y₀.left]
    [SmoothOfRelativeDimension 1 Y₀.hom] [GeometricallyConnected Y₀.hom]
    (N : WeilModule D ell Y₀)
    (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) N.carrier)
    (d₀ : Compactification Y₀.hom) :
    ∃ (x : {x : Y₀.left // x ∈ closedPoints Y₀.left})
      (ix : Y₀.left.residueField x.val →+* D.k)
      (hix : ix.comp (Y₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
      FiniteDimensional (PadicAlgCl ell) (closedFiber D ell Y₀ N x ix hix) ∧
      ∃ π : closedFiber D ell Y₀ N x ix hix →ₗ[PadicAlgCl ell]
          unliftCompactH D ell Y₀ d₀ N,
        Function.Surjective π ∧
        π ∘ₗ (closedOperator D ell Y₀ N x ix hix).hom =
          (((Nat.card D.k₀ : PadicAlgCl ell)⁻¹ •
              (unliftCompactFrobenius D ell Y₀ d₀ N).hom) ^
            localClosedPointDegree D Y₀ x) ∘ₗ π := by
  sorry

end WeilConjectures.CondensedWeil
