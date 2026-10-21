/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Topology.LadicLattice
public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Sheaf.CategoryTheory.CondensedDerivedInvariantBar

/-! # Polynomial evaluation into the derived internal lattice bar

Source: main-20261015 blueprint, direct-images proof, paragraph (3), agent-formulated
polynomial homogeneous-resolution comparison
(blueprint: lem-sfb-polynomial-derived-bar-comparison).

The polynomial object is specified by actual coproducts, its differential by finite
integer matrices, and its evaluation and total comparison by their components. These
specifications determine the objects up to the displayed identifications and the maps
uniquely. No unspecified object or arbitrary comparison map is chosen by a definition.
The all-continuous noncomplete-coefficient reference remains WANTED.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar

namespace Profinite.CondensedAction.PolynomialBar

/-- The lattice with its product ell-adic topology, lifted into the site universe.
`Multiplicative` only changes the notation for its additive group law.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
abbrev Lattice (ell r : ℕ) [Fact ell.Prime] :=
  Profinite.LadicLattice.Lattice.{u} ell r

/-- Transport total disconnectedness along the notation-only multiplicative tag.
Source: the inverse-limit lattice topology in blueprint paragraph (3)
(blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
instance latticeTotallyDisconnected (ell r : ℕ) [Fact ell.Prime] :
    TotallyDisconnectedSpace (Lattice.{u} ell r) :=
  Profinite.LadicLattice.latticeTotallyDisconnected ell r

/-- Monomials in the nr variables, with finite nonnegative exponent vectors.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
abbrev Monomial (r n : ℕ) := (Fin n × Fin r) →₀ ℕ

/-- A finite polynomial with integer coefficients specifies an A-linear generator map
into a monomial-indexed internal coproduct, using finite sums of its coprojections.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
def polynomialArrow (A : CategoryTheory.CondensedBar.Ring.{u}) (r n : ℕ)
    (X : CategoryTheory.CondensedBar.Modules A)
    (ι : Monomial r n → (Mod.regular A.X ⟶ X))
    (f : MvPolynomial (Fin n × Fin r) ℤ) : Mod.regular A.X ⟶ X :=
  ∑ m ∈ f.support, f.coeff m • ι m

/-- The variable substitution for a bar face: drop the first or last variable block,
or replace the two adjacent blocks by their sum at an interior face.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
def faceVariable (r n : ℕ) (i : Fin (n + 2)) (v : Fin n × Fin r) :
    MvPolynomial (Fin (n + 1) × Fin r) ℤ :=
  if v.1.val + 1 < i.val then MvPolynomial.X (v.1.castSucc, v.2)
  else if v.1.val + 1 = i.val then
    MvPolynomial.X (v.1.castSucc, v.2) + MvPolynomial.X (v.1.succ, v.2)
  else MvPolynomial.X (v.1.succ, v.2)

/-- The displayed additive-bar differential, as a finite universal integer polynomial.
Face zero drops the first block; face n+1 drops the last block, including n=0.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
def differentialPolynomial (r n : ℕ) (f : MvPolynomial (Fin n × Fin r) ℤ) :
    MvPolynomial (Fin (n + 1) × Fin r) ℤ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    MvPolynomial.eval₂Hom MvPolynomial.C (faceVariable r n i) f

/-- A polynomial complex, identified degreewise with the specified internal coproducts.
The generator equation specifies its entire differential by A-linearity and the coproduct
universal property. Extension by zero below will impose zero in every negative degree.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
structure Complex (A : CategoryTheory.CondensedBar.Ring.{u}) (r : ℕ) where
  cochain : CochainComplex (CategoryTheory.CondensedBar.Modules A) ℕ
  ι : ∀ n : ℕ, Monomial r n → (Mod.regular A.X ⟶ cochain.X n)
  isColimit : ∀ n : ℕ, IsColimit (Cofan.mk (cochain.X n) (ι n))
  differential : ∀ (n : ℕ) (m : Monomial r n),
    ι n m ≫ cochain.d n (n + 1) =
      polynomialArrow A r (n + 1) (cochain.X (n + 1)) (ι (n + 1))
        (differentialPolynomial r n (MvPolynomial.monomial m 1))

variable (ell : ℕ) [Fact ell.Prime] (F : Type u) [NormedField F]
  [NormedAlgebra ℚ_[ell] F] (r : ℕ)

/-- The coefficient action is exactly trivial inflation of the regular internal module.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
abbrev trivialScalar : CategoryTheory.CondensedBar.Equivariant
    (continuousScalarRing F) (Lattice.{u} ell r) :=
  (trivial (R := (continuousScalarRing F).toMon) (P := Lattice.{u} ell r)).obj
    (Mod.regular (continuousScalarRing F).X)

/-- Polynomial evaluation is pinned on every monomial with every section coefficient,
after every profinite base change. This uses all continuous F-valued sections. The
formula determines the internal map uniquely and includes the empty product in degree 0.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
structure Evaluation (P : Complex (continuousScalarRing F) r)
    (functions : InternalFunctions (continuousScalarRing F))
    (bar : BarDiagram (G := Lattice.{u} ell r) functions) where
  map : P.cochain ⟶ (cochains bar).obj (trivialScalar ell F r)
  monomial : ∀ (n : ℕ) (m : Monomial r n) (S : Profinite.{u})
    (c : ULift.{u + 1} C(S, F)) (T : Profinite.{u}) (f : T ⟶ S)
    (g : C(T, power (Lattice.{u} ell r) n)) (t : T),
    (((functions.evaluate (power (Lattice.{u} ell r) n) S
        (Mod.regular (continuousScalarRing F).X)
        ((P.ι n m ≫ map.f n ≫
            (bar.term (trivialScalar ell F r) n).hom).hom.hom.app (op S) c)).val
              T f g).down) t =
      c.down (f.hom.hom t) * ∏ v : Fin n × Fin r,
        (algebraMap ℚ_[ell] F ((g t v.1).toAdd.down v.2 : ℚ_[ell])) ^ m v

variable [ActionAbelian (continuousScalarRing F) (Lattice.{u} ell r)]
  [IsGrothendieckAbelian.{u + 1}
    (CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F) (Lattice.{u} ell r))]
  [HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F) (Lattice.{u} ell r))]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules (continuousScalarRing F))]

/-- The canonical map into the compatible nonnegative total is specified on each degree:
evaluate, apply A to I^0, and include the (n,0) summand. The generator and total-summand
formulas uniquely determine this map; no arbitrary isomorphism is substituted for it.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
def TotalComponents (M : Model (continuousScalarRing F) (Lattice.{u} ell r))
    (P : Complex (continuousScalarRing F) r) (e : Evaluation ell F r P M.functions M.bar)
    (I : InjectiveResolution (trivialScalar ell F r))
    (eta : P.cochain ⟶ (totalCochains M.bar).obj I.cocomplex) : Prop :=
  ∀ n : ℕ, eta.f n = e.map.f n ≫ ((cochains M.bar).map (I.ι.f 0)).f n ≫
    (doubleComplex M.bar I.cocomplex).ιTotal (.up ℕ) n 0 n (by simp)


/-- The comparison assertion includes existence of its normalized polynomial model and
bar data. All compatible bar models and every nonnegative injective resolution give the
same specified comparison, which is invertible in the ordinary derived category. No
acyclicity of underived individual internal-Hom terms is asserted.
Source: blueprint paragraph (3) (blueprint: lem-sfb-polynomial-derived-bar-comparison). -/
def Comparison (ell : ℕ) [Fact ell.Prime] (F : Type u) [NormedField F]
    [NormedAlgebra ℚ_[ell] F] (r : ℕ) : Prop := by
  refine ∃ h : ActionAbelian (continuousScalarRing F) (Lattice.{u} ell r), ?_
  letI : ActionAbelian (continuousScalarRing F) (Lattice.{u} ell r) := h
  refine ∃ g : IsGrothendieckAbelian.{u + 1}
    (CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F) (Lattice.{u} ell r)), ?_
  letI : IsGrothendieckAbelian.{u + 1}
    (CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F) (Lattice.{u} ell r)) := g
  letI : HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F) (Lattice.{u} ell r)) :=
      HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Modules (continuousScalarRing F)) :=
    HasDerivedCategory.standard _
  exact Nonempty (Model (continuousScalarRing F) (Lattice.{u} ell r)) ∧
    ∃ P : Complex (continuousScalarRing F) r,
      ∀ M : Model (continuousScalarRing F) (Lattice.{u} ell r),
        ∃ e : Evaluation ell F r P M.functions M.bar,
          ∀ I : InjectiveResolution (trivialScalar ell F r),
            ∃ eta : P.cochain ⟶ (totalCochains M.bar).obj I.cocomplex,
              TotalComponents ell F r M P e I eta ∧
                IsIso (DerivedCategory.Q.{u + 2}.map
                  (HomologicalComplex.extendMap eta ComplexShape.embeddingUpNat))

/-- Polynomial evaluation into the derived internal lattice bar is an isomorphism, for
both the finite intermediate field and the noncomplete norm-topological algebraic closure.
The ordinary derived category contains the site and every profinite parameter set.
Source: main-20261015 direct-images proof, paragraph (3), agent-formulated analytic input
(blueprint: lem-sfb-polynomial-derived-bar-comparison).

Proof:
1. Form the equivariant homogeneous polynomial complex K in (n+1)r variables, with
   diagonal translation y_a maps to y_a-g, alternating deletion differential, and
   constant augmentation. Finite substitution matrices define internal linear maps.
   Paired deletions prove d squared is zero, and forgetting detects exactness by
   lem-sfb-condensed-derived-restriction-calculus.
2. Insert zero as the first coordinate to obtain an underlying contraction of the
   augmented complex: d h + h d = 1 and evaluation at zero splits the augmentation.
   The contraction need not be equivariant; forgetting detects the quasi-isomorphism.
3. Change coordinates to z=y_0 and x_a=y_a-y_(a-1), with inverse y_a=z+x_1+...+x_a.
   Apply lem-sfb-polynomial-translation-acyclic to this translation module T_(r,nr).
   Every K^n is invariant-acyclic without interchanging derivation and filtered colimits.
4. Invariance under each constant integer unit translation removes all z variables:
   the degree d-1 coefficient of f(z+1)-f(z) is d times the leading coefficient, and
   d is invertible in every section ring. Work locally on finite polynomials and glue.
   Parameter-dependent translations fix the remaining x variables. Deleting y_0,
   an interior y_a, or the last y identifies the differential with the displayed one.
5. Apply the bounded-below derived-object clause of sk-thm-acyclicity to K using the
   Grothendieck and left exact invariant structures of the restriction-calculus node.
   The inverse of derived augmentation followed by the normalized acyclic-resolution
   unit gives an isomorphism P to ordinary derived invariants of A in degree zero.
6. Evaluate homogeneous polynomials on lattice tuples. Evaluation is continuous in
   every profinite parameter, equivariant, commutes with deletion, and preserves the
   augmentation. The homogeneous-to-inhomogeneous substitution is
   (0,g_1,g_1+g_2,...,g_1+...+g_n), whose consecutive differences are precisely g_a.
   By lem-sfb-equivariant-resolution-bar-normalization the specified eta equals the
   composite of the preceding isomorphism with the normalized bar comparison.
   Apply lem-sfb-condensed-derived-invariant-bar to that last comparison. Thus the
   actual evaluation arrow eta is invertible, for every compatible resolution/model.
7. For r=0 the group is trivial, invariants are the identity, and the inserted-zero
   contraction and evaluation preserve the constant degree-zero augmentation. Both
   coefficient fields are retained, with no completion, infinite series, or replacement
   of all continuous Omega-valued functions by finite-subextension-valued functions.
-/
theorem polynomial_derived_bar_comparison (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E] (r : ℕ) :
    Comparison ell E r ∧ Comparison ell Ω r := by
  sorry

end PolynomialBar
end Profinite.CondensedAction
