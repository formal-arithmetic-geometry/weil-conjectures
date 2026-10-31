/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedScalarRealization
public import WeilConjectures.AlgebraicGeometry.GeometricHypotheses
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.IndPrincipalZariski
import WeilConjectures.CategoryTheory.RingedSitePerfectDuality
import WeilConjectures.Algebra.Homology.FieldComplexCohomologySplitting
import WeilConjectures.AlgebraicGeometry.CondensedLisseProEtaleLocality
import WeilConjectures.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect

/-! # Perfect point and condensed coefficient complexes

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/sk-def-perfect/_section.md,
order 3598 (blueprint: sk-def-perfect).

The point category is the ordinary module derived category of the singleton section ring.
The scheme category is the ordinary unbounded derived category of modules over p_X^Λ.
Its tensor is the published K-flat relative derived tensor, with the native Koszul symmetry.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w v t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Perfect point complexes are dualizable for the ordinary relative derived tensor.
No dual is selected by this proposition. In the coefficient setting R is Λ(*).
Source: blueprint order 3598, point definition (blueprint: sk-def-perfect). -/
def IsPerfectPointComplex
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [HasDerivedCategory.{w} (ModuleCat.{u + 1} (condensedScalarRing Λ))]
    (K : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) : Prop :=
  IsDualizable K

/-- Perfectness over Λ_X means dualizability in the ordinary unbounded category of
modules over the existing pulled-back condensed ring. The monoidal unit is Λ_X[0].
Source: blueprint order 3598, scheme definition (blueprint: sk-def-perfect). -/
def IsPerfectOver (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) : Prop :=
  IsDualizable K

/-- The existence predicate is precisely the two triangle identities, with composition
written in Lean's left-to-right order. It does not choose a dual.
Source: blueprint order 3598, displayed duality identities (blueprint: sk-def-perfect).
Proof: unpack HasRightDual into its object and ExactPairing. The two ExactPairing
identities become the displayed identities by inserting the inverse source unitor and
cancelling the target unitor. Conversely cancel those unitors and construct ExactPairing,
then HasRightDual, from the evaluation and coevaluation. -/
theorem dualizable_iff_triangle_identities {C : Type t} [Category.{v} C]
    [MonoidalCategory C] (K : C) :
    IsDualizable K ↔
      ∃ (D : C) (e : D ⊗ K ⟶ 𝟙_ C) (c : 𝟙_ C ⟶ K ⊗ D),
        (λ_ K).inv ≫ c ▷ K ≫ (α_ K D K).hom ≫ K ◁ e ≫ (ρ_ K).hom = 𝟙 K ∧
        (ρ_ D).inv ≫ D ◁ c ≫ (α_ D K D).inv ≫ e ▷ D ≫ (λ_ D).hom = 𝟙 D := by
  sorry

/-- A perfect point complex is exactly an object with a bounded finite-projective model,
for every commutative ring, including the zero ring and nonregular finite quotients.
Source: blueprint order 3598, point equivalence (blueprint: sk-def-perfect).
Proof: a bounded finite-projective complex has its termwise dual with reversed degrees;
the signed evaluation and coevaluation descend to the K-flat derived tensor and satisfy
both triangles. Conversely a dualizable object is compact, because the regular module
R[0] is compact and tensoring with the dual preserves coproducts. The compact objects of
D(R), generated by R[0], are precisely the retracts of finite iterated cones of its shifts,
which are exactly the bounded finite-projective models (Stacks 0FNS). -/
theorem perfectPointComplex_iff_finiteProjectiveModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [HasDerivedCategory.{w} (ModuleCat.{u + 1} (condensedScalarRing Λ))]
    (K : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) :
    IsPerfectPointComplex Λ K ↔ DerivedCategory.IsPerfectRingComplex K := by
  sorry

/-- Over a field the same point perfectness means bounded finite-dimensional cohomology.
Module.Finite is finite dimension over a field; IsZero is vanishing of the cohomology module.
Source: blueprint order 3598, field parenthesis (blueprint: sk-def-perfect).
Proof: split each degree of a complex of vector spaces into boundaries, cohomology and a
complement mapping isomorphically onto the next boundaries. The boundary/complement pairs
are contractible, leaving the zero-differential cohomology complex. If its terms are finite
and vanish outside [a,b], that complex is a bounded finite-projective model. Conversely
cohomology of such a model is a subquotient of finite-dimensional terms and vanishes outside
the degree bounds. Apply the point finite-projective characterization. -/
theorem perfectPointComplex_iff_finiteCohomology
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hField : IsField (condensedScalarRing Λ))
    [HasDerivedCategory.{w} (ModuleCat.{u + 1} (condensedScalarRing Λ))]
    (K : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) :
    IsPerfectPointComplex Λ K ↔
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (condensedScalarRing Λ)) i).obj K)) ∧
      ∀ i : ℤ, Module.Finite (condensedScalarRing Λ)
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (condensedScalarRing Λ)) i).obj K) := by
  sorry

namespace CondensedRing

/-- The finite member of the specified coefficient list: the existing quotient O_E/ϖ_E^n
with discrete topology, then the existing continuous-map condensed ring construction.
Source: blueprint order 3598, coefficient list (blueprint: sk-def-perfect). -/
abbrev perfectFiniteCoefficient (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ell E n) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ell E n) := discreteTopology_bot _
  Profinite.continuousMapRingObj (Padic.coefficientExtensionRing ell E n)

/-- In the stated finite-field geometry, perfectness is exactly pro-etale local
representation by bounded finite-projective coefficient-module complexes. The list is
A_(E,n), O_E, E and the finite-subextension-valued condensed algebraic closure.
Source: blueprint order 3598, local equivalence (blueprint: sk-def-perfect).
Proof: finite-type affine opens have finitely many irreducible components. Cluster them
by intersections to obtain connected clopen affine pieces. Dualizability restricts to them.
The condensed connected-contractible-model theorem supplies perfect scalar models on a
w-contractible affine cover. Extend their bounded finite-projective representatives
termwise: scalar extension preserves finite-free retracts and their degree bounds. The
composite cover therefore witnesses IsPerfectOnCoefficientSite, without requiring its
members to be connected. Conversely, site-perfect duality identifies RHom(K,Λ_X) tensor N
with RHom(K,N). Transpose the identity of K through this comparison and symmetry to obtain
coevaluation. The closed evaluation criterion gives both triangles, hence dualizability.
This uses the ordinary relative derived tensor, including at the algebraic closure. -/
theorem perfectOver_iff_sitePerfect (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hDifferent : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hAdmissible : IsAdmissibleCoefficient Λ)
    (_hCoefficient :
      Nonempty (Mon.mk Λ ≅ Mon.mk (perfectFiniteCoefficient ell E n)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom] [GeometricallyConnected X₀.hom]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber X₀).left) Ab.{u + 1})
        (condensedRingObj Λ (D.geometricFiber X₀).left))) :
    IsPerfectOver Λ (D.geometricFiber X₀).left K ↔
      IsPerfectOnCoefficientSite Λ (D.geometricFiber X₀).left K := by
  sorry

end CondensedRing
end AlgebraicGeometry.ProEtale
