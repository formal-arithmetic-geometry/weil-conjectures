/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.NumberTheory.Padics.CountableClosedFiniteCover
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Finite-quotient descent for continuous scalar cochains

Source: main-20261015 six-functors direct-images proof, paragraph (3), agent analytic
expansion (blueprint: lem-sfb-prime-to-ell-cochain-finite-quotient-descent).

The complexes and their inclusion are specified by section coordinates and the actual
sheafification counit. These coordinates determine the objects up to unique compatible
isomorphism. No definition chooses data from the comparison theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.ContinuousScalarCochains

/-- A cochain factors through one open normal quotient in all its group coordinates.
The descended function remains continuous in the unrestricted profinite parameter.
Source: paragraph (3), finite-quotient subpresheaf
(blueprint: lem-sfb-prime-to-ell-cochain-finite-quotient-descent). -/
def FactorsThroughFiniteQuotient {F K : Type u} [TopologicalSpace F] [Group K]
    [TopologicalSpace K] [IsTopologicalGroup K] {S : Profinite.{u}} {n : ℕ}
    (c : C(S × (Fin n → K), F)) : Prop :=
  ∃ U : OpenNormalSubgroup K,
    ∃ b : C(S × (Fin n → K ⧸ U.toSubgroup), F),
      ∀ (s : S) (g : Fin n → K),
        c (s, g) = b (s, fun j ↦ QuotientGroup.mk' U.toSubgroup (g j))

/-- The two explicit nonnegative complexes and their canonical inclusion, in section
coordinates. The internal module category is Mathlib's `Mod`, for the recorded
continuous-map ring object and its recorded tensor structure. `P` is the finite-quotient
subpresheaf complex: its inclusion is injective and has exactly the specified image at
every S and degree. `a` identifies its actual sheafification with the underlying complex
of L. The last equality fixes iota as the sheafified inclusion followed by the canonical
counit, rather than an arbitrary map between isomorphic objects. The last clause is its
invertibility in the unbounded derived category, after extension by zero to negative degrees.

The section equivalences include addition, restriction, scalar multiplication and the
entire inhomogeneous differential. In degree zero that formula subtracts the same value
from itself. In particular these are all continuous cochains, not locally constant ones.
Source: paragraph (3), definitions of C, L and iota and the derived comparison
(blueprint: lem-sfb-prime-to-ell-cochain-finite-quotient-descent). -/
def HasFiniteQuotientComparison (F K : Type u) [NormedField F] [Group K]
    [TopologicalSpace K] [IsTopologicalGroup K] : Prop := by
  let A := Profinite.continuousMapRingObjOfUniverse.{u, u} F
  letI : MonObj A := Profinite.continuousMapRingObjOfUniverseMonObj F
  letI : IsCommMonObj A := Profinite.isCommMonObj_continuousMapRingObjOfUniverse F
  let M := Mod (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) A
  let V : M ⥤ Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} := Mod.forget A
  let U := V ⋙ sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}
  let T := presheafToSheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}
  letI : HasDerivedCategory.{u + 2} M := HasDerivedCategory.standard M
  exact ∃ (C L : CochainComplex M ℕ)
    (e : ∀ (n : ℕ) (S : Profinite.{u}),
      (C.X n).X.obj.obj (op S) ≃+ C(S × (Fin n → K), F)),
    (∀ (n : ℕ) (S S' : Profinite.{u}) (f : S' ⟶ S)
      (x : (C.X n).X.obj.obj (op S)) (s : S') (g : Fin n → K),
      e n S' ((C.X n).X.obj.map f.op x) (s, g) = e n S x (f s, g)) ∧
    (∀ (n : ℕ) (S : Profinite.{u})
      (r : (InternalAbelianSheafModule.sectionRings (coherentTopology Profinite.{u}) A).obj
        (op S))
      (x : ((InternalAbelianSheafModule.sectionModuleFunctor
        (coherentTopology Profinite.{u}) A).obj (C.X n)).val.obj (op S))
      (s : S) (g : Fin n → K),
      e n S (r • x) (s, g) = r.down s * e n S x (s, g)) ∧
    (∀ (n : ℕ) (S : Profinite.{u}) (x : (C.X n).X.obj.obj (op S))
      (s : S) (g : Fin (n + 1) → K),
      e (n + 1) S (((C.d n (n + 1)).hom.hom.app (op S)) x) (s, g) =
        e n S x (s, fun j ↦ g j.succ) +
          ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
            e n S x (s, Fin.contractNth j (· * ·) g)) ∧
    ∃ (P : CochainComplex (Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ)
      (i : P ⟶ (U.mapHomologicalComplex (.up ℕ)).obj C),
      (∀ (n : ℕ) (S : Profinite.{u}), Function.Injective ((i.f n).app (op S))) ∧
      (∀ (n : ℕ) (S : Profinite.{u}) (c : C(S × (Fin n → K), F)),
        (∃ x : (P.X n).obj (op S), e n S (((i.f n).app (op S)) x) = c) ↔
          FactorsThroughFiniteQuotient c) ∧
      ∃ (a : (T.mapHomologicalComplex (.up ℕ)).obj P ≅
          (V.mapHomologicalComplex (.up ℕ)).obj L)
        (iota : L ⟶ C),
        (∀ n : ℕ, V.map (iota.f n) = a.inv.f n ≫ T.map (i.f n) ≫
          (sheafificationAdjunction (coherentTopology Profinite.{u})
            AddCommGrpCat.{u + 1}).counit.app (C.X n).X) ∧
        IsIso (DerivedCategory.Q.{u + 2}.map
          (HomologicalComplex.extendMap iota ComplexShape.embeddingUpNat))

/-- Finite-quotient scalar cochains compare with all continuous scalar cochains over
both E and the noncomplete norm-topological algebraic closure Omega. The coordinate
presentation in `HasFiniteQuotientComparison` fixes the inclusion before localization.
Source: paragraph (3), agent analytic expansion
(blueprint: lem-sfb-prime-to-ell-cochain-finite-quotient-descent).

Proof:
1. The continuous faces preserve the scalar action and finite-quotient subpresheaves.
   Associativity gives the coface identities; pairing opposite signs gives d squared zero.
   Intersections give a common quotient. Degree zero is the scalar sheaf and d is zero.
2. For a finite-quotient n-cocycle, use (-1)^n/|Q| times its sum over the last variable.
   Sum its cocycle equation and translate the last variable to obtain db=c. For n=1 this
   gives c=0. The primitive is continuous with the unrestricted parameter S.
3. For every finite subfield use lem-weil-l-adic-extension-complete and
   lem-weil-l-adic-extension-absolute-value, then
   lem-sfb-prime-to-ell-complete-scalar-integral. Integrate the same cocycle equation;
   translation and normalization give a continuous primitive with norm bound one.
4. For Omega use lem-sfb-profinite-metric-function-quotients to descend a single family
   to metrizable profinite parameter and group quotients. Surjectivity preserves the
   cocycle equation and the prime-to-ell condition. Empty S has only the zero cochain.
5. Use lem-sfb-algcl-countable-closed-finite-cover and
   lem-sfb-norm-one-finite-subfield-projection. Increasing finite fields F_i cover Omega.
   The components e_i=(p_i-p_(i-1))z are finite-field cocycles, pointwise eventually zero.
   Finite epsilon nets in the compact image show p_i z tends uniformly to z and e_i to zero.
6. In homogeneous coordinates apply lem-sfb-baire-closed-cover-interior in each group
   fibre to obtain a finite-field coset rectangle. A countable clopen basis enumerates
   rectangle/field certificates. The parameter sets A_j on which a certificate holds
   are closed and cover S; no open neighbourhood inside A_j is asserted.
7. Choose refining finite clopen partitions with mesh tending to zero. The union U_(j,i)
   of atoms meeting A_j decreases to A_j. The least eligible j<=i, with default 1, is a
   locally constant finite-range selector k_i, eventually the least valid j at each s.
8. Apply lem-sfb-bounded-finite-evaluation-rectangle-replacement for each certificate.
   On k_i=j set b_i=T_j e_i+h_(F_i) R_j e_i. Clopen gluing gives a continuous primitive
   db_i=e_i with norm at most the norm of e_i, uniformly tending to zero.
9. At fixed s the selector stabilizes. Both projections eventually fix its certificate
   field, so the homogeneous e_i vanishes on the rectangle. The replacement residual is
   then zero as an entire cochain. Its remaining T_j is a fixed finite sum of evaluations;
   each evaluation of e_i is eventually zero. Hence b_i(s,x) is eventually zero.
10. Use lem-sfb-normed-field-completion. The ultrametric inequality makes the primitive
    series uniformly Cauchy in the completion and its limit continuous. Step 9 makes
    each value a finite sum in Omega. The subspace metric makes it Omega-continuous.
    The finite differential commutes with the limit, giving db=z. Pull back from step 4.
11. Apply lem-weil-pbc-site-module-presheaf-sheafification-exact to the underlying abelian
    presheaves (constant ring Z). Sheafification preserves homology. Both complexes have
    scalar degree-zero cohomology and zero positive cohomology. The inclusion is the
    identity in degree zero and preserves module actions; it is a quasi-isomorphism.
12. Extend by zero in negative degrees and localize using sk-def-sfb-derived-categories.
    The specified inclusion becomes invertible. For K=1, d is zero in even degree and
    identity in odd positive degree. Finite K uses step 2. No completeness of Omega is used.
-/
theorem prime_to_ell_cochain_finite_quotient_descent (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E]
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ∀ (Q : Type u) [Group Q] [Fintype Q] [TopologicalSpace Q] [DiscreteTopology Q]
      (q : K →ₜ* Q), Function.Surjective q → Nat.Coprime (Nat.card Q) ell) :
    HasFiniteQuotientComparison E K ∧ HasFiniteQuotientComparison Ω K := by
  sorry

end Profinite.ContinuousScalarCochains
