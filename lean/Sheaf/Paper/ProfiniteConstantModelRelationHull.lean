/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ProfiniteFiniteConstantLocalModel
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.Paper.ComponentRelativeProfiniteSite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.ExtremallyDisconnected
import Sheaf.CategoryTheory.RingedSiteFreeMatrixScalarExtension

/-! # Continuous relation kernels in the finite-model derived hull

Source: Hemo--Richarz--Scholbach, Example 3.1, Remark 3.2, Examples 3.6 and 4.2,
Section 4.1; agent-formulated generation obligation, exact reference WANTED
(blueprint: lem-sfb-profinite-constant-model-relation-hull).

All categories below are ordinary uncompleted internal-module derived categories.
Finite presentations are chosen on the condensed point, hence use scalar matrices.
Their pullbacks to the slice are the scalar models in the node. The map between these
pullbacks is arbitrary; it is not required to be the pullback of a map on the point.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The classes intersected in the definition of the profinite finite-model hull.
Products are universal limiting fans in the ordinary derived category. Filtered
colimits are universal colimiting cocones in actual complexes of module sheaves,
with one common termwise lower bound, before applying localization.
Source: the hull paragraph of the agent-formulated relation-kernel obligation;
HRS Section 4.1 (blueprint: lem-sfb-profinite-constant-model-relation-hull). -/
def IsProfiniteModelGenerationClass (P : Profinite.{u})
    (H : ObjectProperty (DerivedCategory
      (Mod (Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1})
        (profiniteCoefficient Λ P)))) : Prop :=
  H.IsTriangulated ∧ H.IsClosedUnderIsomorphisms ∧
  (∀ (K L : DerivedCategory
      (Mod (Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1})
        (profiniteCoefficient Λ P)))
    (i : K ⟶ L) (p : L ⟶ K), i ≫ p = 𝟙 K → H L → H K) ∧
  (∀ (I : Type (u + 1))
    (K : I → DerivedCategory
      (Mod (Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1})
        (profiniteCoefficient Λ P)))
    (c : Fan K), IsLimit c → (∀ i : I, H (K i)) → H c.pt) ∧
  (∀ F : Mod (Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1})
      (profiniteCoefficient Λ P),
    HasFiniteConstantProfiniteLocalModel Λ P F → H ((DerivedCategory.singleFunctor _ 0).obj F)) ∧
  (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1})
        (profiniteCoefficient Λ P)) ℤ)
    (a : ℤ) (c : Cocone D), IsColimit c →
    (∀ i : I, (D.obj i).IsStrictlyGE a) →
    (∀ i : I, H (DerivedCategory.Q.obj (D.obj i))) → H (DerivedCategory.Q.obj c.pt))

/-- The intersection of all full replete classes containing finite scalar local models
and closed under precisely the operations specified in `IsProfiniteModelGenerationClass`.
Source: the hull paragraph of the agent-formulated relation-kernel obligation;
HRS Section 4.1 (blueprint: lem-sfb-profinite-constant-model-relation-hull). -/
def profiniteModelGenerationHull (P : Profinite.{u}) : ObjectProperty (DerivedCategory
    (Mod (Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1})
      (profiniteCoefficient Λ P))) :=
  fun K ↦ ∀ H : ObjectProperty (DerivedCategory
    (Mod (Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1})
      (profiniteCoefficient Λ P))), IsProfiniteModelGenerationClass Λ P H → H K

/-- The abelian sheaf kernel of an arbitrary arrow between scalar models belongs to
exactly the stated hull. Finite presentations on the condensed point are cokernels of
finite scalar matrices, so they encode all finitely presented scalar modules, without
allowing continuous-function matrices in their presentations.

Source: HRS Example 3.1, Remark 3.2, Examples 3.6 and 4.2, Section 4.1;
agent-formulated relation-kernel obligation, exact reference WANTED
(blueprint: lem-sfb-profinite-constant-model-relation-hull).

Proof plan from the DAG:
1. For finite A, choose scalar generators of B. Their images are continuous maps into
finite discrete C. A common finite clopen partition makes them all constant, hence makes
v scalar on each part. Its finite kernel is finitely presented over the finite ring,
so the kernel is itself a finite scalar local model. This includes the zero ring.
2. For O_E (and Z_ell), use lem-sfb-profinite-integral-scalar-realization. Reduce v
modulo pi^k and take N_k = ker v_k. A finite clopen partition makes each finite map
constant, so N_k is a finite scalar local model. The actual quotient maps give a strict
tower and integral realization identifies ker v with its sheaf inverse limit.
3. Apply lem-sfb-relative-finite-bundle-roos to this tower, using compact finite solution
bundles. Its triangle has (ker v)[0] and two derived products of the N_k[0]. Products,
shifts and triangle extensions give membership; surjective transitions or uniform
stabilization are not assumed.
4. For E (including Q_ell), choose scalar bases. Use
lem-sfb-ringed-site-free-matrix-scalar-extension to express the actual v by one matrix
of continuous E-valued functions on P, acting by restriction on every profinite test.
5. Use lem-sfb-stonean-continuous-field-diagonalization to write D = L F U with L,U
invertible continuous matrices. The free-matrix correspondence identifies ker F with
ker D, which is the sum of the rank-one annihilators and the remaining free summands.
Apply lem-sfb-profinite-field-scalar-annihilator-hull to each diagonal entry, with the
class defined above. The free remainder is a generator; finite sums follow from split
triangles. Repleteness finishes. Empty spaces and zero modules use empty matrices and
sums; zero and identity arrows give respectively the source and zero.
-/
theorem profinite_constant_model_relation_mem_hull
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (P : Profinite.{u}) [ExtremallyDisconnected P]
    (B C : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hB : Mod.IsFinitelyPresented Λ B) (hC : Mod.IsFinitelyPresented Λ C)
    (v : (((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P).mapMod Λ).obj B ⟶
      (((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P).mapMod Λ).obj C) :
    profiniteModelGenerationHull Λ P ((DerivedCategory.singleFunctor _ 0).obj (kernel v)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
