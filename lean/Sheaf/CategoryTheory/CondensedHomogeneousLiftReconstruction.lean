/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective
public import Sheaf.CategoryTheory.UniverseCondensedActionModule
public import Sheaf.CategoryTheory.CondensedInternalBarData
import Sheaf.CategoryTheory.CondensedFreeLinearizationTensor

/-! # Reconstruction of internal homogeneous-function lifts

Source: blueprint direct-image stability, paragraph (3), internal homogeneous-function
helper, reconstruction and extension steps; Stacks Project Tag 03EO (2)
(blueprint: lem-sfb-internal-homogeneous-lift-reconstruction).

The model, slice evaluation, free generators and relative pure tensors are the existing
constructions. The result includes existence of the normalized action and reconstructs
an equivariant lift from any internal tensor map, without an injectivity hypothesis.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace Profinite.CondensedAction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The normalized homogeneous action exists. For every normalized model and internal
tensor map beta, there is an equivariant internal linear lift with the specified formula
on every slice, its identity-coordinate normalization, and its extension identity.

Source: blueprint direct-image stability, paragraph (3), internal homogeneous-function
helper, old steps 6--8; Stacks Project Tag 03EO (2)
(blueprint: lem-sfb-internal-homogeneous-lift-reconstruction).

Proof:
1. A restriction-natural family F_T(x,v), linear in v, gives a map A[X] tensor V to W.
Indeed on each slice x gives a linear map V|_S to W|_S and thus an internal-Hom section.
Use the free-generator bijection of lem-sfb-condensed-free-linearization-tensor, then
uncurry by lem-pc-sheaf-modules-tensor-closed and symmetry. These bijections also show
that equality is detected by all slice evaluations; no sectionwise freeness is asserted.
2. With Q = G^(n+1) and K = Hom_A(A[Q],UJ), apply this construction to
F_T((k,q),c) = k acting on c(k^(-1)q). Free-product tensor comparison, associativity,
symmetry and currying give the action on K. It is natural and linear in c.
3. Evaluate both action laws on every slice. The equality
k(l c(l^(-1)k^(-1)q)) = (kl)c((kl)^(-1)q), and the unit law for J, give the action laws
on K by slice detection. The identity identification supplies a normalized model.
4. Apply step 1 to B_T(q,m) = g_0 beta([g_0^(-1)g_1,...,g_0^(-1)g_n]
tensor (g_0^(-1)m)). Restriction commutes with every operation and the expression is
linear in m. Transpose to UM to K, and compose with the inverse identification for any
normalized model H. This gives the first displayed equality for every T to S.
5. To check equivariance, use (k^(-1)g_0)^(-1)(k^(-1)g_i) = g_0^(-1)g_i and
(k^(-1)g_0)^(-1) = g_0^(-1)k. The action laws identify k b(m)(k^(-1)q) with b(km)(q).
Detection by all slice evaluations gives an equivariant internal-module morphism b.
6. Setting g_0 = 1 gives normalization. For an equivariant i and h with the prescribed
identity-coordinate values, substitute g_0^(-1)x in that identity. Equivariance of i
makes the reconstruction g_0 h(g_0^(-1)x)(1,r), where r_i = g_0^(-1)g_i.
Equivariance of h and its normalized homogeneous action turn this into h(x)(q).
Slice detection proves i followed by b equals h; monicity and injectivity are unused.
7. At n = 0 the tail is the unique empty tuple and A[G^0] is A[1], isomorphic to A.
For trivial G the formula is the ordinary transpose at the terminal parameter. On the
empty test all module sections are unique; for zero coefficients all sections vanish.
The construction and cancellation identities apply in each of these cases.
-/
theorem homogeneous_lift_reconstruction (J : ActionModule R G) (n : ℕ) :
    Nonempty (HomogeneousFunctions R G J n) ∧
    ∀ (H : HomogeneousFunctions R G J n) (M : ActionModule R G)
      (β : InternalBar.freePower R G n ⊗ M.module ⟶ J.module),
      ∃ b : M ⟶ H.object,
        (∀ (S : Profinite.{u}) (m : sectionModule R M.module S)
          (T : Profinite.{u}) (f : T ⟶ S) (q : Fin (n + 1) → C(T, G)),
          homogeneousEvaluate R G J n S
            ((H.internalHom.hom.val.app (op S)).hom (InternalBar.onSections R b.val S m))
            T f q =
          J.act T (q 0)
            (InternalBar.onSections R β T
              (InternalBar.pureTensor R (InternalBar.freePower R G n) M.module T
                (InternalBar.generator R G n T (fun i ↦ (q 0)⁻¹ * q i.succ))
                (M.act T (q 0)⁻¹ ((M.module.X.obj.map f.op).hom m))))) ∧
        (∀ (S : Profinite.{u}) (m : sectionModule R M.module S)
          (T : Profinite.{u}) (f : T ⟶ S) (t : Fin n → C(T, G)),
          homogeneousEvaluate R G J n S
            ((H.internalHom.hom.val.app (op S)).hom (InternalBar.onSections R b.val S m))
            T f (Fin.cons 1 t) =
          InternalBar.onSections R β T
            (InternalBar.pureTensor R (InternalBar.freePower R G n) M.module T
              (InternalBar.generator R G n T t) ((M.module.X.obj.map f.op).hom m))) ∧
        (∀ (N : ActionModule R G) (i : N ⟶ M) (h : N ⟶ H.object),
          (∀ (S : Profinite.{u}) (x : sectionModule R N.module S)
            (T : Profinite.{u}) (f : T ⟶ S) (t : Fin n → C(T, G)),
            InternalBar.onSections R β T
              (InternalBar.pureTensor R (InternalBar.freePower R G n) M.module T
                (InternalBar.generator R G n T t)
                (InternalBar.onSections R i.val T ((N.module.X.obj.map f.op).hom x))) =
            homogeneousEvaluate R G J n S
              ((H.internalHom.hom.val.app (op S)).hom
                (InternalBar.onSections R h.val S x)) T f (Fin.cons 1 t)) →
          i ≫ b = h) := by
  sorry

end Profinite.CondensedAction
