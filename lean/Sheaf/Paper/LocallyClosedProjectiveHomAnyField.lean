/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.SixFunctors.FlatModelGeneration
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The locally closed projective generator calculation

Source: Bhatt–Scholze, The pro-étale topology for schemes, Lemmas 6.7.11 and 6.7.13.
(blueprint: lem-per-locally-closed-projective-hom-any-field).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- Ambient Hom from a locally closed finite-projective sheaf preserves bounded
constructibility. Only the second input's bounded constructibility is needed.

Source: Bhatt–Scholze, Lemma 6.7.13, generator calculation, using Lemmas 6.7.11
and 6.7.2 (blueprint: lem-per-locally-closed-projective-hom-any-field).

Proof: Put A = O_E/varpi^n. The DVR description makes A finite and Noetherian,
and ell^n kills A, with ell invertible in k. All the schemes below are Noetherian
and finite type over k. Factor a as the open immersion j into its scheme-theoretic
closure followed by the closed immersion g into X. Its canonical extension is g_*j_!.
The support triangle g_*Rg^!M -> M -> Rh_*h^*M, where h is the open complement,
shows that g_*Rg^!M is bounded constructible: exact inverse image preserves its
finite constructible strata, and finite-type direct image preserves bounded
constructibility by finite-ring étale origin, étale finiteness and qcqs direct-image
comparison. Pull back by exact g^*, and use g^*g_* = 1, to get Rg^!M bounded
constructible. Thus j^*Rg^!M is bounded constructible too. On S, perfect duality
identifies RHom(L,j^*Rg^!M) with L^dual tensor j^*Rg^!M. On trivializing covers,
L and its dual are finite-projective summands of finite free modules. Tensoring
with the dual is exact and a summand of a finite sum, preserving bounds and finite
constructible local models. Ambient adjunction for g and j identifies
RHom(g_*j_!L,M) with Rg_*Rj_*RHom(L,j^*Rg^!M). Finite-type direct image again
proves the conclusion. No cohomological-dimension bound on k is used. For empty S
or X, or zero L or M, the calculation gives zero, and n = 1 is included. -/
theorem locallyClosedProjective_internalHom_constructible_anyField
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsNoetherian X]
    (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
    (L : proEtaleRingModules S (proEtaleConstantRing S (Padic.coefficientExtensionRing l E n)))
    (_hL : FlatModelProEtaleLisseProjective S (Padic.coefficientExtensionRing l E n) L)
    (M : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (_hM : intrinsicFiniteTorsionConstructible l E n hn X M) :
    intrinsicFiniteTorsionConstructible l E n hn X
      ((derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj
            ((@flatModelProEtaleExtension S X inferInstance
              (Padic.coefficientExtensionRing l E n) inferInstance
              (Padic.finite_coefficientExtensionRing l E n hn) a ha).obj L)), M)) := by sorry

end AlgebraicGeometry.Scheme
