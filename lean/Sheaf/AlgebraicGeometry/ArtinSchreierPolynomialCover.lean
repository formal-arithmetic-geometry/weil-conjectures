/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# Surjective étale covers solving Artin--Schreier equations

Source: Stacks Project, Tag 03PL, proof by adjoining a root.
(blueprint: lem-sc-artin-schreier-polynomial-cover)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

namespace AlgebraicGeometry.Scheme

/-- Every global function in characteristic prime `p` acquires an Artin--Schreier
preimage on a surjective étale cover.
Source: Stacks Project, Tag 03PL, polynomial-cover argument.
(blueprint: lem-sc-artin-schreier-polynomial-cover)

Proof: Set `R = Γ(U, ⊤)` and `F = X^p - X - C t`. This is monic of degree `p`;
its derivative is `-1`. The pair `(F,1)` is standard étale, and its algebra is
isomorphic to `AdjoinRoot F`. The latter is faithfully flat, since the monic
polynomial has positive degree. Thus its spectrum is étale and surjective over
`Spec R`. Base change by `U.toSpecΓ` preserves both properties. Pull the class
of `X` back along the second projection, using the canonical global-sections
isomorphism of a spectrum. The polynomial relation and the pullback square give
the required equation. For the zero ring, every function is zero and the identity
cover suffices. -/
theorem exists_etale_surjective_artinSchreier_eq_appTop {U : Scheme.{u}}
    (p : ℕ) (hp : p.Prime) (hchar : (p : Γ(U, ⊤)) = 0) (t : Γ(U, ⊤)) :
    ∃ (V : Scheme.{u}) (f : V ⟶ U), Etale f ∧ Surjective f ∧
      ∃ ω : Γ(V, ⊤), ω ^ p - ω = f.appTop t := by
  classical
  by_cases htriv : Subsingleton Γ(U, ⊤)
  · have := htriv
    exact ⟨U, 𝟙 U, inferInstance, inferInstance, 0, Subsingleton.elim _ _⟩
  have : Nontrivial Γ(U, ⊤) := not_subsingleton_iff_nontrivial.mp htriv
  let F : Γ(U, ⊤)[X] := X ^ p - X - C t
  have hlt : (X : Γ(U, ⊤)[X]).degree < (X ^ p : Γ(U, ⊤)[X]).degree := by
    rw [degree_X, degree_X_pow]
    exact_mod_cast hp.one_lt
  have hbase : (X ^ p - X : Γ(U, ⊤)[X]).degree = (p : WithBot ℕ) := by
    rw [degree_sub_eq_left_of_degree_lt hlt, degree_X_pow]
  have hc : (C t).degree < (X ^ p - X : Γ(U, ⊤)[X]).degree := by
    rw [hbase]
    exact degree_C_le.trans_lt (by exact_mod_cast hp.pos)
  have hmonic : F.Monic := ((monic_X_pow p).sub_of_left hlt).sub_of_left hc
  have hdegF : F.degree = (p : WithBot ℕ) := by
    dsimp [F]
    rw [degree_sub_eq_left_of_degree_lt hc, hbase]
  have hderiv : derivative F = -1 := by
    simp [F, derivative_sub, derivative_X_pow, hchar]
  let P : StandardEtalePair Γ(U, ⊤) :=
    { f := F, monic_f := hmonic, g := 1,
      cond := ⟨-1, 0, 0, by rw [hderiv]; simp⟩ }
  let e : P.Ring ≃ₐ[Γ(U, ⊤)] AdjoinRoot F :=
    .ofAlgHom
      (P.lift (AdjoinRoot.root F)
        ⟨by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], by simp [P]⟩)
      (AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) P.X P.hasMap_X.1)
      (AdjoinRoot.algHom_ext (by simp [AdjoinRoot.liftAlgHom_root]))
      (P.hom_ext (by simp [AdjoinRoot.liftAlgHom_root]))
  have : Algebra.IsStandardEtale Γ(U, ⊤) (AdjoinRoot F) :=
    Algebra.IsStandardEtale.of_equiv e
  let φ : Γ(U, ⊤) ⟶ CommRingCat.of (AdjoinRoot F) :=
    CommRingCat.ofHom (algebraMap _ _)
  have : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hdeg : F.degree ≠ 0 := by
    rw [hdegF]
    exact_mod_cast hp.ne_zero
  have : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr
      (AdjoinRoot.faithfullyFlat_of_monic hmonic hdeg))).2
  let f := pullback.fst U.toSpecΓ (Spec.map φ)
  let g := pullback.snd U.toSpecΓ (Spec.map φ)
  let ω := g.appTop ((ΓSpecIso _).inv (AdjoinRoot.root F))
  refine ⟨_, f, inferInstance, inferInstance, ω, ?_⟩
  have hroot : AdjoinRoot.root F ^ p - AdjoinRoot.root F = φ t := by
    have h := AdjoinRoot.eval₂_root F
    simpa only [F, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, sub_eq_zero,
      φ, CommRingCat.hom_ofHom, AdjoinRoot.algebraMap_eq] using h
  change ω ^ p - ω = f.appTop t
  rw [pullback_fst_toSpecΓ_appTop]
  change ω ^ p - ω = g.appTop ((ΓSpecIso _).inv (φ t))
  rw [← hroot, map_sub, map_pow, map_sub, map_pow]

end AlgebraicGeometry.Scheme
