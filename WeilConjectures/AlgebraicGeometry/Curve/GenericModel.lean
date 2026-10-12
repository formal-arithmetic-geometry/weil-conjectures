/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# A generic curve model for a projective family of dimension at most one

Let `f : X ⟶ S` be projective with `S` integral of finite type over a field and geometric fibres
of dimension at most one. Over a nonempty open of `S` and after a finite surjective base change
`S' ⟶ S`, the reduced family `T = (X ×_S S')_red` is the target of a finite surjection
`ν : ∐ₐ Yₐ ⟶ T` from a finite disjoint union of smooth projective curve families and finite
étale families, which is an isomorphism outside a closed subscheme `D ⊆ T` finite over `S'`
(`lem-fin-generic-curve-model`). The construction normalizes the geometric generic fibre and
spreads the result out.

## Main statements

- `AlgebraicGeometry.exists_isFinite_sigmaDesc_genericCurveModel`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `lem-fin-generic-curve-model`: A generic curve model with finite comparison
boundary.

Let `S` be integral of finite type over a field `k`, `f : X ⟶ S` projective (`f = π ∘ i` for a
closed immersion `i : X ⟶ ℙ(n; S)`) with geometric fibres of dimension at most one. There are

* a nonempty open `U ⊆ S`, an integral scheme `S'` and a finite surjection `p : S' ⟶ U`;
* the reduced scheme `T = (X_U ×_U S')_red`, given with its surjective closed immersion
  `t : T ⟶ X_U ×_U S'`;
* finitely many schemes `Yₐ` over `S'` and a finite surjection `ν : ∐ₐ Yₐ ⟶ T`, each `Yₐ ⟶ S'`
  being either projective and smooth of relative dimension one, or finite étale;
* a closed subscheme `d : D ⟶ T`, finite over `S'`, outside of which `ν` is an isomorphism. -/
theorem exists_isFinite_sigmaDesc_genericCurveModel {k : Type u} [Field k] {X S : Scheme.{u}}
    [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i]
    (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1) :
    ∃ (U : S.Opens) (_ : U ≠ ⊥) (S' : Scheme.{u}) (_ : IsIntegral S') (p : S' ⟶ U.toScheme)
      (_ : IsFinite p) (_ : Surjective p)
      (T : Scheme.{u}) (t : T ⟶ pullback (f ∣_ U) p) (_ : IsClosedImmersion t)
      (_ : Surjective t) (_ : IsReduced T)
      (ι : Type u) (_ : Finite ι) (Y : ι → Scheme.{u}) (ν : ∐ Y ⟶ T) (_ : IsFinite ν)
      (_ : Surjective ν) (D : Scheme.{u}) (d : D ⟶ T) (_ : IsClosedImmersion d),
      IsFinite (d ≫ t ≫ pullback.snd _ _) ∧
      IsIso (ν ∣_ ⟨(Set.range d.base)ᶜ, d.isClosedEmbedding.isClosed_range.isOpen_compl⟩) ∧
      ∀ a : ι,
        ((∃ (m : Type u) (_ : Finite m) (j : Y a ⟶ ℙ(m; S')), IsClosedImmersion j ∧
            j ≫ ℙ(m; S') ↘ S' = Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd _ _) ∧
          SmoothOfRelativeDimension 1 (Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd _ _)) ∨
        (IsFinite (Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd _ _) ∧
          Etale (Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd _ _)) := by
  sorry

end AlgebraicGeometry
