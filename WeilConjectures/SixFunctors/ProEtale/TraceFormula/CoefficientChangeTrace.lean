/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.CoefficientChange

/-!
# Finite-level coefficient change of the traces in the trace formula

Let `ρ : R ⟶ S` be a homomorphism of finite commutative rings whose exponent is invertible in
the field `k`, and write `Ψ = - ⊗ᴸ_R S` for derived scalar extension of pro-étale sheaves.
For a Weil complex `(K, φ)` with coefficients in `R` on a geometric scheme `X` over `k`, compact
cohomology and the geometric stalks of the scalar extension `(Ψ K, Ψ φ)` are the scalar
extensions of those of `(K, φ)`, with matching Frobenius operators (blueprint
`sk-p-trace-coeff`), and the traces of the Frobenius operators over `S` are the images of the
traces over `R` (blueprint `thm-trf-finite-coefficient-map`).

## Main results

- `AlgebraicGeometry.ProEtale.WeilComplex.extendScalars_compactCohomology_stalk`: blueprint
  `sk-p-trace-coeff`.
- `AlgebraicGeometry.ProEtale.WeilComplex.trace_stalkFrobenius_extendScalars`: the identity
  `ρ(tr_R(F_{x,m} ∣ K_x̄)) = tr_S(F_{x,m} ∣ (Ψ K)_x̄)`.
- `AlgebraicGeometry.ProEtale.WeilComplex.trace_globalOperator_extendScalars`: the identity
  `ρ(tr_R(F_{c,m} ∣ RΓ_c(X, K))) = tr_S(F_{c,m} ∣ RΓ_c(X, Ψ K))`.

## Implementation notes

The induced map `ρ : End (𝟙_ D(s, R)) ⟶ End (𝟙_ D(s, S))` on the coefficient rings of the
categorical traces is `t ↦ ε ≫ Ψ t ≫ η`, for the unit `ε : 𝟙_ ⟶ Ψ 𝟙_` of a braided
monoidal structure on `Ψ` over the base. The braidings of the derived categories are the
temporary choice `DerivedBraiding`, so the braided monoidal structure of `Ψ` is an instance
hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme GeometricOperations

namespace WeilComplex

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] [Finite R] [Finite S]
  [DerivedBraiding (ModuleCat.{u + 1} R)] [DerivedBraiding (ModuleCat.{u + 1} S)]
  {k : Type u} [Field k] [HasInvertibleExponent R (Spec (.of k))]
  {G_R : GeometricOperations (ModuleCat.{u + 1} R) (Spec (.of k))}
  {G_S : GeometricOperations (ModuleCat.{u + 1} S) (Spec (.of k))}
  {X : Scheme.{u}} {aX : X ⟶ Spec (.of k)} [IsGeometric aX] [HasCompactification aX]

omit [HasCompactification aX] in
/-- The scalar extension of a Weil complex in `Dᵇctf` is in `Dᵇctf`. -/
lemma ctf_extendScalars (W : WeilComplex (A := ModuleCat.{u + 1} R) aX)
    (hW : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X W.obj) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X (W.extendScalars S).obj :=
  constructibleFiniteTor_leftDerivedSheafExtendScalars_of_isGeometricHom R S (.id aX) hW

variable (G_R G_S) in
/-- Two geometric operation packages over `R` and `S` compatible with scalar extension, the
stability of `Dᵇctf` under `Ψ` being
`AlgebraicGeometry.ProEtale.constructibleFiniteTor_leftDerivedSheafExtendScalars_of_isGeometricHom`.
-/
abbrev ExtendScalarsCompatibleOverField : Prop :=
  ExtendScalarsCompatible G_R G_S
    (fun hX _ ↦
      constructibleFiniteTor_leftDerivedSheafExtendScalars_of_isGeometricHom R S hX)

/-- **Finite-level coefficient change** (blueprint `sk-p-trace-coeff`). Let `(K, φ)` be a Weil
complex with coefficients in a finite ring `R` on a geometric scheme `X` over a field `k`, with
`K` bounded constructible of finite Tor amplitude, and let `R ⟶ S` be a homomorphism of finite
rings whose exponent is invertible in `k`. Then compact cohomology and the geometric stalks
commute with the scalar extension `Ψ = - ⊗ᴸ_R S`, compatibly with the Frobenius operators:
- the comparison `Ψ RΓ_c(X, K) ⟶ RΓ_c(X, Ψ K)` is an isomorphism, and it carries the scalar
  extension of the global Frobenius operator `F_{c,m}` of `(K, φ)` to the global Frobenius
  operator of `(Ψ K, Ψ φ)`;
- at every point `x` fixed by `Φ_m`, the isomorphism `(Ψ K)_x̄ ≅ Ψ (K_x̄)` carries the stalk
  Frobenius `F_{x,m}` of `(Ψ K, Ψ φ)` to the scalar extension of that of `(K, φ)`. -/
theorem extendScalars_compactCohomology_stalk (hG : ExtendScalarsCompatibleOverField G_R G_S)
    (W : WeilComplex (A := ModuleCat.{u + 1} R) aX)
    (hW : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X W.obj) (m : ℕ)
    [IsProper (W.frobeniusIterate m)] :
    IsIso ((rightDerivedLowerShriekExtendScalarsMap R S aX).app W.obj) ∧
      (L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).map
          (Correspondence.globalOperator G_R (W.graph G_R hW m) hW) ≫
        (rightDerivedLowerShriekExtendScalarsMap R S aX).app W.obj =
      (rightDerivedLowerShriekExtendScalarsMap R S aX).app W.obj ≫
        Correspondence.globalOperator G_S
          ((W.extendScalars S).graph G_S (W.ctf_extendScalars hW) m)
          (W.ctf_extendScalars hW) ∧
      ∀ (x : Spec (.of k) ⟶ X) (hx : x ≫ W.frobeniusIterate m = x),
        (W.extendScalars S).stalkFrobenius m x hx =
          (leftDerivedUpperStarExtendScalarsIso R S x).hom.app W.obj ≫
            (L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).map
              (W.stalkFrobenius m x hx) ≫
            (leftDerivedUpperStarExtendScalarsIso R S x).inv.app W.obj :=
  ⟨isIso_rightDerivedLowerShriekExtendScalarsMap_app R S aX hW,
    globalOperator_graph_extendScalars hG W hW m,
    fun x hx ↦ W.stalkFrobenius_extendScalars m x hx⟩

variable [(L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).Braided]

/-- **Coefficient change of the local traces** (blueprint `thm-trf-finite-coefficient-map`):
`ρ(tr_R(F_{x,m} ∣ K_x̄)) = tr_S(F_{x,m} ∣ (Ψ K)_x̄)`, where `ρ` is induced by the braided
monoidal functor `Ψ = - ⊗ᴸ_R S`. -/
theorem trace_stalkFrobenius_extendScalars (W : WeilComplex (A := ModuleCat.{u + 1} R) aX)
    (m : ℕ) (x : Spec (.of k) ⟶ X) (hx : x ≫ W.frobeniusIterate m = x)
    [HasRightDual ((L((x)^*[ModuleCat.{u + 1} R])).obj W.obj)]
    [HasRightDual ((L((x)^*[ModuleCat.{u + 1} S])).obj (W.extendScalars S).obj)]
    [HasRightDual ((L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).obj
      ((L((x)^*[ModuleCat.{u + 1} R])).obj W.obj))] :
    MonoidalCategory.trace ((W.extendScalars S).stalkFrobenius m x hx) =
      Functor.LaxMonoidal.ε (L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))) ≫
        (L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).map
          (MonoidalCategory.trace (W.stalkFrobenius m x hx)) ≫
        Functor.OplaxMonoidal.η (L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))) := by
  letI : HasRightDual
      ((L(sheafExtendScalars (algebraMap R S) X) ⋙ L((x)^*[ModuleCat.{u + 1} S])).obj W.obj) :=
    inferInstanceAs (HasRightDual ((L((x)^*[ModuleCat.{u + 1} S])).obj (W.extendScalars S).obj))
  letI : HasRightDual ((L((x)^*[ModuleCat.{u + 1} R]) ⋙
      L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).obj W.obj) :=
    inferInstanceAs (HasRightDual ((L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).obj
      ((L((x)^*[ModuleCat.{u + 1} R])).obj W.obj)))
  have h := MonoidalCategory.trace_conj ((leftDerivedUpperStarExtendScalarsIso R S x).app W.obj)
    ((L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).map (W.stalkFrobenius m x hx))
  rw [W.stalkFrobenius_extendScalars m x hx]
  exact h.trans (Functor.map_trace _ _)

/-- **Coefficient change of the global traces** (blueprint `thm-trf-finite-coefficient-map`):
`ρ(tr_R(F_{c,m} ∣ RΓ_c(X, K))) = tr_S(F_{c,m} ∣ RΓ_c(X, Ψ K))`, where `ρ` is induced by the
braided monoidal functor `Ψ = - ⊗ᴸ_R S`. Hence the finite-ring trace formula over `R` maps to
the one over `S`. -/
theorem trace_globalOperator_extendScalars (hG : ExtendScalarsCompatibleOverField G_R G_S)
    (W : WeilComplex (A := ModuleCat.{u + 1} R) aX)
    (hW : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X W.obj) (m : ℕ)
    [IsProper (W.frobeniusIterate m)]
    [HasRightDual ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX).obj W.obj)]
    [HasRightDual ((rightDerivedLowerShriek (ModuleCat.{u + 1} S) aX).obj
      (W.extendScalars S).obj)]
    [HasRightDual ((L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX).obj W.obj))] :
    MonoidalCategory.trace (Correspondence.globalOperator G_S
        ((W.extendScalars S).graph G_S (W.ctf_extendScalars hW) m) (W.ctf_extendScalars hW)) =
      Functor.LaxMonoidal.ε (L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))) ≫
        (L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).map
          (MonoidalCategory.trace (Correspondence.globalOperator G_R (W.graph G_R hW m) hW)) ≫
        Functor.OplaxMonoidal.η (L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))) := by
  obtain ⟨hc, hF, -⟩ := extendScalars_compactCohomology_stalk hG W hW m
  letI : HasRightDual ((L(sheafExtendScalars (algebraMap R S) X) ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} S) aX).obj W.obj) :=
    inferInstanceAs (HasRightDual
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} S) aX).obj (W.extendScalars S).obj))
  letI : HasRightDual ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX ⋙
      L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).obj W.obj) :=
    inferInstanceAs (HasRightDual ((L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) aX).obj W.obj)))
  have h := MonoidalCategory.trace_conj
    (asIso ((rightDerivedLowerShriekExtendScalarsMap R S aX).app W.obj)).symm
    ((L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).map
      (Correspondence.globalOperator G_R (W.graph G_R hW m) hW))
  simp only [Iso.symm_hom, Iso.symm_inv, asIso_inv, asIso_hom, reassoc_of% hF,
    IsIso.inv_hom_id_assoc] at h
  exact h.trans (Functor.map_trace _ _)

end WeilComplex

end AlgebraicGeometry.ProEtale
