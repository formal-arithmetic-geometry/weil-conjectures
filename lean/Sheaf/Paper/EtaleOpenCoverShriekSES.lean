/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-! # Open-cover short exact sequence for étale extension by zero

Source: Stacks Project, `more-etale.tex`, Tag 0GKK, lemma-mayer-vietoris-shriek
(blueprint: lem-weil-pbc-etale-open-cover-shriek-ses).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map `ι_U : k_{W!}(F|_W) → k_{U!}(F|_U)` from the extension by zero on the
overlap to the extension by zero on the first open: the composition isomorphism
`(a ≫ k_U)_! ≅ k_{U!} ∘ a_!`, then `k_{U!}` applied to `a_!` of the restriction isomorphism
`(a ≫ k_U)^* F ≅ a^*(F|_U)` followed by the counit of `a_! ⊣ a^*`. It is the
sheafification of the presheaf map that is the identity of `F(E)` on every étale `E → X`
factoring through `W` and zero otherwise.
Source: Stacks Project, `more-etale.tex`, Tag 0GKK, lemma-mayer-vietoris-shriek, the maps
of the short exact sequence (blueprint: lem-weil-pbc-etale-open-cover-shriek-ses). -/
noncomputable def etaleOpenCoverIotaU
    {Λ : Type (u + 1)} [CommRing Λ]
    {X U W : Scheme.{u}} (jU : U ⟶ X) (a : W ⟶ U) (jW : W ⟶ X)
    [IsOpenImmersion jU] [IsOpenImmersion a] [IsOpenImmersion jW]
    (hUa : a ≫ jU = jW)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jW).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) jW).obj F) ⟶
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jU).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) jU).obj F) :=
  by
    subst jW
    exact (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) a jU).hom.app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a ≫ jU)).obj F) ≫
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jU).map
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a jU (a ≫ jU) rfl).hom.app F) ≫
        (Etale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) a).counit.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) jU).obj F))

/-- The canonical map `ι_V : k_{W!}(F|_W) → k_{V!}(F|_V)` from the extension by zero on the
overlap to the extension by zero on the second open, built as `etaleOpenCoverIotaU` with
`b : W ⟶ V` and `k_V` in place of `a` and `k_U`.
Source: Stacks Project, `more-etale.tex`, Tag 0GKK, lemma-mayer-vietoris-shriek, the maps
of the short exact sequence (blueprint: lem-weil-pbc-etale-open-cover-shriek-ses). -/
noncomputable def etaleOpenCoverIotaV
    {Λ : Type (u + 1)} [CommRing Λ]
    {X V W : Scheme.{u}} (jV : V ⟶ X) (b : W ⟶ V) (jW : W ⟶ X)
    [IsOpenImmersion jV] [IsOpenImmersion b] [IsOpenImmersion jW]
    (hVb : b ≫ jV = jW)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jW).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) jW).obj F) ⟶
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jV).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) jV).obj F) :=
  by
    subst jW
    exact (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) b jV).hom.app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (b ≫ jV)).obj F) ≫
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jV).map
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) b jV (b ≫ jV) rfl).hom.app F) ≫
        (Etale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) b).counit.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) jV).obj F))

/-- The counit `ε_U : k_{U!}(F|_U) → F` of `k_{U!} ⊣ k_U^*`, the sheafification of the
identity of `F(E)` on every étale `E → X` factoring through `U`.
Source: Stacks Project, `more-etale.tex`, Tag 0GKK, lemma-mayer-vietoris-shriek, the maps
of the short exact sequence (blueprint: lem-weil-pbc-etale-open-cover-shriek-ses). -/
noncomputable def etaleOpenCoverEpsilonU
    {Λ : Type (u + 1)} [CommRing Λ]
    {X U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jU).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) jU).obj F) ⟶ F :=
  (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) jU).counit.app F

/-- The counit `ε_V : k_{V!}(F|_V) → F` of `k_{V!} ⊣ k_V^*`, the sheafification of the
identity of `F(E)` on every étale `E → X` factoring through `V`.
Source: Stacks Project, `more-etale.tex`, Tag 0GKK, lemma-mayer-vietoris-shriek, the maps
of the short exact sequence (blueprint: lem-weil-pbc-etale-open-cover-shriek-ses). -/
noncomputable def etaleOpenCoverEpsilonV
    {Λ : Type (u + 1)} [CommRing Λ]
    {X V : Scheme.{u}} (jV : V ⟶ X) [IsOpenImmersion jV]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jV).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) jV).obj F) ⟶ F :=
  (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) jV).counit.app F

/-- The extension-by-zero short exact sequence associated with a two-open cover.
Source: Stacks Project, `more-etale.tex`, Tag 0GKK, lemma-mayer-vietoris-shriek.
(blueprint: lem-weil-pbc-etale-open-cover-shriek-ses).

Proof (Stacks 0GKK: the sequence is checked on stalks), step by step:
1. On the presheaves `P_T = k_{T,p!}(F|_T)` the maps `P_W → P_T → F` commute with
   restrictions, and both composites `P_W → F` (for `T = U, V`) are the identity on `F(E)`
   for `E` factoring through `W` and zero otherwise. By uniqueness in sheafification the
   sheafified composites agree, so `(ε_U + ε_V) ∘ (ι_U, -ι_V) = 0`: a complex.
2. For a geometric point `x̄` put `A = F_x̄`. If `x̄ ∈ T`, neighbourhoods factoring through
   `T` are cofinal (`E ×_X T` for a pointed étale `E`, `T → X` étale), so
   `(F|_T)_x̄ → F_x̄` is bijective; by the stalks of extension by zero
   `(k_{T!}(F|_T))_x̄` is `A` if `x̄ ∈ T` and `0` otherwise, germ to the same germ. Hence
   `ε_T` is the identity of `A` for `x̄ ∈ T` and `ι_T` the identity for `x̄ ∈ W`.
3. Stalks are exact, so they preserve the biproduct. On `W` the stalk sequence is
   `0 → A → A ⊞ A → A → 0`, `a ↦ (a, -a)`, `(b, c) ↦ b + c`; on `U \ V` it is
   `0 → 0 → A ⊞ 0 → A → 0`; on `V \ U` it is `0 → 0 → 0 ⊞ A → A → 0`. All are exact.
4. Geometric stalk functors are exact and jointly reflect isomorphisms, so the categorical
   criterion (`JointlyReflectIsomorphisms.shortExact_iff`) makes the underlying abelian
   sequence short exact. No finiteness or Noetherian hypothesis is used.
5. Via the constant-ring module equivalence, the forgetful functor to abelian sheaves is
   exact and reflects isomorphisms; the same criterion gives short exactness of the
   `Λ`-module sequence.
6. For `α : F ⟶ G` the presheaf squares of inclusions and counits commute; sheafification
   carries them to the four naturality squares, and the pair with sign and the sum then
   commute with `α`. -/
theorem etale_openCover_lowerShriek_shortExact
    {Λ : Type (u + 1)} [CommRing Λ]
    (X U V W : Scheme.{u})
    (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    (a : W ⟶ U) (b : W ⟶ V)
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    [IsOpenImmersion a] [IsOpenImmersion b]
    (hUa : a ≫ jU = jW) (hVb : b ≫ jV = jW)
    (hsq : IsPullback a b jU jV)
    (hcover : ∀ x : X,
      (∃ y : U, jU.base y = x) ∨ ∃ y : V, jV.base y = x)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ hcomplex : biprod.lift (etaleOpenCoverIotaU jU a jW hUa F)
        (-(etaleOpenCoverIotaV jV b jW hVb F)) ≫
        biprod.desc (etaleOpenCoverEpsilonU jU F) (etaleOpenCoverEpsilonV jV F) = 0,
      (ShortComplex.mk
      (biprod.lift (etaleOpenCoverIotaU jU a jW hUa F)
        (-(etaleOpenCoverIotaV jV b jW hVb F)))
      (biprod.desc (etaleOpenCoverEpsilonU jU F) (etaleOpenCoverEpsilonV jV F))
      hcomplex).ShortExact ∧
      ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (α : F ⟶ G),
        etaleOpenCoverIotaU jU a jW hUa F ≫
            (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jU).map
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) jU).map α) =
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jW).map
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) jW).map α) ≫
            etaleOpenCoverIotaU jU a jW hUa G ∧
        etaleOpenCoverIotaV jV b jW hVb F ≫
            (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jV).map
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) jV).map α) =
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jW).map
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) jW).map α) ≫
            etaleOpenCoverIotaV jV b jW hVb G ∧
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jU).map
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) jU).map α) ≫
            etaleOpenCoverEpsilonU jU G =
          etaleOpenCoverEpsilonU jU F ≫ α ∧
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) jV).map
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) jV).map α) ≫
            etaleOpenCoverEpsilonV jV G =
          etaleOpenCoverEpsilonV jV F ≫ α := by
  sorry

end AlgebraicGeometry
