/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/--
Existence of the exceptional inverse image on the localizing constructible categories.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-brown-representability-for-all-coefficient-rings/sk-prop-sf-existence/_section.md,
entire statement, and both paragraphs of `sk-prop-sf-existence.proof.md`; standing base
field: part-six-operations/prose-P1-01.md, final paragraph (finite or algebraically
closed), and det-def-sfb-dc-setting; Stacks Tags 0A8F, 0A8G, 0A8D.
The functor in the statement is the compact-support functor supplied by
`sk-prop-sf-comp-coherence`; its displayed adjunction is natural in both objects.  The
uniqueness clause is uniqueness of a right adjoint together with its counit.
(blueprint: sk-prop-sf-existence)

Proof:
1. Put `T_Z = Loc(Dctf(Z, Λ))` for `Z = X, Y`.  By sk-lem-brown-hypotheses, applied
   separately at `X` and `Y` in the standing setting, `T_Z` is locally small and
   triangulated with arbitrary small coproducts, `Dctf(Z, Λ)` is thick and essentially
   small, and a small skeleton is a set of compact generators.  By
   sk-prop-sf-comp-coherence, `F = Rf_! = Rp_* j_!` for the fixed compactification is
   exact, preserves direct sums, and maps `Dctf(X, Λ)` into `Dctf(Y, Λ)`.
2. For `N ∈ T_Y`, lem-pc-brown-hom-representability-locally-small represents the
   cohomological sum-to-product functor `M ↦ Hom(F M, N)` by `G_N ∈ T_X`;
   lem-sfb-right-adjoint-from-objectwise-representability assembles them into
   `G : T_Y ⥤ T_X` with `F ⊣ G`.  Set `f^! = G`.
3. lem-weil-pbc-adjunction-shift-compatibility-unique supplies the shifts on `G`
   compatible with unit and counit; lem-sf-triangulated-right-adjoint makes `G` exact;
   det-sp-unique-right-adjoint gives the unique counit-compatible isomorphism to any
   other right adjoint.
4. For a small family `N_α`, the comparison `⨁ G N_α ⟶ G (⨁ N_α)` induces a bijection on
   `Hom(S[n], -)` for each `S ∈ Dctf(X, Λ)`, since `S[n]` and `F(S[n])` are compact
   (def-pc-compact-object) and both sides are `⨁ Hom(F S[n], N_α)` by adjunction.
   lem-sf-localizing-hom-test in `T_X`, which is the localizing closure of `Dctf(X, Λ)`
   (sk-def-localizing-closure), makes it an isomorphism, also for the empty family.
-/
theorem sk_prop_sf_existence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∀ c : Compactification.BoundaryCompactification f,
      ∃ (h : ∀ K, localizingClosureProEtale Λ X K →
          localizingClosureProEtale Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)),
        ∃ (hX : (localizingClosureProEtale Λ X).IsTriangulated)
          (hY : (localizingClosureProEtale Λ Y).IsTriangulated),
          let _ := hX
          let _ := hY
          (localizingLowerShriek Λ c.obj.obj h).IsTriangulated ∧
          (∀ I : Type (u + 1),
            PreservesColimitsOfShape (Discrete I)
              (localizingLowerShriek Λ c.obj.obj h)) ∧
          ∃ G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
              (localizingClosureProEtale Λ X).FullSubcategory,
            ∃ s : G.CommShift ℤ,
              let _ := s
              G.IsTriangulated ∧
              (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G) ∧
              ∃ adj : localizingLowerShriek Λ c.obj.obj h ⊣ G,
                ∀ (J : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
                    (localizingClosureProEtale Λ X).FullSubcategory)
                  (adjJ : localizingLowerShriek Λ c.obj.obj h ⊣ J),
                  ∃! e : G ≅ J, ∀ N,
                    (localizingLowerShriek Λ c.obj.obj h).map
                        (e.hom.app N) ≫ adjJ.counit.app N = adj.counit.app N := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
