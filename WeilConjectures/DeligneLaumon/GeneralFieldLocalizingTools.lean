/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedOpenDerivedCalculus
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.Perfect

/-! # General-field localizing tools

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
  sk-thm-purity-transport.proof.md, coefficient transport Steps 1--4; general-field
  comparison is WANTED (blueprint: lem-dla1-general-field-localizing-tools).

The statement records the characteristic-free proper direct-image, Brown representability,
and open-immersion assertions for the native finite-extension and finite-subextension
condensed coefficient rings. All categories and functors are the existing ordinary
module-object derived categories and their recorded localizing closures.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Brown representability on the specified localizing closure, with its inherited
triangulated structure made explicit so that the functor's cohomological condition is
well-typed: every homological functor `L_Λ(S)ᵒᵖ ⥤ Ab` sending small coproducts of `L_Λ(S)`
to products is isomorphic to `Hom(-, G)` for an object `G` of `L_Λ(S)`. This is only an
interface for the localizing-closure assertion below; it chooses no additional category or
functor.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
sk-thm-purity-transport.proof.md, Steps 2-3, agent assembly of the general-field localizing
tools; the Brown clause of the node statement
(blueprint: lem-dla1-general-field-localizing-tools). -/
def BrownRepresentableOnLocalizingClosure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (H : (localizingClosureProEtale Λ S).FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : Prop :=
  ∃ hTri : (localizingClosureProEtale Λ S).IsTriangulated,
    letI := hTri
    ∀ [H.IsHomological],
      (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) H) →
        ∃ G : (localizingClosureProEtale Λ S).FullSubcategory,
          Nonempty (H ≅ preadditiveYoneda.obj G)

/-- Proper direct image, Brown representability, and open localization for native condensed
coefficients over a perfect field.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
sk-thm-purity-transport.proof.md, Steps 2-3, agent assembly of the general-field localizing
tools (blueprint: lem-dla1-general-field-localizing-tools).

Proof.
1. `Spec k` is a one-point Noetherian scheme, so `T` and `S` are Noetherian and qcqs
  (lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-qcqs-over-affine). The internal
  `Λ_T`-module heart is Grothendieck abelian (lem-weil-pbc-sheaf-tensor-closed,
  lem-sfb-modobj-grothendieck) with K-injective resolutions (det-def-sfb-derived-categories).
  The hull is locally small, triangulated, with ambient coproducts
  (h1-brown-hypotheses-structural); `C_Λ(T)` is thick with a set of representatives
  (det-brown-hypotheses-small), equal to the bounded constructibles for these field
  coefficients (det-def-localizing-closure-ctf-equals-bc). The same holds on a quasi-compact
  open of `T`.
2. For a constructible `M` in degree zero every `H^q(Rp_* M[0])` has finite constant models
  (lem-dla1-proper-sheaf-constant-model-finiteness); the heart bound of
  lem-sfb-proper-serre-heart-continuous / -qbar is a common upper bound, and `M[0]` bounded
  below gives the lower bound, so `Rp_* M[0] ∈ C_Λ(S)`.
3. Finite truncation dévissage (def-kun-truncations), triangulatedness of the total derived
  pushforward (lem-pc-right-derived-functor-triangulated) and thickness give
  `Rp_* C_Λ(T) ⊆ C_Λ(S)`.
4. Finite constant models are locally finitely presented, so `L_Λ(T)` lies in the hull of
  lem-dla1-proper-heart-localizing-coproduct-criterion, whose heart inputs are those of
  lem-sfb-proper-serre-heart-continuous / -qbar; the coproduct comparison is invertible for
  every family (including the empty one), and the conditional assertion of
  det-proper-image-localizing-proper gives the coproduct-preserving restriction
  `Rp_* : L_Λ(T) → L_Λ(S)`.
5. A set of representatives `G` of `C_Λ(S)` has `Loc(G) = L_Λ(S)` (sk-def-localizing-closure);
  lem-dla1-set-generated-derived-brown represents every homological functor sending
  coproducts to products.
6. For `j` quasi-compact open, `j_!` and `j^*` are exact termwise derived functors with
  `j_! ⊣ j^*` (lem-pod-condensed-open-derived-calculus); extending a finite constructible
  stratification of `U` by the closed complement (model zero), resp. intersecting one of `T`
  with `U`, shows that both preserve bounded constructibles, hence `C_Λ`.
7. The objects of `L_Λ(U)` with `j_!`-image in `L_Λ(T)` form a localizing subcategory
  containing the generators, hence all of `L_Λ(U)`; likewise for `j^*`. Both hulls are full,
  so the ambient adjunction restricts. The empty open and the zero generator are no
  exception, and no step restricts the characteristic. -/
theorem generalFieldLocalizingTools (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [PerfectField k] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {T S : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k))]
    [S.Over (Spec (CommRingCat.of k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k))]
    [IsSeparated (S ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))]
    (p : T ⟶ S) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    {U : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] :
    (∀ K, localizingClosureProEtale Λ T K →
      localizingClosureProEtale Λ S
        ((moduleObjectDerivedPushforward Λ p).obj K)) ∧
    (∀ I : Type (u + 1),
      PreservesColimitsOfShape (Discrete I)
        ((localizingClosureProEtale Λ T).ι ⋙ moduleObjectDerivedPushforward Λ p)) ∧
    (∀ (H : (localizingClosureProEtale Λ S).FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      BrownRepresentableOnLocalizingClosure Λ S H) ∧
    D(openImmersionLowerShriek Λ j).IsTriangulated ∧
      (∀ K, constantModelBoundedConstructible Λ U K →
        constantModelBoundedConstructible Λ T
          (D(openImmersionLowerShriek Λ j).obj K)) ∧
      (∀ K, localizingClosureProEtale Λ U K →
        localizingClosureProEtale Λ T
          (D(openImmersionLowerShriek Λ j).obj K)) ∧
      (∀ K, constantModelBoundedConstructible Λ T K →
        constantModelBoundedConstructible Λ U
          (D(upperStar Λ j).obj K)) ∧
      (∀ K, localizingClosureProEtale Λ T K →
        localizingClosureProEtale Λ U (D(upperStar Λ j).obj K)) ∧
      ∃ (hshriek : ∀ K, localizingClosureProEtale Λ T
          (((localizingClosureProEtale Λ U).ι ⋙
            D(openImmersionLowerShriek Λ j)).obj K))
        (hstar : ∀ K, localizingClosureProEtale Λ U
          (((localizingClosureProEtale Λ T).ι ⋙ D(upperStar Λ j)).obj K)),
        Nonempty
          ((localizingClosureProEtale Λ T).lift
              ((localizingClosureProEtale Λ U).ι ⋙
                D(openImmersionLowerShriek Λ j)) hshriek ⊣
            (localizingClosureProEtale Λ U).lift
              ((localizingClosureProEtale Λ T).ι ⋙ D(upperStar Λ j)) hstar) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
