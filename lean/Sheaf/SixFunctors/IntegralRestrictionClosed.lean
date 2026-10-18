/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.SixFunctors.IntegralBrownAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.FormalClosedSupportDerived
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.FormalClosedSupportSheaves
import Sheaf.Paper.IntegralConstantModelHeart
import Sheaf.Paper.IntegralTensorPullback
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.SixFunctors.IntegralLocalizingCompactSupport
import Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage

/-!
# Integral exceptional inverse image along a closed immersion

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
`sk-thm-int-restriction-closed.md` (blueprint: det-thm-int-restriction-closed).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The inclusion of finite-constant bounded constructible complexes into the integral
localizing category.  This records the ambient category in which the Brown right adjoint
is compared with sections with support.
Source: blueprint `sk-def-localizing-closure` and `det-thm-int-restriction-closed`
(blueprint: det-thm-int-restriction-closed). -/
def generatorsToLocalizing {X : Scheme.{u}}
    (h : ∀ K, generators (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) X K) :
    (generators (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory :=
  (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).lift
    (generators (Profinite.padicIntegersRingObj ℓ E.val) X).ι
    (fun K ↦ h K.obj K.property)

/-- The assertion package for integral closed restriction.  The first clause is bounded
constructibility of derived sections with support.  The second clause says that, on the
bounded-constructible generators, this support functor is naturally isomorphic to every
right adjoint supplied by the integral Brown theorem, for every boundary compactification.
Source: blueprint `sk-thm-int-restriction-closed.md`, both displayed clauses
(blueprint: det-thm-int-restriction-closed). -/
def integralRestrictionClosedAssertions {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (.of k))]
    (hAdd : (closedModuleSectionsWithSupport
      (Profinite.padicIntegersRingObj ℓ E.val) i i.openComplement.ι).Additive) : Prop := by
  letI := hAdd
  exact ∃ hgen : ∀ K, generators (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) X K,
    (∀ K, generators (Profinite.padicIntegersRingObj ℓ E.val) X K →
      generators (Profinite.padicIntegersRingObj ℓ E.val) Z
        (((closedModuleSectionsWithSupport
          (Profinite.padicIntegersRingObj ℓ E.val) i i.openComplement.ι).rightDerivedFunctor).obj
          K)) ∧
    (∀ (c : Compactification.BoundaryCompactification i)
      (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) Z K →
        localizing (Profinite.padicIntegersRingObj ℓ E.val) X
          ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
      (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory ⥤
        (localizing (Profinite.padicIntegersRingObj ℓ E.val) Z).FullSubcategory)
      (_adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G),
      Nonempty
        (generatorsToLocalizing ℓ E hgen ⋙ G ⋙
            (localizing (Profinite.padicIntegersRingObj ℓ E.val) Z).ι ≅
          (generators (Profinite.padicIntegersRingObj ℓ E.val) X).ι ⋙
            (closedModuleSectionsWithSupport
              (Profinite.padicIntegersRingObj ℓ E.val) i i.openComplement.ι).rightDerivedFunctor))

/-- For a closed immersion over a finite-type separated scheme over a field, derived sections
with support along the canonical open complement preserve bounded constructibility and identify
naturally with the integral exceptional inverse image.  The latter is the right adjoint of the
integral Brown compact-support functor, independently of the chosen boundary compactification.
Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
`sk-thm-int-restriction-closed.md` (blueprint: det-thm-int-restriction-closed).

Proof plan (the node's steps):
1. Let `j : U ⟶ X` be the open complement `i.openComplement.ι`.  `k` is Noetherian, so `X` is
   Noetherian (lem-weil-pbc-finite-type-over-noetherian) and every open of `X` is
   quasi-compact (lem-weil-pbc-noetherian-open-subscheme-noetherian); hence `j` is
   quasi-compact, of finite type (lem-weil-pbc-qc-open-immersion-finite-type) and separated
   (lem-weil-pbc-separated-cancellation (a)).  `U` with `a_X ∘ j` is a standing scheme
   (lem-weil-pbc-proper-fp-permanence (e), def-weil-finite-type-morphism).  The pulled-back
   `O_E` is admissible in det-lem-formal-closed-support-sheaves; its (2) makes `i_*` exact.
2. `i` is proper (lem-weil-pbc-closed-immersion-proper (a)); use the compactification
   `(id_Z, i)`.  The formula and comparison of det-prop-int-brown-construction give
   `Ri_! ≅ Ri_* D((id_Z)_!) = Ri_*`, and exactness of `i_*` gives `Ri_* ≅ i_*`.
3. det-lem-formal-closed-support-derived (1),(3) with `Λ = O_E`: the natural triangle
   `F → K → Rj_* j^* K → F[1]` with `F = i_* RΓ_Z K`, the fibre formula
   `RΓ_Z K ≅ i^* F`, and the adjunction `Hom_X(i_* A, K) ≃ Hom_Z(A, RΓ_Z K)`.
4. det-lem-int-tensor-pullback (1) for `j`: `J = j^* K ∈ Dbc(U, O_E)`.
5. det-thm-sf-pf-adic-open for `J` and the quasi-compact open immersion `j`:
   `C = Rj_* J ∈ Dbc(X, O_E)`.
6. det-lem-int-integral-heart-triangulated (1): `Dbc(X, O_E)` is triangulated.  Rotating
   (TR2 of def-weil-triangulated-category) to `C[-1] → F → K → C`, the two-out-of-three
   condition of def-weil-triangulated-subcategory gives `F ∈ Dbc(X, O_E)`.
7. det-lem-int-tensor-pullback (1) for `i`: `i^* F ∈ Dbc(Z, O_E)`; by the fibre formula and
   isomorphism invariance (sk-def-sfb-constructible), `RΓ_Z K ∈ Dbc(Z, O_E)`.  This is the
   first clause.
8. Put `B = i^! K` (from `G`, the right adjoint of det-prop-int-brown-adjoint for `c`) and
   `H = RΓ_Z K`.  With det-def-localizing-closure-ctf-equals-bc (2), `K`, `H`, `B` lie in
   the localizing categories (sk-def-localizing-closure, full).  For `A` in `Loc(Dbc(Z))`,
   the Brown bijection, step 2 and step 3 give
   `Φ_A : Hom(A, B) ≃ Hom(i_* A, K) ≃ Hom(A, H)`, natural in `A` and `K`.
9. Yoneda: `α_K = Φ_B (𝟙 B)` and `β_K = Φ_H⁻¹ (𝟙 H)` are inverse, and naturality of `Φ` in
   `K` makes `α` natural; restricted to generators this is the second clause. -/
theorem integralRestrictionClosed (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (.of k))] :
    ∃ hAdd : (closedModuleSectionsWithSupport
      (Profinite.padicIntegersRingObj ℓ E.val) i i.openComplement.ι).Additive,
      integralRestrictionClosedAssertions (k := k) ℓ E i hAdd := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
