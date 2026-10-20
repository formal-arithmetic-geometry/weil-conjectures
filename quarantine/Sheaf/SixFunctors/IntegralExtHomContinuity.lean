/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ConstructibleHomContinuityDevissage
import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
import Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
import Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.FormalClosedSupportDerived
import Sheaf.Paper.IntegralStratumHomFormula
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FreeSheafFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.Paper.IntegralHeartDualizable

/-!
# Continuity of Ext out of integral constructible complexes

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-ext/
sk-lem-int-ext-continuity.md,
node det-lem-int-ext-continuity (blueprint: det-lem-int-ext-continuity).

The constructible category is `Dbc(X, 𝒪_E)` of sk-def-sfb-constructible (finite constant
scalar models), and the comparison is the canonical map `homContinuityComparison` of
det-lem-constructible-ext-continuity-devissage, built from the termwise colimit cocone.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {ℓ : ℕ} {k : Type u} {E : Type} [Field k] [Field E]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [Fact ℓ.Prime] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- Ext out of an integral constructible complex commutes with a bounded-below filtered
termwise colimit: for `C ∈ Dbc(X, 𝒪_E)` and every `q`, the canonical map
`colim_i Hom(C, K_i[q]) ⟶ Hom(C, K[q])` induced by the colimit cocone is an isomorphism of
abelian groups.
Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext/
sk-lem-int-ext-continuity (blueprint: det-lem-int-ext-continuity).

Proof:
1. By det-lem-constructible-ext-continuity-devissage the objects `D` for which the comparison
is bijective in every degree are closed under shifts, isomorphisms and distinguished
extensions. Clause (1) of det-lem-int-ext-formula writes `C` as a finite extension of shifts
of `a_!L`, `a = i ∘ u : S ⟶ Z ⟶ X` with `i` closed, `u` open and `L` locally the completion of
a finitely generated module. The schemes `S, Z, X, V = X \ Z` are Noetherian
(lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian),
hence qcqs (lem-weil-pbc-locally-noetherian-quasi-separated), and `j : V ⟶ X` is qcqs
(lem-weil-pbc-qcqs-morphism-permanence).
2. Put `P = L^∨`; it has Tor amplitude `[0,1]` by det-lem-int-integral-heart-dualizable.
Clause (2) of det-lem-int-ext-formula, the tensor-internal Hom adjunction
(sk-def-sfb-derived-tensor-hom) and the K-injective computation of derived sections
(def-pur-ringed-site-zeroth-hypercohomology, lem-weil-pbc-kinjective-hom-derived) give,
naturally in `K`, `Hom(a_!L, K[q]) ≅ H^q(S, P ⊗^L u^* RΓ_Z K)`.
3. Take a two-term flat model `F` of `P` (lem-sc-source-tor-amplitude-flat-model, with flat
resolutions from lem-weil-pbc-free-sheaf-flat and lem-sfb-modobj-flat-resolutions). The
functor `T(B) = Tot(F ⊗ u^* i^* B)` commutes with filtered colimits and preserves the termwise
lower bound and quasi-isomorphisms; det-pe-bounded-continuity-sections on the qcqs `S` gives
`colim_i H^q(S, Φ K_i) ≅ H^q(S, Φ K)` for `Φ B = P ⊗^L u^* i^* B`.
4. With functorial K-injective resolutions (lem-weil-pbc-kinjective-functorial-existence,
lem-weil-pbc-right-adjoint-preserves-kinjective), `j_* I(j^* K_i)` represents `Rj_* j^* K_i`;
it has no cohomology below `b` (thm-sp-truncation-e2), so its quotient by the truncation
`τ_{≤ b-1}` (def-sbc-standard-tstructure-derived-category) is a termwise bounded model.
det-lem-bounded-continuity-direct-image makes the colimit of these models quasi-isomorphic to
the model for `K`, and Step 3 gives `colim_i H^q(S, Φ Rj_* j^* K_i) ≅ H^q(S, Φ Rj_* j^* K)`.
5. Clause (3) of det-lem-formal-closed-support-derived gives `RΓ_Z B ≃ i^* fib(B ⟶ Rj_* j^* B)`;
the exact and K-flat functors are triangulated (lem-sf-exact-functor-derived-triangulated,
lem-sc-source-kflat-tensor-left-triangulated, lem-pc-right-derived-functor-triangulated), so
there is a natural triangle and a long exact sequence (lem-sf-derived-homology-long-exact).
Filtered colimits are exact (lem-weil-pbc-filtered-colimit-abelian-groups-exact); Steps 3 and 4
and the five lemma (lem-weil-pbc-five-lemma) give
`colim_i H^q(S, P ⊗^L u^* RΓ_Z K_i) ≅ H^q(S, P ⊗^L u^* RΓ_Z K)`.
6. By Step 2 this is the comparison for `a_!L`, so every piece lies in the comparison class;
the closure of Step 1 along the finite filtration of clause (1) gives the assertion for `C`
in every degree `q`. -/
theorem integralExtHomContinuous
    {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (C : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)))
    (hC : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)) ℤ)
    [HasColimit K]
    (b : ℤ) (hK : ∀ i : I, ∀ r : ℤ, r < b → IsZero ((K.obj i).X r)) (q : ℤ) :
    IsIso (homContinuityComparison (K ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.mapCocone (colimit.cocone K)) C q) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
