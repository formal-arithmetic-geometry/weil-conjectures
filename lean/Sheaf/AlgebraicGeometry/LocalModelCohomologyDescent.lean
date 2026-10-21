/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.Paper.PullbackFiniteConstantLocalModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# Cohomology descent from finite scalar local models

Source: blueprint main-20261015, `det-prop-scalar-six-ctf.proof.md`, paragraph (2),
expanded by Stacks Project Tags 010N, 015F, 00VH, 00VM, 092A and 03DH
(blueprint: lem-sfb-local-model-cohomology-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Γ] [IsCommMonObj Γ]

-- Keep the original hypothesis and binder names even when this proof does not need them.
set_option linter.unusedVariables false in
/-- A finite cover by bounded scalar complexes gives the same global cohomology bounds,
and cohomology on each given covering member is extension of the given scalar cohomology.
Consequently every cohomology sheaf has a finite constant local model on the whole scheme,
is constructible, and the original object belongs to the bounded constructible category.
The three functor-class hypotheses together mean exactness of scalar extension.

Source: blueprint main-20261015, `det-prop-scalar-six-ctf.proof.md`, paragraph (2),
with the node's expanded proof from Stacks Tags 010N, 015F, 00VH, 00VM, 092A and 03DH
(blueprint: lem-sfb-local-model-cohomology-descent).

Proof plan:
1. For each covering member V, weakly etale composition and cancellation identify
S_proet/V with V_proet (sk-lem-pe-weakly-etale-stability, sk-def-pe-site).
Localized restriction is sectionwise (def-pur-localized-ringed-site).
The canonical coefficient comparison identifies the restricted coefficient ring with
Γ_V, compatibly with restriction and multiplication
(sk-def-sfb-coefficient-morphisms, lem-sfb-coefficient-sections-localization).
Renaming the module action along this isomorphism gives an equivalence of module categories.
Thus CondensedRing.upperStar on a covering member is exact localized restriction.
2. Restriction is exact by lem-pur-site-restriction-module-adjunction-exact, and the
coefficient equivalence preserves kernels and cokernels. Choose a representing complex
for Q (def-weil-abstract-derived-category). By
lem-weil-pbc-exact-functor-derived-factorization its termwise restriction represents
Q restricted to V; lem-weil-pbc-exact-functor-complex-cohomology identifies its cohomology
with restriction of H^q(Q). Derived cohomology factors complex cohomology.
3. Apply lem-weil-pbc-exact-functor-complex-cohomology to the assumed exact functor
finiteConstantScalarExtension Γ V and the given scalar complex. The assumed derived
isomorphism induces an isomorphism on cohomology. Compose with Step 2 to obtain exactly
H^q(Q)|_V ≅ Γ_V tensor H^q(K_i), with the original covering members and scalar complexes.
4. Outside [r,s] the middle scalar term is zero, hence its kernel/image cohomology is
zero. Exact additive scalar extension preserves zero objects, so all restrictions of
H^q(Q) to the covering members vanish (def-weil-abstract-derived-category).
5. For every test object W, base change gives a cover by W times_S V_i
(def-weil-pbc-sites-and-cohomology). All its section modules vanish by Step 4 and the
sectionwise description of def-pur-localized-ringed-site. Sheaf uniqueness makes any
section equal to zero. This proves global vanishing, including the empty-cover case.
6. The given finite presentations of the scalar cohomology and the isomorphisms of
Step 3 witness det-def-sfb-constructible-local-model. The identity stratum S is a finite
locally closed constructible stratification: S and the empty set are open retrocompact,
so S is constructible (def-constructible-stratification, def-weil-constructible-subset).
For the affine-local convention restrict the same scalar-matrix cokernel presentations
to each affine open; exact restriction preserves cokernels and finite sums, and the
coefficient comparison preserves their scalar entries. This proves constructibility
also without quasi-separatedness. Step 5 gives a finite interval of nonzero cohomology,
so det-def-sfb-constructible-tor-amplitude places Q in Dbc. -/
theorem localModel_cohomology_descent (S : Scheme.{u}) [CompactSpace S]
    (Q : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ S)))
    (𝒱 : Scheme.Cover.{u} Scheme.proetalePrecoverage S) [Finite 𝒱.I₀]
    (r s : ℤ) (hrs : r ≤ s)
    (K : ∀ i : 𝒱.I₀, CochainComplex (Mod Ab.{u + 1} (scalarRingObj Γ)) ℤ)
    [hadd : ∀ i : 𝒱.I₀, (finiteConstantScalarExtension Γ (𝒱.X i)).Additive]
    [hlim : ∀ i : 𝒱.I₀, PreservesFiniteLimits (finiteConstantScalarExtension Γ (𝒱.X i))]
    [hcolim : ∀ i : 𝒱.I₀, PreservesFiniteColimits (finiteConstantScalarExtension Γ (𝒱.X i))]
    (hterms : ∀ (i : 𝒱.I₀) (q : ℤ), q < r ∨ s < q → IsZero ((K i).X q))
    (hmodel : ∀ i : 𝒱.I₀,
      Nonempty (((CondensedRing.upperStar Γ (𝒱.f i)).mapDerivedCategory).obj Q ≅
        DerivedCategory.Q.obj
          (((finiteConstantScalarExtension Γ (𝒱.X i)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (K i))))
    (hfp : ∀ (i : 𝒱.I₀) (q : ℤ),
      Mod.IsFinitelyPresented (scalarRingObj Γ) ((K i).homology q)) :
    (∀ q : ℤ, q < r ∨ s < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj Q)) ∧
    (∀ (i : 𝒱.I₀) (q : ℤ),
      Nonempty ((CondensedRing.upperStar Γ (𝒱.f i)).obj
          ((DerivedCategory.homologyFunctor _ q).obj Q) ≅
        (finiteConstantScalarExtension Γ (𝒱.X i)).obj ((K i).homology q))) ∧
    (∀ q : ℤ,
      HasFiniteConstantLocalModel Γ S ((DerivedCategory.homologyFunctor _ q).obj Q) ∧
      IsConstantModelConstructible Γ S ((DerivedCategory.homologyFunctor _ q).obj Q)) ∧
    constantModelBoundedConstructible Γ S Q := by
  classical
  have hcoh (i : 𝒱.I₀) (q : ℤ) :
      Nonempty ((CondensedRing.upperStar Γ (𝒱.f i)).obj
          ((DerivedCategory.homologyFunctor _ q).obj Q) ≅
        (finiteConstantScalarExtension Γ (𝒱.X i)).obj ((K i).homology q)) := by
    obtain ⟨e⟩ := hmodel i
    exact ⟨((CondensedRing.upperStar Γ (𝒱.f i)).mapDerivedCategoryHomologyFunctorIso q).app Q
      ≪≫ (DerivedCategory.homologyFunctor _ q).mapIso e
      ≪≫ (DerivedCategory.homologyFunctorFactors _ q).app _
      ≪≫ ((finiteConstantScalarExtension Γ (𝒱.X i)).mapHomologicalComplexHomologyIso
        (.up ℤ) q).app (K i)⟩
  have hzero (q : ℤ) (hq : q < r ∨ s < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj Q) := by
    let H := (DerivedCategory.homologyFunctor _ q).obj Q
    have hz (i : 𝒱.I₀) : IsZero ((CondensedRing.upperStar Γ (𝒱.f i)).obj H) := by
      obtain ⟨e⟩ := hcoh i q
      exact ((finiteConstantScalarExtension Γ (𝒱.X i)).map_isZero
        (((K i).sc q).isZero_homology_of_isZero_X₂ (hterms i q hq))).of_iso e
    have : ∀ i, WeaklyEtale (𝒱.f i) :=
      (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mp 𝒱.mem₀.2 |>.2
    have hz' (i : 𝒱.I₀) : IsZero ((upperStar Ab.{u + 1} (𝒱.f i)).obj H.X) := by
      let e : CondensedRing.upperStar Γ (𝒱.f i) ⋙ Mod.forget _ ≅
          Mod.forget _ ⋙ upperStar Ab.{u + 1} (𝒱.f i) :=
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} (𝒱.f i)).mapMod _)
            (Mod.extendScalarsIsoComapInv (condensedPullbackHom Γ (𝒱.f i))))
          (Mod.forget _)
      exact ((Mod.forget _).map_isZero (hz i)).of_iso (e.app H).symm
    have : IsIso (0 : H.X ⟶ H.X) := by
      apply isIso_of_isIso_localizationRestriction Ab.{u + 1} (0 : H.X ⟶ H.X)
        𝒱.f 𝒱.mem₀
      intro i
      let e := upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒱.f i) inferInstance
      have hi := (hz' i).of_iso (e.app H.X).symm
      exact hi.isIso hi _
    have hX : IsZero H.X :=
      (IsZero.iff_id_eq_zero H.X).2 (isIsoZeroSelfEquiv H.X inferInstance)
    apply (IsZero.iff_id_eq_zero H).2
    apply (Mod.forget _).map_injective
    simpa using hX.eq_of_src ((Mod.forget _).map (𝟙 H)) ((Mod.forget _).map (0 : H ⟶ H))
  have hlocal (q : ℤ) :
      HasFiniteConstantLocalModel Γ S ((DerivedCategory.homologyFunctor _ q).obj Q) := by
    apply (finiteConstantLocalModel_iff_exists_cover Γ _).2
    exact ⟨𝒱, fun i ↦ ⟨(K i).homology q, hfp i q, hcoh i q⟩⟩
  have hstrat (T : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Γ T))
      (hM : HasFiniteConstantLocalModel Γ T M) : IsFiniteConstantStratified Γ T M := by
    exact ⟨Scheme.Stratification.trivial T,
      fun _ ↦ pullback_finiteConstantLocalModel Γ (𝟙 T) M hM⟩
  have hcons (q : ℤ) :
      IsConstantModelConstructible Γ S ((DerivedCategory.homologyFunctor _ q).obj Q) := by
    unfold IsConstantModelConstructible
    split
    · exact hstrat _ _ (hlocal q)
    · intro U _
      exact hstrat _ _ (pullback_finiteConstantLocalModel Γ U.ι _ (hlocal q))
  refine ⟨hzero, hcoh, fun q ↦ ⟨hlocal q, hcons q⟩, ?_⟩
  have : Q.IsGE r := (DerivedCategory.isGE_iff Q r).2 fun q hq ↦ hzero q (Or.inl hq)
  have : Q.IsLE s := (DerivedCategory.isLE_iff Q s).2 fun q hq ↦ hzero q (Or.inr hq)
  exact ⟨⟨⟨r, inferInstance⟩, ⟨s, inferInstance⟩⟩, hcons⟩

end AlgebraicGeometry.ProEtale
