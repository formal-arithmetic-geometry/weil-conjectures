/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.IntegralOpenDirectImageCurrent
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations

/-!
# Integral finiteness for the open-complement term of localization

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/sk-thm-restriction/
`sk-thm-int-restriction-closed.proof.md` (det-thm-int-restriction-closed), line 5
“Let `j` be the open complement, quasi-compact since `X` is Noetherian” and lines 11–12
“Its third term lies in `Dbc(X, O_E)` by [det-thm-sf-pf-adic-open]”
(blueprint: lem-sfb-int-closed-complement-finiteness).

This module states only the third-term bounded-constructibility assertion. The
open complement is the canonical `i.left.openComplement.ι`; coefficients are the
current pulled-back condensed integral coefficient ring
`Profinite.padicIntegersRingObj ℓ E.val`, and the derived functors are the ordinary
module-object derived pullback and pushforward.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

/-- For a bounded constructible object, restriction to the open complement of a
closed immersion followed by derived direct image is bounded constructible.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/sk-thm-restriction/
`sk-thm-int-restriction-closed.proof.md`, lines 5 and 11–12, open-complement
third-term step (blueprint: lem-sfb-int-closed-complement-finiteness).
The coefficient is `Profinite.padicIntegersRingObj`, i.e. the pulled-back
condensed ring of integers of the finite coefficient extension. The open
complement is the canonical open immersion supplied by
`Scheme.Hom.openComplement`; `K` is an arbitrary object of the ambient ordinary
derived category satisfying the bounded finite-constant constructibility
predicate, and the conclusion applies the same predicate to
`Rj_* L j^* K`.

Proof (the node's steps):
1. The field `k` is Noetherian, so the finite-type `X` is Noetherian; every open
   subscheme of `X` is Noetherian, hence `U` is quasi-compact and `j` is quasi-compact.
   A quasi-compact open immersion is of finite type, so `U → Spec k` is separated of
   finite type and `j` satisfies the standing hypotheses of the integral open-image
   theorem (lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-noetherian-open-subscheme-noetherian,
   lem-weil-pbc-qc-open-immersion-finite-type, lem-weil-pbc-proper-fp-permanence).
2. Restrict a finite constructible stratification of each `H^q(K)` to `U`: the strata
   meet `U` in strata with the same finite constant local models
   `O_{E,V} ⊗_{O_E} P`. Cartesian coefficients make `j^*` exact, so
   `H^q(j^*K) = j^*H^q(K)` and the cohomological interval is unchanged; hence
   `j^*K ∈ Dbc(U, O_E)` (sk-def-sfb-constructible, sk-prop-sfb-cartesian-coefficients).
3. Apply det-thm-sf-pf-adic-open to the quasi-compact open immersion `j` and
   `j^*K ∈ Dbc(U, O_E)`. The standing hypothesis `hk : Finite k ∨ IsAlgClosed k`
   is part of the finite-or-algebraically-closed base-field convention; its final clause
   gives `Rj_*j^*K ∈ Dbc(X, O_E)`.
-/
theorem integralClosedComplementFiniteness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)]
    {Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X.left)))
    (hK : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val)
      X.left K) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X.left
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
        i.left.openComplement.ι).obj
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val)
          i.left.openComplement.ι).obj K)) := by
  -- Exact restriction along a coefficient isomorphism preserves the finite local models.
  have boundedCoefficientTransport
      {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
      [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
      (e : Λ ≅ Λ') [IsMonHom e.hom] (X : Scheme.{u})
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) :
      constantModelBoundedConstructible Λ' X
        ((Mod.comap (coefficientMap e.inv X)).mapDerivedCategory.obj K) ↔
        constantModelBoundedConstructible Λ X K := by
    let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
        Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) :=
      Mod.comap (coefficientMap e.inv X)
    constructor
    · intro h
      refine ⟨F.bounded_of_bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
      apply (constantModel_comap_iff e.inv X _).1
      exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm (h.2 n)
    · intro h
      refine ⟨F.bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
      exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
        ((constantModel_comap_iff e.inv X _).2 (h.2 n))
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  have : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  have : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  let U := i.left.openComplement.toScheme
  let j : U ⟶ X.left := i.left.openComplement.ι
  let : U.Over (Spec (.of k)) := ⟨j ≫ X.hom⟩
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (j ≫ X.hom)
    infer_instance
  have : QuasiCompact (U ↘ Spec (.of k)) := by
    change QuasiCompact (j ≫ X.hom)
    infer_instance
  have : IsSeparated (U ↘ Spec (.of k)) := by
    change IsSeparated (j ≫ X.hom)
    infer_instance
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : CompactSpace U :=
    QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : IsNoetherian U := ⟨⟩
  have hpull := (integralModelsOperations ℓ E).1 j K hK
  let J := (moduleObjectDerivedPullback Λ j).obj K
  have hJ : constantModelBoundedConstructible Λ U J := by
    have hclosed := (constantModelConstructibleFiniteTor_wellDefined Λ U).2.1
    let := hclosed
    exact (constantModelBoundedConstructible Λ U).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app K).symm hpull
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.val)).symm.finiteDimensional
  let eR := integerRingSheafIso.{u} ℓ ⟨E.val, E.property⟩
  let e : Λ ≅ DerivedNakayama.integerRing ℓ (ULift.{u} E.val) :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e.hom := by
    dsimp only [e]
    exact Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom e.inv := by dsimp only [e]; infer_instance
  let T : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U) ⥤
      Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (DerivedNakayama.integerRing ℓ (ULift.{u} E.val)) U) :=
    Mod.comap (coefficientMap e.inv U)
  have hinput := (boundedCoefficientTransport e U J).2 hJ
  have houtput := (integral_open_direct_image_current ℓ (ULift.{u} E.val)
    j k hk (Fact.out : ringChar k ≠ ℓ) (T.mapDerivedCategory.obj J) hinput).2.2.1
  have (W : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv W)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  let c := (derivedComapLowerStarIso e.inv j).app J
  exact (boundedCoefficientTransport e X.left _).1
    ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso c.symm houtput.1,
      fun n ↦ constructible_iso
        (Λ := DerivedNakayama.integerRing ℓ (ULift.{u} E.val))
        ((DerivedCategory.homologyFunctor _ n).mapIso c.symm) (houtput.2 n)⟩

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
