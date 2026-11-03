/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralUnderived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetProperHeartBoundFiltration
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralUnderived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived

/-! # Reduction of proper heart bounds to integral lattices on strata

Source: blueprint latest, `part-six-operations/sec-six-functors-basics/`
`sec-brown-construction/sec-proper-direct-image-of-unbounded-complexes/`
`sk-lem-proper-heart-bound/sk-lem-proper-heart-bound-reduction.md` and its proof.
(blueprint: det-proper-heart-bound-reduction).

All coefficients are the pulled-back condensed rings; the algebraic-closure coefficient
has finite-subextension-valued sections. Constructibility uses finite constant scalar models.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Reduction of a proper direct-image bound to lisse integral lattices on strata.

Source: blueprint latest, `part-six-operations/sec-six-functors-basics/`
`sec-brown-construction/sec-proper-direct-image-of-unbounded-complexes/`
`sk-lem-proper-heart-bound/sk-lem-proper-heart-bound-reduction.md`, complete statement
(blueprint: det-proper-heart-bound-reduction).

The hypotheses quantify over every locally closed factorization `a = i ∘ u`, every finite
coefficient field `E'` containing the fixed field `E`, and every locally free integral module
`L₀` on the stratum.  The three vanishing hypotheses concern `a_! L₀`, its extension to
`E'`, and its extension to the algebraic closure.  The conclusion is the same higher-direct-
image vanishing for every constructible module over the chosen coefficient ring.  The proof
follows the blueprint's Extensions, Strata, and Lattices argument:

1. Finite-type schemes over a field and their locally closed strata are Noetherian,
   separated, and qcqs, so the finite stratification and lattice inputs apply.
2. The long exact sequence for higher direct images shows that the bound is stable
   under extensions. Negative degrees vanish for heart objects, so integer bounds are allowed.
3. Identify scalar extension from integers to a finite field with the filtered colimit
   inverting `l`. Exact filtered colimits make it exact. Finite-field extension and extension
   to the algebraic closure are exact by flatness.
4. Choose a finite lisse stratification of `M`. In the algebraic-closure case descend each
   lisse restriction to a finite coefficient field and enlarge it to contain the fixed `E`.
5. Apply stratified lattice existence and refine to strata with open initial unions.
   Restrict the lattices to the refined strata; pullback and scalar transitivity retain
   their lissity and localization identities.
6. Exact locally closed extension commutes with the two scalar extensions. Thus each
   stratum extension of the restriction of `M` is one of the two rational objects in
   the hypotheses, and satisfies the bound.
7. The open-closed filtration of `M` has these stratum extensions as subquotients.
   Induction using step 2 gives the stated vanishing.
(blueprint: det-proper-heart-bound-reduction). -/
theorem det_proper_heart_bound_reduction
    (l : ℕ) [Fact l.Prime] (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hpchar : 0 < pchar) (hpl : pchar ≠ l)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField l)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : Λ = Mon.mk (Profinite.continuousMapRingObj E.1) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (c : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))
    (hM : IsConstantModelConstructible Λ.X X M)
    (hvan₀ : ∀ (E' : PadicAlgCl.FiniteIntermediateField l), E ≤ E' →
      ∀ {S Sbar : Scheme.{u}} (a : S ⟶ X) (u : S ⟶ Sbar) (i : Sbar ⟶ X),
      a = u ≫ i → [IsOpenImmersion u] → [IsClosedImmersion i] →
      ∀ (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj l E'.1) S)),
      IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj l E'.1) S) L₀ →
      ∀ q : ℤ, c < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E'.1) p).obj
            ((DerivedCategory.singleFunctor _ 0).obj
            ((lowerStar (Profinite.padicIntegersRingObj l E'.1) i).obj
              ((openImmersionLowerShriek (Profinite.padicIntegersRingObj l E'.1) u).obj L₀))))))
    (hvanₑ : ∀ (E' : PadicAlgCl.FiniteIntermediateField l), E ≤ E' →
      ∀ {S Sbar : Scheme.{u}} (a : S ⟶ X) (u : S ⟶ Sbar) (i : Sbar ⟶ X),
      a = u ≫ i → [IsOpenImmersion u] → [IsClosedImmersion i] →
      ∀ (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj l E'.1) S)),
      IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj l E'.1) S) L₀ →
      ∀ q : ℤ, c < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E'.1) p).obj
            ((DerivedCategory.singleFunctor _ 0).obj
            ((Mod.extendScalars
              (coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E') X)).obj
              ((lowerStar (Profinite.padicIntegersRingObj l E'.1) i).obj
                ((openImmersionLowerShriek
                  (Profinite.padicIntegersRingObj l E'.1) u).obj L₀)))))))
    (hvanQ : ∀ (E' : PadicAlgCl.FiniteIntermediateField l), E ≤ E' →
      ∀ {S Sbar : Scheme.{u}} (a : S ⟶ X) (u : S ⟶ Sbar) (i : Sbar ⟶ X),
      a = u ≫ i → [IsOpenImmersion u] → [IsClosedImmersion i] →
      ∀ (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj l E'.1) S)),
      IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj l E'.1) S) L₀ →
      ∀ q : ℤ, c < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj l) p).obj
            ((DerivedCategory.singleFunctor _ 0).obj
            ((Mod.extendScalars (coefficientMap
              (Profinite.padicSubfieldRingObjToPadicAlgCl l E') X)).obj
              ((Mod.extendScalars
                (coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E') X)).obj
                ((lowerStar (Profinite.padicIntegersRingObj l E'.1) i).obj
                  ((openImmersionLowerShriek
                    (Profinite.padicIntegersRingObj l E'.1) u).obj L₀)))))))) :
    ∀ q : ℤ, c < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((moduleObjectDerivedPushforward Λ.X p).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  exact det_proper_heart_bound_filtration l pchar k hpchar hpl E Λ hΛ p c M hM
    (fun a _ N hN ↦ det_proper_heart_bound_stratum_step l pchar k hpchar hpl E Λ hΛ p c
      hvan₀ hvanₑ hvanQ a N hN)

end AlgebraicGeometry.ProEtale.CondensedRing
