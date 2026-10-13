# AlgebraicGeometry.Scheme.Modules.localized_middle_comparison_bijective

## Reason
Repair of reviewer X-a9a3d, head a9a3da850, E2 point 4. The former
intermediate theorem was false: c was arbitrary, and h_locUV's final predicate
was True. On Spec k for a nonzero field, with U = V = S = top, L = F = O
and s = 1, c W p = 0 satisfies the former premises but is not bijective in
degree zero. Add the canonical fraction formula hc and restore the same
formula for the intersection equivalence. Uniqueness on fractions then ties
c to the canonical diagram and to the three local equivalences. No definition
or target statement changes. The historical counterexample is preserved.

## Old
```lean
theorem localized_middle_comparison_bijective
    (X : Scheme.{u_1}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (c : ∀ (W : X.Opens) (p : ℕ), CohomologyFractionPresentation L F s p W →+
      (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F)
    (h_locU : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p U ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p U n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ S ≤ U))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p V ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p V).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p V n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : V ⊓ S ≤ V))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locUV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p (U ⊓ V) ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)), True) :
    ∀ p : ℕ, Function.Bijective (c (U ⊔ V) p)
```

## New
```lean
theorem localized_middle_comparison_bijective
    (X : Scheme.{u_1}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (c : ∀ (W : X.Opens) (p : ℕ), CohomologyFractionPresentation L F s p W →+
      (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F)
    (hc : ∀ (W : X.Opens) (p n : ℕ)
        (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p W).obj
          (F ⊗ L.tensorPow n : X.Modules)),
      (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
          (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
            F ⟶ (F ⊗ L.tensorPow n : X.Modules))
          (c W p (cohomologyFraction L F s p W n ξ)) =
        (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (inf_le_left : W ⊓ S ≤ W))).app
            (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locU : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p U ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p U n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ S ≤ U))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p V ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p V).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p V n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : V ⊓ S ≤ V))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locUV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p (U ⊓ V) ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p (U ⊓ V) n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ V ⊓ S ≤ U ⊓ V))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ) :
    ∀ p : ℕ, Function.Bijective (c (U ⊔ V) p)
```

## Users

`tools/downstream.py --uses localized_middle_comparison_bijective` finds only
the declaration's own module and the sole caller below. Transitive importers
use the caller's unchanged signature. The caller's signature and visibility
are preserved; only its proof's application of the auxiliary theorem changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluing | unclaimed | forced proof adaptation: pass hc and h_locUV without discarding their formulas |

Original caller lines 108–112 supplied h_locU where the corrected auxiliary
requires hc. Replace those five lines with an exact application passing
`c hc h_locU h_locV h_locUV`. The caller already obtains hc from the diagram
and has the full h_locUV premise, so its interface requires no alteration.

## Status
landed 20261013T024043-L-3337456 2026-10-13 (merge of deliver/P4/Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluingAux)
