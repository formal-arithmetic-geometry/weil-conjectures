# IsLocalRing.complete_local_domain_finite_over_regular_residue

## Reason

Repair reviewer X-babb1, head babb1a450, E2 (review point 4). The retained split theorem is
false: take R = ℂ and R₀ its real subfield. Both are complete regular local fields and
ℂ is finite over ℝ, but the compatible residue map ℝ → ℂ is not surjective. The prior
sandbox counterexample proves this in Lean. Retire the invalid theorem rather than
retain a false sorry or add hypotheses the parent cannot supply.

## Old

```lean
theorem complete_local_domain_finite_over_regular_residue
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (R₀ : Subring R) (hreg : IsRegularLocalRing R₀)
    [hlocal : IsLocalRing R₀] (hfinite : Module.Finite R₀ R)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀) :
    IsLocalRing.maximalIdeal R₀ =
        Ideal.comap R₀.subtype (IsLocalRing.maximalIdeal R) ∧
      ∃ e : (R₀ ⧸ IsLocalRing.maximalIdeal R₀) ≃+*
          (R ⧸ IsLocalRing.maximalIdeal R),
        (∀ x : R₀,
          e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R₀) x) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (R₀.subtype x)) ∧
      ((∃ (k : Type u), ∃ h : Field k, ∃ d : ℕ,
          let _ := h
          Nonempty (R₀ ≃+* MvPowerSeries (Fin d) k)) ∨
      (∃ (Λ : Type u), ∃ h : CommRing Λ, ∃ d : ℕ,
          let _ := h
          ∃ p : ℕ, IsCohenRing p Λ ∧
          Nonempty (R₀ ≃+* MvPowerSeries (Fin d) Λ)))
```

## New

The entire declaration is deleted. The module header remains; its four unused public imports
are removed because the retired module has no remaining statements or definitions.
Its node has no Lean realization and no proposed proof. The parent
`IsLocalRing.complete_local_domain_finite_over_regular` retains its exact signature,
visibility and existing eight-step source proof docstring. Its proof is restored to
`:= by sorry`, and its two private proof imports of the core and residue splits are removed.
The parent DAG again records the eight-step construction from that docstring, without
core/residue dependencies. No target statement or definition changes.

## Users

`tools/downstream.py Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegularResidue
--uses IsLocalRing.complete_local_domain_finite_over_regular_residue`
finds only the declaring module and the parent as textual declaration users. The parent
is the sole direct importer; none of the other transitive importers mention the removed
name. Their interfaces are preserved through the unchanged parent signature.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegularResidue | X3 | Delete the false theorem. |
| Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular | unclaimed | Forced adaptation: remove the two split imports and replace the composition proof with sorry. Signature, visibility and docstring preserved. |

The original parent fails against the retired module at line 166:8 with
`error(lean.unknownIdentifier): Unknown identifier
complete_local_domain_finite_over_regular_residue`, and at line 165:13 with
`Tactic rcases failed: x✝ : ?m.125 is not an inductive datatype`. The original parent compiles
against the baseline; the adapted parent compiles against the delivered set. Only these
forced Lean lines changed in the parent; the DAG restoration is expressly requested by the reviewer.

## Status

landed 20261012T160145-L-2567466 2026-10-12 (merge of deliver/X3/Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegularResidue)
