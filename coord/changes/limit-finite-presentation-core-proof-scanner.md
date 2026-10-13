# Algebra.exists_limit_finite_presentation_core

## Reason

The preflight reports a change in “commands such as variable, open, notation or attribute”.
This is a scanner false positive: `tools/leanindex.py` treats the existing column-zero
`:= by` line as an `other` command rather than the continuation of the theorem declaration.
Its `#commands` comparison therefore includes the entire proof. The old signature, visibility,
public imports, namespace, universe, and public section are identical. The only new top-level
commands are three non-public proof imports. No declaration, instance, or attribute was added.
The scanner was not modified or bypassed; this record documents its flag for CODEX review.

## Old

```lean
theorem exists_limit_finite_presentation_core
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.FinitePresentation φ) :
    ∃ (Λ : Type u) (_hpo : Preorder Λ) (_hne : Nonempty Λ)
      (_hdir : IsDirected Λ (fun a b => a ≤ b))
      (Rfun : Λ ⥤ CommRingCat) (Sfun : Λ ⥤ CommRingCat)
      (η : Rfun ⟶ Sfun) (cR : Cocone Rfun) (cS : Cocone Sfun),
      cR.pt = CommRingCat.of R ∧ cS.pt = CommRingCat.of S ∧
      (∀ l (hR : cR.pt = CommRingCat.of R) (hS : cS.pt = CommRingCat.of S),
        η.app l ≫ cS.ι.app l = cR.ι.app l ≫
          (eqToHom hR ≫ CommRingCat.ofHom φ ≫ eqToHom hS.symm)) ∧
      (∀ l, RingHom.FiniteType (η.app l).hom) ∧
      (∀ l, RingHom.FiniteType (algebraMap ℤ (Rfun.obj l))) ∧
      (∀ l m (h : l ≤ m),
        Nonempty (CategoryTheory.IsPushout (η.app l) (Rfun.map (homOfLE h))
          (Sfun.map (homOfLE h)) (η.app m))) ∧
      (∀ l (hR : cR.pt = CommRingCat.of R) (hS : cS.pt = CommRingCat.of S),
        Nonempty (CategoryTheory.IsPushout (η.app l) (cR.ι.app l) (cS.ι.app l)
          (eqToHom hR ≫ CommRingCat.ofHom φ ≫ eqToHom hS.symm))) ∧
      Nonempty (IsColimit cR)
:= by
  sorry
```

## New

```lean
theorem exists_limit_finite_presentation_core
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.FinitePresentation φ) :
    ∃ (Λ : Type u) (_hpo : Preorder Λ) (_hne : Nonempty Λ)
      (_hdir : IsDirected Λ (fun a b => a ≤ b))
      (Rfun : Λ ⥤ CommRingCat) (Sfun : Λ ⥤ CommRingCat)
      (η : Rfun ⟶ Sfun) (cR : Cocone Rfun) (cS : Cocone Sfun),
      cR.pt = CommRingCat.of R ∧ cS.pt = CommRingCat.of S ∧
      (∀ l (hR : cR.pt = CommRingCat.of R) (hS : cS.pt = CommRingCat.of S),
        η.app l ≫ cS.ι.app l = cR.ι.app l ≫
          (eqToHom hR ≫ CommRingCat.ofHom φ ≫ eqToHom hS.symm)) ∧
      (∀ l, RingHom.FiniteType (η.app l).hom) ∧
      (∀ l, RingHom.FiniteType (algebraMap ℤ (Rfun.obj l))) ∧
      (∀ l m (h : l ≤ m),
        Nonempty (CategoryTheory.IsPushout (η.app l) (Rfun.map (homOfLE h))
          (Sfun.map (homOfLE h)) (η.app m))) ∧
      (∀ l (hR : cR.pt = CommRingCat.of R) (hS : cS.pt = CommRingCat.of S),
        Nonempty (CategoryTheory.IsPushout (η.app l) (cR.ι.app l) (cS.ι.app l)
          (eqToHom hR ≫ CommRingCat.ofHom φ ≫ eqToHom hS.symm))) ∧
      Nonempty (IsColimit cR)
```

The complete pushout-system proof follows this signature in the item module. Its body obtains a proved finite-stage descent witness, constructs the
restricted index and diagram, and proves every assertion. No public definition is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.LimitFinitePresentation | unclaimed | Same theorem type and visibility; no adaptation. |

The module above is the direct importer and direct user of this theorem. All transitive
users receive the same statement and public imports. No dependent module is edited.

## Status

landed 20261013T082413-L-1648049 2026-10-13 (merge of deliver/S4/Sheaf.Algebra.LimitFinitePresentation.Core)
