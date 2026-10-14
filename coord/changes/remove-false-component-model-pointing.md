# AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_model_pointing

## Reason

Repair return X-cbd87 (head cbd87dec6), point E2 / review point 4. The assertion is
false: the two projections R × R → K agree after the diagonal R → R × R but
have different values on (1, 0). The retained proved private counterexample
establishes this under the original hypotheses. Leaving the false theorem with
`sorry`, even marked disputed, was rejected. Delete it and repair its sole caller.

## Old

```lean
theorem etaleResidueTriples_primeLocalization_component_extension_model_pointing
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
    (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B)
    (hiα : c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α) :
      i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ
```

The old declaration's proof was `by sorry`.

## New

Deleted; no replacement public theorem and no remaining hole. Its historical DAG
node has `lean: null`, records its retirement, and is no longer a proof dependency.
The module retains one proved private counterexample declaration. Repair X-039e3
removes the two duplicate private field-point helpers and uses Mathlib’s
`SpecToEquivOfField` equivalence directly in the counterexample proof. A local
`linter.privateModule` setting permits this intentionally private-only evidence module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel | unclaimed (local claims snapshot) | Replace the two proof-only imports AuxModelStructure and AuxModelPointing by UniqueAuxCompatible, and replace only the proof body with the existing compatible-model theorem. Signature, visibility, public imports and docstring remain byte-for-byte unchanged. |

`tools/downstream.py --uses` finds only this caller and the deleted declaration's own
module. All further downstream modules retain the same caller interface, so need
no adaptation. No target signature or definition changes.

The original caller uses the deleted name in its proof. The forced adaptation
changes original lines 5–6 and 36–42, introducing the single replacement import
and two-line `exact` application. Both compatibility equations are supplied
simultaneously by the existing proved theorem, using the identity R-triple.

The unchanged scratch baseline compiles when its three unchanged sources are
supplied. With only the pointing deletion, the original caller fails at line 40:
`error(lean.unknownIdentifier): Unknown identifier
etaleResidueTriples_primeLocalization_component_extension_model_pointing`.
The adapted caller and counterexample module compile together without warnings.
The previously missing shared AuxModelStructure.olean is now available; the
second reading repeated the delivery script's baseline and counterfactual checks
successfully (dry run OK).

## Status

landed 20261014T010851-L-3167153 2026-10-14 (merge of deliver/R2/Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModelPointing)
