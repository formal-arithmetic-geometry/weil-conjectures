# CategoryTheory.brownHypotheses_arbitraryField_compactness_obligation

## Reason

Maintenance repair of six identical preflight refusals on 2026-10-27. The false
unrestricted objectwise compactness obligation was used to prove a witness, then
the original Brown theorem. Both auxiliary statements already said
STATEMENT-DISPUTED; neither the finite-field theorem nor the conditional integral
criterion supplies their missing hypotheses. The node's purported plan explicitly
says that the obligation is false. Repeatedly dispatching a proof of this split
cannot repair it.

The worker correctly removed the false splits and restored the original Brown
hole. The ordinary gate refuses this as replacing a proved declaration by sorry,
because it measures direct holes rather than the validity of their premises.
This is a maintainer-authorized rollback of that assembly, not permission for
workers to hollow proofs. No gate, landing tool, or launcher policy is changed.

The mathematical diagnosis and Lean changes are the retained K4 worker repair;
maintenance does not claim a new proof or a formal counterexample.

## Old

The removed signatures, verbatim:

```lean
theorem brownHypotheses_arbitraryField_compactness_obligation
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hSums : HasCoproducts.{u + 1}
      (localizingClosureProEtale Λ X).FullSubcategory)
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj) :
    @IsCompactObject _ _ _ hSums K

theorem brownHypotheses_arbitraryField_compactness_witness
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
      letI := hSums
      ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
        (constantModelBoundedConstructible Λ X K.obj ∧
          DerivedCategory.finiteTorAmplitude _ K.obj) → IsCompactObject K
```

They assume neither the finite-field datum nor the integral Ext bound. The old
Brown proof was:

```lean
  let _ := hp
  let _ := hpl
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  exact (brownHypothesesFor_iff_compact_of_noetherian ℓ X Λ hΛ).mpr
    (brownHypotheses_arbitraryField_compactness_witness X Λ)
```

## New

Remove the false obligation and witness with no replacement assertion. Retain
their DAG records as explicitly retired statements, with statement_change records
containing the old statements, old plans, provenance, and all affected citers.
Remove their live proof-dependency edges and Lean attachments.

Keep the exact statement of CategoryTheory.brownHypotheses and its existing
STATEMENT-DISPUTED diagnosis; its proof is again `by sorry`. The hole is tracked
by sk-lem-brown-hypotheses. The unit route and project targets are unchanged.

Retain both proved objectwise specializations in the item. Reuse them in the
parent's finite-field assembly and conditional integral criterion, preserving
all hypotheses. Their five node plans now match the retained repair. Keep its
local elaboration improvements so the parent stays within the 60-second limit.

Direct holes: item 1 -> 0, parent 0 -> 1; net proof progress zero. This removes
false premises and corrects their plan; it does not prove arbitrary-field Brown
compactness. Any correction to the original unit statement still requires the
human's decision. Do not recreate the retired splits or an unconditional Ext
bound to hide that dispute.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypothesesArbitraryFieldCompactness | K4 | Remove the false obligation; retain both proved specializations. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Remove the witness, restore the original hole, and reuse the supported specializations. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Direct importer; no signature or proof change required. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Direct importer; no signature or proof change required. |

The declaration-use search finds the removed names only in the first two
modules. No unchanged module needs either removed name. All other public
signatures, definitions, instances, and public imports are preserved, so
transitive consumers require no adaptation.

## Status

Maintenance rollback; the server transaction accepts this file only after the
two changed Lean modules and both unchanged direct importers pass sequential
tools/lean_file.sh checks (60-second acceptance, 300-second diagnostic run).
