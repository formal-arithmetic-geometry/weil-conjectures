# FiniteHypercoverDescentParts extraction

## Reason

The upstream sync quarantined the extracted helper module and two consumers.
Two trailing scoped option commands had lost the public theorem that followed
in the old source, so `end AlgebraicGeometry` instead encountered the anonymous
scope of `set_option ... in`. Remove the orphaned commands, preserving every
helper signature and mathematical argument. The extracted file intentionally contains private
helpers: use the existing private-module linter convention, and wrap the
sync-generated module comment to the project line limit.

The section-colimit consumer still attempted to import the private helper
`AlgebraicGeometry.truncated_terms_qcqs` from the upstream module. Its original
text, compiled against the repaired extraction, fails at line 32 with
`Unknown identifier truncated_terms_qcqs`. Import the private declarations from
the extracted module that actually owns them.

## Old

The extracted module ended with:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry
```

The section-colimit consumer contained:

```lean
import all WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts
import all WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts
```

## New

The extracted module ends with:

```lean
end AlgebraicGeometry
```

Its header documents its private-helper role and sets
`set_option linter.privateModule false`. No declaration signatures change.

The private proof `finite_components_lift` also replaces:

```lean
      change pullback.fst _ _ ≫ (ej f).left ≫ pullback.fst (W f).hom (D.map h) =
        (K.hom.app (V f)).left ≫ θ f
```

and the subsequent chained `congrArg`/`trans` term with direct rewrites
`rw [← hM, Category.assoc, hj]` followed by
`simp only [θ, Category.assoc]`. Profiling diagnostic prefixes located the
nested pullback definitional-equality bottleneck there after the first dry run
hit 60 seconds. This retains the same first-projection proof, without changing
any definition or splitting the delivered module.
The section-colimit consumer instead contains:

```lean
import all Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts
```

Its existing public import of the extracted module stays unchanged.

## Users

The source-only downstream tool with `--allow-missing --uses truncated_terms_qcqs`
reports no live importers because the entire three-module cluster is quarantined.
Reading coord/rework.tsv and the quarantined sources gives these consumers:

| module | group holding it | effect |
|---|---|---|
| Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts | F7 | Restore after repairing scoped commands; every declaration preserved. |
| Sheaf.AlgebraicGeometry.GrothendieckHypercoverSectionColimit | unclaimed in coord/claims | Restore with private helper import corrected; all signatures and proof bodies preserved. |
| Sheaf.AlgebraicGeometry.GrothendieckHypercoverLimitGeneration | unclaimed in coord/claims | Restore current quarantined source verbatim; compiles against the corrected consumer. |

All three compile without warnings through lcompile.py in import order
(30.5 s, 7.8 s, 5.9 s).
No target, definition, statement, DAG proof route, or upstream file changes.
The two consumer nodes remain attached to the same declarations:
lem-weil-pbc-grothendieck-hypercover-section-colimit and
lem-weil-pbc-grothendieck-hypercover-limit-generation.

Return repair (delivery head 070ca68e01, stale base e0d550965): read the current
rework rows, claim and return, then copied the current quarantined limit-generation
source back into the sandbox. Its live lean/ path is absent, and its quarantine
source is byte-for-byte identical to the retained proof (SHA-256
d32aedff61813594a0a5bbba8d6cc46debe865d993623428f29f2f6fdc7e1f9d).
The actual helper and consumer repairs above remain. The delivery is regenerated
against the tool's freshly fetched sheaf-dag base, preserving the current proof.
On this retry lcompile.py --all compiled the three modules without warnings,
exit code 0, in 12.6 s, 4.9 s and 3.7 s respectively.

## Status

landed 20261020T145509-L-2402616 2026-10-20 (merge of deliver/F7/Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts)
