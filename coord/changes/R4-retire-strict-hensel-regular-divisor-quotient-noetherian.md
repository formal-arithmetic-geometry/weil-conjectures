# AlgebraicGeometry.Scheme.strictHenselizationRing_noetherian_of_regular

## Reason

Complete the zero-hole retirement explicitly listed in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian`.
Both the Sheaf theorem and its upstream owner are already proved, but they use the
small and full affine-neighbourhood colimits respectively. A bare import replacement
would give a ring map with the wrong codomain.

Withdraw the duplicate, preserve its mathematical DAG node and dependencies, and adapt
its sole direct consumer with the canonical colimit comparison. No adopted source file,
definition, target statement, or public consumer signature changes.

## Old

The duplicate small-colimit theorem has this exact signature:

```lean
theorem strictHenselizationRing_noetherian_of_regular
    (R : CommRingCat.{u}) [IsRegularRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    IsNoetherianRing (strictHenselizationRing barY)
```

Its sole direct consumer privately imports:

```lean
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian
```

and proves the Noetherianity conjunct by:

```lean
  have hN := strictHenselizationRing_noetherian_of_regular R barY b hb
```

## New

Withdraw the item through `deleted.txt`; the delivery tool supplies its empty module.
Reattach its mathematical node to the proved upstream owner, whose exact signature is:

```lean
theorem strictHenselizationRing_noetherian_of_regular
    (R : CommRingCat.{u}) [IsRegularRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    IsNoetherianRing (strictHenselization barY)
```

The direct consumer privately imports:

```lean
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian
```

It moves its existing canonical comparison and base-map identity to the start of the
proof, so both Noetherianity and quotient regularity/domain use the same comparison:

```lean
  let e : strictHenselizationRing barY ≅ strictHenselization barY :=
    smallStrictHenselizationColimitIso barY
  have hbe : Spec.map (b ≫ e.hom) = strictLocalizationToBase barY := by
    rw [Spec.map_comp, hb]
    exact comparison_base barY
  let : IsNoetherianRing (strictHenselization barY) :=
    strictHenselizationRing_noetherian_of_regular R barY (b ≫ e.hom) hbe
  have hN : IsNoetherianRing (strictHenselizationRing barY) :=
    isNoetherianRing_of_ringEquiv _ e.symm.commRingCatIsoToRingEquiv
```

The remaining quotient transport is unchanged. The final theorem and its docstring,
all public imports, visibility and universes are verbatim. The ring equivalence is
the canonical final-functor colimit comparison; no mathematical data is chosen from
an unproved existence statement. There are no new declarations or nodes.

This covers divisor zero, fields and all nonunit divisors in the original statement.
The zero base ring admits no displayed geometric point. No extra hypotheses are needed.
The unit route in `sk-prop-input-spreading` is unchanged: the mathematical Noetherianity
node remains a dependency of the same regular-divisor quotient node.

## Users

`tools/downstream.py` with `--uses strictHenselizationRing_noetherian_of_regular`
reports eight downstream modules. Exactly one imports/calls the retired item directly.
A parsed scan of all DAG statement/proof dependencies and proof-step uses finds only
the combined regular-divisor quotient node as a parent. No quarantined module mentions
the retired module or declaration. All eight modules were unclaimed when checked.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Transitive consumer; no source or signature change. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | Transitive consumer; no source or signature change. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | Sole direct caller; replace the private import and explicitly transport upstream Noetherianity. Signature and docstring unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Transitive consumer; no source or signature change. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Transitive consumer; no source or signature change. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Transitive consumer; no source or signature change. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Transitive consumer; no source or signature change. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | Transitive consumer; no source or signature change. |

Compiling the original direct consumer against the empty item fails at line 87 with
`Unknown identifier strictHenselizationRing_noetherian_of_regular`.
The adapted consumer compiles cleanly with the explicit ring transport. All eight
downstream modules compile individually in import order through `lcompile.py --all`
against the adapted consumer and the empty item. An unchanged verification copy of
`SmallStrictHenselizationIndEtale` supplies a missing published artifact; it and all
unchanged downstream verification copies are removed before delivery. The final
delivery preflight checks the final packet, including declaration axiom probes.

## Status

landed 20261021T120516-L-3904630 2026-10-21 (merge of deliver/R4/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian)
