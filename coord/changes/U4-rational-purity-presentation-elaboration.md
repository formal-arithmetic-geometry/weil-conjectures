# AlgebraicGeometry.Scheme.PbcPurityCoefficientConclusion

## Reason

Restore `Sheaf.Paper.RationalPurityPresentation` from the archive named in
`coord/rework.tsv`. Its assigned defect is a 60-second compile timeout. The archive
still disables transparency checking throughout the module, even though several
of its current dependencies protect expensive derived and scalar constructions.
Restore normal transparency checking for elaboration of these definitions and
locally protect scalar-Hom composition, scalar-Hom transport and the two stage
comparison isomorphisms. This is file-local and changes no exported reducibility or
mathematical data. The detailed profiler found repeated reductions of
ScalarLocalization.composition into chosen bilinear maps and tensor-product
quotients while comparing the coherence equations. It also found repeated failed
Module-instance searches through NormedSpace and LieAdmissibleAlgebra before the
canonical Algebra.toModule instance. Prefer that existing instance, and the
canonical scalar-localization category instance, locally in this file.

Also prove `pbcPurityGeometricBounds` using the existing finite-type Noetherian and
finite-dimension results and the prime-to-characteristic field unit mapped to each
stalk. No additional geometric hypothesis is needed, including for the empty scheme.

## Old

The rework source is `quarantine/Sheaf/Paper/RationalPurityPresentation.lean`.
Its 39 declaration signatures, public imports and definition bodies are preserved.
The relevant old file command is:

```lean
set_option backward.isDefEq.respectTransparency false
```

The old theorem, including its entire proof body, is:

```lean
theorem pbcPurityGeometricBounds (hl : l ≠ D.p) (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))] :
    IsNoetherian W ∧ (∃ n : ℕ, topologicalKrullDim W ≤ (n : WithBot ℕ∞)) ∧
      ∀ x : W, IsUnit (l : W.presheaf.stalk x) := by
  sorry
```

## New

The new file-local commands are:

```lean
set_option backward.isDefEq.respectTransparency true
attribute [local instance high] Algebra.toModule ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom
  AlgebraicGeometry.Scheme.pbcRationalScalarHom
attribute [local irreducible] pbcPurityStageA pbcPurityStageC
```

The theorem keeps exactly the signature above and has a complete proof. The new
private import `Mathlib.Algebra.CharP.CharAndCard` supplies
`charP_of_card_eq_prime_pow`. No public import, exported attribute, exported
instance priority, definition body, statement or visibility is changed. These irreducibility settings end at this module boundary;
consumers see precisely the original reducibility. The archived descent component formulas,
including both whiskerRight expressions, are preserved.

Validation: the final source compiled through `lcompile.py` in 37.3 seconds with
exit code 0 and no diagnostics, below the unchanged 60-second limit. The restored
archive initially compiled in 34.2 seconds; a transparency-only candidate compiled
in 33.5 seconds. Each run used a changing private dependency overlay, so these are
not controlled speedup measurements. The detailed trace exposed recursive
scalar-Hom reductions and unrelated instance-search branches; its large debug log
made that diagnostic run exceed the limit. All profiling/trace commands are removed
from the delivered source. No timeout limit is raised and no module is split.

## Users

`python3 tools/downstream.py Sheaf.Paper.RationalPurityPresentation --allow-missing`
reports zero live downstream modules. Without `--allow-missing`, the tool correctly
reports the item unknown because it is quarantined. A separate source search across
both `lean/` and `quarantine/` finds the archived direct importer below, and no other
external textual use of the item's declarations. No consumer is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | quarantined; not adapted | Existing interface and construction data identical; private import retained. |

The item's DAG attachment, dependencies, source hypotheses, unit route and target
meanings are preserved. There is no definition change requiring renewed statement
review. The archive is retained; the live item is restored, not withdrawn.

## Status

landed 20261026T002956-L-135695 2026-10-26 (merge of deliver/U4/Sheaf.Paper.RationalPurityPresentation)
