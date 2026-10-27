## Worker report

Q51, stage 2, 2026-10-22. Repair of independent return L on immutable head
351d0daa934c, H4/H12. The required initial dry run of the saved packet passed
at eb9ba259f98. That mechanical pass did not resolve the review's duplicate:
this packet now removes it and reuses the landed construction.

The item is `WeilConjectures.zlWeilShriek_coefficient_long_exact` in
`lean/Sheaf/Paper/ZlWeilShriekCoefficientLongExact.lean`. Its higher-image functor
is now exactly the Weil-heart inclusion, followed by `zlComplexShriek`, followed
by `sfWeilCohomology D l hl Ω Y₀ r` from `Sheaf.Paper.WeilMixedUpperBounds`.
The duplicate `def-zl-normalized-weil-cohomology` node and its module
`ZlNormalizedWeilCohomology.lean` have been removed from the sandbox packet.
The item's statement dependency on that duplicate has been replaced by the
landed owning node `sk-d-dl-general-weights`, as explicitly required by the return.
There are no new nodes or dependency modules in this repair.

Hypothesis and clause correspondence:

- `D : FiniteFieldDatum.{u}` specifies the finite field, algebraic closure and
  geometric Frobenius. `l`, `[Fact l.Prime]` and `hl : l ≠ D.p` specify the prime
  different from the characteristic. `Ω : Type v`, `[Field Ω]`,
  `[Algebra (Padic l) Ω]` and `[IsAlgClosure (Padic l) Ω]` specify the algebraically
  closed coefficient field. The scheme and coefficient universes remain independent.
- `X₀ Y₀ : Over (Spec (.of D.k₀))` specify the base-field schemes. Their structure
  morphisms have `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` instances,
  exactly separated finite type. Their geometric fibres are `D.geometricFiber`.
- `f₀ : X₀ ⟶ Y₀` is over the base field, and `IsSeparated f₀.left`,
  `LocallyOfFiniteType f₀.left`, `QuasiCompact f₀.left` specify the morphism's
  hypotheses. The explicit `include hXsep hYsep hfsep hfft hfqc in` retains each
  of these section assumptions in the theorem even when elaboration does not need it.
- `c : Compactification f₀.left` is any compactification. The already-recorded
  `zlCommonStageShriek_recorded` identifies the actual compact-support functor
  with the normalized recorded coefficient action; no special choice is required.
- `sfCommonStageWeilSheaf` is the full subcategory of geometric-Frobenius fixed
  pairs with carrier in the constructible heart. `S : ShortComplex (...)` and
  `hS : S.ShortExact` give the short exact Weil sequence, including the
  intertwining condition on its arrows.
- `zlCoefficientHigherShriek ... r` is precisely H^r(Rf_!(F[0])). Its first factor
  is the full-subcategory inclusion `ι`; its second is the actual Weil complex
  compact-support functor `zlComplexShriek`; its last is the landed
  `sfWeilCohomology`. The latter's carrier is `constructibleTruncationCohomology`
  and its Frobenius comparison uses the normalized shift and truncation comparisons.
- The existential family `δ` ranges over every short exact S and every integer r.
  Its type is an arrow in the Weil heart, asserting Frobenius compatibility as a
  conclusion, rather than assuming an arbitrary compatible boundary as input.
- The three `ShortComplex.Exact` clauses assert exactness respectively at
  R^r f_! F, R^r f_! F'', and R^(r+1) f_! F'. Their existential witnesses `h`
  assert that consecutive composites vanish. For all r these cover the entire
  long exact sequence, including the explicitly required same-degree piece.
- `zlCoefficientBoundaryFormula` specifies the underlying boundary and its sign.
  The arrow `t` completes the actual underlying heart sequence to a distinguished
  triangle. Its compact-support image is `zlCommonStageShriek.map t` followed by
  the prescribed `commShiftIso 1`. `constructibleTruncationCohomology ... r` is
  applied to this arrow. The comparisons `a` and `b` are fixed by commuting with
  the LE counit and GE unit respectively. Their shifted composite, followed by
  the inverse of `shiftFunctorAdd'`, identifies H^r(A[1]) with H^(r+1)(A).
  Equality to `δ.hom.hom.f` therefore specifies the canonical underlying boundary.
- For every morphism `φ : S ⟶ T` of short exact sequences, the last equation is
  R^r f_!(φ.τ₃) ≫ δ_T = δ_S ≫ R^(r+1) f_!(φ.τ₁). The same-degree squares follow
  from functoriality. The sequence morphism need not be invertible.

Dependency declarations used, with signatures and docstrings inspected:

- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilFrobeniusPullback`,
  `sfCommonStageWeilComplex`, `sfCommonStageWeilForget`, `sfCommonStageWeilSheaf`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`,
  `sfCommonStageStandardTStructure`, `sfCommonStageHeart_properties`.
- `Sheaf.Paper.ConstructibleTruncations`: `constructibleTruncationCohomology`.
- `Sheaf.Paper.CommonStageWeilShriek`: `zlCommonStageShriek`, `zlComplexShriek`,
  `zlCommonStageShriek_recorded` and the prescribed proper/open Frobenius exchange.
- `Sheaf.Paper.FieldWeilShriekShiftData`: `fieldCommonWeilFrobeniusShift`,
  `fieldZlShriekShift`. Their previously added owning statement dependencies remain.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`.
- `Sheaf.Paper.WeilMixedUpperBounds`, owned by `sk-d-dl-general-weights`:
  `sfWeilCohomologyUnderlying`, `sfWeilFrobeniusTruncLE_existsUnique`,
  `sfWeilFrobeniusTruncLE`, `sfWeilFrobeniusTruncGE_existsUnique`,
  `sfWeilFrobeniusTruncGE`, `sfWeilCohomologyFrobenius`,
  `sfWeilCohomology_mem`, `sfWeilCohomology`.

The original proof-plan imports and seven-step theorem docstring remain. The
boundary-comparison node is a proof dependency; it is not an input assumption
of either definition. Both definitions have actual data. The item's single
postponed theorem has proof `sorry`, matching the DAG statement and proof plan.
No target or natural-language node statement is corrected or disputed.

Edge cases checked: empty schemes, zero sequence, identity f, split short exact
sequences, all negative degrees, transitions -1/0 and 0/1, and noninvertible
morphisms of sequences. The nonsplit Frobenius Jordan-block extension at a point
is still covered without asserting a triangulation on fixed pairs. The A¹
example with nonzero H^0_c(i_*Λ) → H^1_c(j_!Λ) retains its canonical boundary sign.
The landed Frobenius comparison uses `fieldCommonWeilFrobeniusShift`, so the
previous free-shift sign ambiguity does not return. Its truncation comparisons
are uniquely fixed by counit/unit equations.

Searches retained from the saved packet (`searches.jsonl`): LeanFinder on a
natural Frobenius-equivariant compact-support higher-image long exact sequence;
Loogle on `homologySequenceδ` and on `WeilSheaf, higherLowerShriek`; Mathlib grep
on `homologySequenceδ|shortExact_iff_exists_distTriang` and the higher-shriek
exactness names; LeanSearch on natural long exact cohomology of short exact
sequences. These found generic homological-functor and heart-triangle inputs,
but no exact match for the item in its common-stage fixed-pair categories.
Project searches inspected `WeilSheaf.exact_map_higherLowerShriek` and native
Weil cohomology; their derived-of-Weil model differs from this node's pairs.

For this repair, `rg -n 'sfWeilCohomology|sfWeilCohomologyFrobenius'
lean/Sheaf/Paper/WeilMixedUpperBounds.lean` found the landed construction at
lines 53, 134, 167 and 189. I opened its full signatures and docstrings and its
LE/GE comparison definitions, then read the owning node's `lean.declarations`.
This is the exact needed notion, so the duplicate was removed. A read-only DAG
traversal found no dependency path from `sk-d-dl-general-weights` back to this
item. Source Part 3 was reopened in the current main-20261015 blueprint.

## Return repairs

L, H4/H12 on 351d0daa934c: removed both the duplicate node and module; imported
`Sheaf.Paper.WeilMixedUpperBounds`; changed the final factor of
`zlCoefficientHigherShriek` to `sfWeilCohomology D l hl Ω Y₀ r`; replaced the
duplicate statement dependency by landed `sk-d-dl-general-weights`; regenerated
`lean.statement` from the file and updated `lean.note` and this report.
The record's theorem signature remains verbatim, with the same hypotheses,
all three exactness positions, naturality and boundary formula.

## Second reading by Q51

The dispatcher prohibits other agents, so this is a separate in-thread rereading;
the maintainer supplies the independent review. I reopened the item statement,
the repaired module and the landed cohomology construction. The only two Lean
text replacements are the import and the final cohomology functor. The latter
has precisely the required Weil-complex domain and Weil-heart codomain, with
arbitrary integer degree and independent universes u and v. Unfolding its carrier
gives GE^r LE^r shifted by r, the cohomology functor used by the unchanged boundary
formula. `IsoAlgebra.mapOfNatIso` gives the same induced Weil structure, now reused
from its actual owner, and the full-subcategory lift uses its already-proved
heart-membership theorem.

I reread each clause against the correspondence above: every geometric and
coefficient premise is present, δ is a Weil morphism, all three types of terms
are exact, and every short-exact-sequence morphism satisfies the boundary square.
The canonical triangle, LE counit, GE unit and shift-addition equations in the
boundary formula are unchanged. No new assumption, restricted degree or sign
choice has entered. Comparison to the current read clone finds changes only
in `lean` and the authorized added `stmt_deps`; no stale base-field changes.

## Validation

The initial saved-packet dry run printed `OK (dry run)` at eb9ba259f98.
The repaired module compiled with scompile.py, exit 0: sandbox 18.7 s and
library 13.6 s, with no errors or warnings. The repaired dry run printed
`OK (dry run): commit b54ad249f46 passes the preflight and compiles; nothing pushed`,
exit 0. It staged only this report, the item node and the item module. The shared
clone gained a routine lean_audit field during refresh; the wrapper correctly
excluded that stale metadata difference, and the sandbox node has now been
rebased to retain the current metadata. The ordinary delivery repeats all gates
before pushing.
