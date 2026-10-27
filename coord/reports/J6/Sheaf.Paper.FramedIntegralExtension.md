## What changed

Proved `WeilConjectures.PurityFiniteSetting.divisorRelativeExtension_existsUnique`
in `Sheaf.Paper.FramedIntegralExtension`. Added the private proof import
`Sheaf.AlgebraicGeometry.OpenClosedIntegralSections`. Applied its normalized
integral open-closed presentation to the existing relative torsor-extension
uniqueness theorem. Naturality identifies its objectwise constant one with the
terminal supported section used in the original predicate. All signatures,
definitions, public imports and docstrings are unchanged.

Updated `def-pur-framed-integral-extension` with the actual proof and dependencies.
The node is not a realized statement or step of its unit, and the unit route is
unchanged. The argument applies to empty support and empty complementary open.

## Proved and sorry left

Closed one hole: `WeilConjectures.PurityFiniteSetting.divisorRelativeExtension_existsUnique`
(node `def-pur-framed-integral-extension`). One of one original holes proved;
zero holes added, zero split off, and zero holes remain in the delivered module.
The chosen extension continues to be selected from the same unique characterization.

## No longer needed

None. No existing import, module or node is pruned. The empty original
`proof_deps` omitted the two existing theorems now used by the proof.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof plan, although the theorem docstring correctly
identified the two ingredients. Both ingredients already have proved declarations:
`exists_integral_openClosed_sections` and `relative_extension_existsUnique`.
No new intermediate statement or definition repair is necessary.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
