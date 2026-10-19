# Repair publication blocked by the upstream derived braiding rename

The stage-3 item `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` repeatedly
failed at its public import of `Sheaf.Paper.ZlOpenDiagramComparisonTransport`.
The transport source landed in e180c0506680419c560db5ff9ea3adf84642da77 and
already compiles in the build tree, but has never reached a green publication.
The last published build was d4d0a14fb18da3ddde7d93b307879ca0bb04a775,
2026-10-19T02:56:25Z. The current red build has only three unknown-constant
errors, in the two modules below.

Upstream sync ee8622b47b6b072e9c8fa488e1cb815ac6156d73 renamed the canonical
`CategoryTheory.DerivedMonoidal.braiding` to `braiding'`, preserving its body.
Adapt the three remaining references in:

- `lean/Sheaf/Paper/FiniteFreeCoefficientExtension.lean`, line 426,
  `IsProKoszulSymmetry` (claimed by T5 when inspected).
- `lean/Sheaf/SixFunctors/CoefTowerNaturalCurrying.lean`, lines 227 and 506,
  `coefCurryingPointEvaluation` and `CoefCurryingModels.finiteArrow`
  (claimed by F2 when inspected).

The original compiler error at each location was
`Unknown constant CategoryTheory.DerivedMonoidal.braiding`.
Only these forced references change. Signatures, visibility, docstrings,
mathematical content, imports, and sorry counts are preserved. This is a
mechanical adaptation to the canonical upstream API, not new mathematics.
The item and its retained sandbox proofs are untouched.

Validation: corrected copies compiled sequentially using `tools/lean_file.sh`
with `SHEAF_TREE=local/buildtree`, `SHEAF_FILE_TIMEOUT=60`, and no group overlay:
FiniteFreeCoefficientExtension in 24.7 s; CoefTowerNaturalCurrying in 32.5 s.
Both exited 0. The pre-existing global build loop will consume the source
repair; this maintenance session does not invoke a global build or publish
individual artifacts out of a red snapshot.

Original source backups are under
`local/maintenance/R5-1792399835/lean/`, with `.bak` appended to each path.
A copy of this new change record is kept under the same backup directory.
The next stage-3 worker should resume the retained sandbox and repeat the
required delivery dry run after the next green publication.
