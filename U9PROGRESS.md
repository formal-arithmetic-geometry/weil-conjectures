# K7 progress

## 2026-11-05: initial inspection

- Branch `u9/K7` starts at `0dfd479395d8cc40e120d97c94d36f96e5ade9c9`, the
  existing merge of `nativetensor` with `slopmaster2` at `19ba966718`.
- The leaf already has its intended proof, and the approved symmetry conjunct is
  proved by `canonical_ordinary_tensor_symmetry`. Preserve both.
- Read the Lean skill and performance guide. All compilation will use `ucheck`.
- Checked the six specified PR branches: none changes the leaf or tensor swap
  modules, so no additional PR merge is needed for this repair.
- Compared the underived proof with `origin/iface-start:lean/Sheaf/Paper/`.
  The starting branch already has an explicit `Mono` instance for `binary_square`.
- Plan: validate the underived module first, repair the remaining build failure,
  then validate the leaf and every module changed relative to `slopmaster2`.
