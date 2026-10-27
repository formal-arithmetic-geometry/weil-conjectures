## What changed

Replaced the hole in `WeilConjectures.SystemTensorMate.system_clopen_tensor_compatibility`
by the proper-adjunction transpose calculation in the original system categories.
The target signature, definitions, public import, and existing docstrings are unchanged.
The proved private helper `mate_tensor_interchange` carries out the formal argument
in arbitrary categories, avoiding reduction of the large geometric functor definitions.
The private helper `delta_naturality_left` proves first-variable naturality of the
canonical open tensor map from its open-unit-defined inverse. The main proof uses
projection counit identities, the mate counit identity, alpha and mu naturality,
and bifunctoriality. It never inverts gamma or a projection map.

The geometric remainder is stated in the new module
`Sheaf.Paper.SystemClopenAlphaTensorSquare`. Its theorem is the alpha/tensor square
of Steps 2--3 of the existing proper/open projection-mate calculation, before either
proper adjunction is transposed. It contains no gamma, projection, or derived proper
direct image in its conclusion. The parent proof genuinely performs the remaining
mate calculation; the new statement does not rename or repackage the parent.

The existing parent node now describes that argument. The new node records its
ringed-site square and presentation-identification dependencies, sources, proof,
and actual Mathlib searches. All writes are confined to this item's sandbox.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.SystemTensorMate.system_clopen_tensor_compatibility`
(node `lem-pur-system-clopen-tensor-compatibility`) by reduction.
Proved the private helper
`WeilConjectures.SystemTensorMate.delta_naturality_left` and
`WeilConjectures.SystemTensorMate.mate_tensor_interchange` without new holes.

Added exactly one hole:
`WeilConjectures.SystemTensorMate.system_clopen_alpha_tensor_square`
(node `lem-pur-system-clopen-alpha-tensor-square`). Its entire proof is `by sorry`;
its docstring gives the complete geometric tensor-square argument and source.
This is a decomposition: one old hole closed, one strictly intermediate hole added,
net zero holes. The item module itself has zero remaining holes.

Validation: the parent compiles cleanly in 13.0 seconds; the new statement module
compiles cleanly in 9.2 seconds, through `lcompile.py`. The parent statement is
byte-identical to the original. No profiling options remain. Delivery checks follow.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`;
- `Sheaf.Paper.SemilinearDerivedSections`;
- `Sheaf.SixFunctors.OpenTensorNormalization`;
- `Sheaf.SixFunctors.ProperOpenProjectionMate`.

The first three remain public prerequisites of `SystemTensorMateArrows`; their
mathematics is retained. The intrinsic `properOpenProjectionMateSystems` theorem
is no longer applied by the parent proof: the formal transpose calculation is
proved here instead. The new alpha-square node retains the existing tensor
presentation and clopen-arrow identification nodes, and uses the existing ringed-site
`lem-sf-clopen-comparison-tensor-square`. The clopen identification module still
imports `ProperOpenProjectionMate`, so this delivery does not claim that module or
its unfinished declarations are globally pruned. No module or declaration is
withdrawn. No source-library file is changed, and no unit statement or unit proof
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The former short assembly is not a direct Lean specialization. The supplied
`properOpenProjectionMateSystems` has `E : Type u` for `Scheme.{u}`, whereas this
item has `E : Type (u+1)`. `Realization.properOpenFactors` explicitly compares the
former interface only with `TensorOperations l (ULift E)`, and its conclusion is
a collection of factor comparisons, not the parent equality for arbitrary supplied
operations in the latter universe. The original tensor-presentation theorem
also concludes existence of compared operations, not equality of the desired paths.
The clopen identification's first theorem supplies alpha and its mate formula,
while its realization theorem uses the former realization interface. Thus writing
`exact properOpenProjectionMateSystems ...` does not implement the planned assembly.
The delivery keeps the same geometric clopen tensor argument but proves its
formal proper-mate passage directly, avoiding that extra interface transport.

Checked the new alpha-square statement on the identity square, a cartesian square,
the empty selected component, and a noncartesian selected clopen summand. In the
last case both sides use the same identity/zero projector. Its final square arrow
is `P_k P_p -> P_r P_i`, matching the parent. No boundedness, coefficient flatness,
cartesianness of systems, or invertibility of proper projection is introduced.

## New nodes

`lem-pur-system-clopen-alpha-tensor-square`, in the parent's chapter and unit,
records precisely the pre-mate geometric square, with a Lean module of its own.
It cites the existing ringed-site full tensor-square theorem and the existing
presentation and alpha identifications; none is duplicated. Mathlib semantic
searches returned generic algebraic tensor/base-change or categorical adjunction
facts, not this geometric normalization. Blueprint search for `clopen tensor`
returned zero blueprint nodes; the existing ringed-site node is explicitly retained
as a dependency. The new node has no dependency path back to the parent.

No definition, statement, exported option, instance or attribute changes, and no
consumer adaptations or change records are needed.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
