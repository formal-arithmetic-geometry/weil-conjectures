## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian` states
`AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`.
It binds a scheme `X : Scheme.{u}` with the instance hypothesis
`[IsLocallyNoetherian X]` and an `O_X`-module `F : X.Modules`. Its conclusion is the
iff in the node: `RingedSpace.IsCoherent X.toRingedSpace F` on the left, and the
conjunction `F.IsQuasicoherent ∧ F.IsFiniteType` on the right. The theorem proof is
`sorry`, as required at stage 2.

The proof docstring records both source directions. In the forward direction the
finite-type and finite-kernel clauses of `pqf-def-coherent` produce a local finite
presentation, and `lem-weil-pbc-quasi-coherent-finite-type-affine` yields
quasi-coherence. In the reverse direction, quasi-coherence makes kernels
quasi-coherent via `lem-weil-pbc-quasi-coherent-module-kernel`; on affine opens the
finite-type criterion gives finite sections, and the Noetherian finite-generation
induction makes kernel sections finite, so the same criterion gives finite type for
the kernel and hence coherence.

No `stmt_deps` are listed for this node, so no dependency declaration is used in the
statement itself. The module imports the existing `RingedSpace.IsCoherent` definition
from `Sheaf.AlgebraicGeometry.Coherent` and Mathlib's locally Noetherian scheme
notion from `Mathlib.AlgebraicGeometry.Noetherian`.

Edge cases checked: `F` is arbitrary, including the zero module; the finite-rank
argument includes rank zero; `X` is not assumed nonempty or quasi-compact, so empty
schemes and arbitrary locally Noetherian schemes remain covered; the universe of `F`
is the scheme universe `u`.

Searches made: `msearch.py C1 pqf-lem-coherent-ft-locnoeth leanfinder "coherent O_X-module on a locally Noetherian scheme iff quasi-coherent and finite type"` (only general locally Noetherian facts); `msearch.py ... loogle "SheafOfModules.IsFiniteType IsFinitePresentation IsQuasicoherent"` (no hits); grep of Mathlib module files for `IsFiniteType|IsFinitePresentation|coherent` (no exact equivalence); `rg` over `WeilConjectures/` and project `lean/Sheaf` (the project has the definition `RingedSpace.IsCoherent` but no theorem with this statement). The existing definition is imported rather than duplicated.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the module signature clause by clause. The module
has exactly the locally Noetherian hypothesis, the scheme `X`, and the module `F`;
its left side is precisely coherence on `X.toRingedSpace`, and its right side has
both quasi-coherence and finite type. No hypothesis or conclusion was added, removed,
or specialized. The module uses the already landed coherence definition and does not
introduce a second notion. The empty scheme and zero module remain included, and the
statement is polymorphic in the scheme universe.

## Second reading by C1

I read the node, the delivered module, and Stacks `coherent.tex`, section
`section-coherent-sheaves`, lemma `lemma-coherent-Noetherian` (Tag 01XZ), from
`/home/ubuntu/c1-stacks-review/`. The section assumes locally Noetherian schemes;
the lemma adds no separatedness, quasi-compactness, field, or characteristic
hypothesis. The node selects precisely equivalence (1) with (2) of that lemma;
its other equivalent characterizations and final examples are not node clauses.

The complete object/hypothesis/conclusion checklist is:

- A scheme X: `(X : Scheme.{u})`. Verdict: same object, arbitrary universe u.
- X locally Noetherian: `[IsLocallyNoetherian X]`. Verdict: exact hypothesis.
  I opened Mathlib `AlgebraicGeometry/Noetherian.lean`: the class requires
  `IsNoetherianRing` for sections on every affine open, equivalent to the local
  affine-cover definition; it does not require global quasi-compactness.
- An arbitrary O_X-module F: `(F : X.Modules)`. Verdict: exact object.
  I opened Mathlib `AlgebraicGeometry/Modules/Sheaf.lean`: `Modules` is
  `SheafOfModules.{u} X.ringCatSheaf`, not the quasi-coherent subcategory.
- F coherent: `RingedSpace.IsCoherent X.toRingedSpace F`. Verdict: exact clause.
  I opened the node `pqf-def-coherent` and its recorded module
  `Sheaf.AlgebraicGeometry.Coherent`, declaration
  `AlgebraicGeometry.RingedSpace.IsCoherent`. Its body is finite type and,
  for every open U, every n : Nat and every map from the free module on
  `ULift (Fin n)` to `F.over U`, finite type of the kernel. This is Stacks
  `modules.tex`, `definition-coherent` (01BV), with maps encoding collections
  of sections. The ringed-space carrier specializes to exactly X.Modules.
- F quasi-coherent: `F.IsQuasicoherent`. Verdict: exact clause. I opened
  Mathlib `ModuleCat/Sheaf/Quasicoherent.lean`: local cokernel presentations by
  free modules match Stacks `definition-quasi-coherent` (01BE), and on schemes
  give the affine-local tilde formulation of `pqf-def-coherent`.
- F of finite type: `F.IsFiniteType`. Verdict: exact clause. Mathlib
  `ModuleCat/Sheaf/Generators.lean` uses local finite generating sections,
  matching Stacks `definition-finite-type` (01B5), equivalently local finite
  free surjections.
- If and only if, with both right-hand clauses: `↔` and `∧`. Verdict: both
  directions, correct order, no additional hypothesis or conclusion.

Although stmt_deps is empty, I inspected the above defining declarations and
coherence node rather than relying on names. No new nodes or dependency modules
are part of this delivery. The theorem introduces no definitions, has only a
`sorry` proof, and has the required source and blueprint docstrings.

Edge cases: empty schemes and empty opens are allowed; no Nonempty or compactness
binder occurs. The zero module is allowed. The coherence predicate quantifies
over every natural rank, including n = 0, and ULift preserves the empty rank-zero
basis. There is no characteristic or base-field restriction. The scheme and
module use the shared arbitrary universe u, per the recorded module category;
there is no independently smaller universe for test objects and no index family
in the statement. Every variable and universe is explicitly bound.

Independent searches, using different wording from the first worker:
`msearch.py ... leanfinder "locally noetherian scheme coherent sheaf equivalence
finitely generated quasi coherent"` returned IsFiniteType and general locally
Noetherian scheme facts, no equivalence. `msearch.py ... loogle '"IsCoherent"'`
returned only topological IsCoherentWith declarations. LeanSearch with
"A sheaf of modules on a locally Noetherian scheme is coherent if and only if it
is quasi coherent and finite type" was unavailable (Internal Server Error).
I also ran rg for `isCoherent|IsCoherent|coherent.*[Nn]oetherian` and the reverse
word order in Mathlib's AlgebraicGeometry and module-sheaf directories, the
source WeilConjectures tree, and project lean/Sheaf; then searched the latter two
for `isCoherent_iff|IsCoherent.*iff|IsCoherent.*↔`. No exact theorem exists.
I opened upstream `AlgebraicGeometry/Modules/Coherent.lean`: its lowercase
`Scheme.Modules.isCoherent` is quasi-coherent plus finite presentation, not the
Stacks kernel definition, and supplies no theorem relating that definition to
finite type. It cannot replace this delivery.

No signature or node-statement mismatch was found, so both are preserved.
The proof docstring omitted the node's explicit justification that the finite
free source is quasi-coherent and compressed the Noetherian induction. I added
its citation `lem-weil-pbc-affine-tilde-gamma-adjunction (4)` and the induction
steps (rank zero, projection, lifted image generators, last-coordinate ideal).
This completes the step-by-step proof handoff without proving anything.
The worker report's sentence saying no dependency declaration is used should be
read as no *listed stmt_deps*: the existing coherence declaration is imported
and used, as checked above. Compilation and delivery preflight are run below.

Validation: scompile completed with exit code 0 in 2.5 seconds and no warnings.
A direct check confirmed lean.statement equals the file signature verbatim and
all Lean lines are at most 100 characters. deliver2 --no-push printed OK:
preflight passed and server compilation passed.
