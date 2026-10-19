## Worker report

The repaired predicate is `AlgebraicGeometry.IsProjectiveBundle` in
`lean/Sheaf/AlgebraicGeometry/ProjectiveBundleMorphism.lean`. The original mathematical
statement is retained. Its only added statement dependency is the definition node
`def-trf-canonical-symmetric-graded-algebra`, which packages the canonical symmetric algebra
on the affine basis for the landed relative-Proj interface.

Clause-by-clause correspondence:

- The ambient schemes and their morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The module in the statement is `E : S.Modules`. Its quasi-coherence is the witness
  `hE : E.IsQuasicoherent`; its finite type is the conjunct `E.IsFiniteType`. These are
  the first two notions of `pqf-def-coherent`, used directly.
- The symmetric algebra with its symmetric-degree grading is the constructed datum
  `@SymmetricAlgebraSheaf.gradedAlgebraData S E hE`. Its ring on an affine open U is
  `SymmetricAlgebra O(U) E(U)`, and its degree-n submodule is the nth power of the
  degree-one inclusion range. The symmetric-grading lemma identifies this with the
  image of the tensor degree n. The affine comparison for the symmetric algebra sheaf
  identifies this ring with the affine sections of `SymmetricAlgebraSheaf.algebra E`.
- The projective bundle is this datum's `.relProj`, and its structural morphism is
  `.relProjHom`. These are the existing canonical gluing constructions.
- A closed embedding, including the stated isomorphism with a closed subscheme, is
  `i : X ⟶ (...).relProj` with `IsClosedImmersion i`. Closed immersions identify their
  source with the corresponding closed subscheme, so no separate source isomorphism
  witness is needed.
- The requirement that f be the resulting map over S is
  `i ≫ (...).relProjHom = f`.
- The final convention sentence distinguishes this predicate from the existing
  `IsHProjective` finite-projective-space predicate. The definition asserts no comparison
  theorem between these conventions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: the retained
  `AlgebraicGeometry.RingedSpace.IsCoherent` record documents all three notions; the two
  predicates used here are Mathlib's `SheafOfModules.IsQuasicoherent` and
  `SheafOfModules.IsFiniteType`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData.relProj` and `.relProjHom`, with the affine-basis input from
  `.RelativeProj.GradedAlgebraData`. Both full source modules were read through
  `scompile.py --source`; the landed NE dependency binding is retained.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `exists_quasiCoherentSymmetricAlgebra`, including the affine-section comparison;
  its construction uses `SymmetricAlgebraSheaf.sections`, `.restriction`, `.presheaf`
  and `.algebra` from `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`.
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images`, read from the current server. Its internal
  direct-sum clause supplies the uniquely determined decomposition used in the helper.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`, for the convention named by `def-kun-projective`.

The helper's real data are fixed by formulas: the actual symmetric section rings, the
symmetric-degree submodules, and the existing symmetric-algebra restriction homomorphisms.
The decomposition uses `DirectSum.IsInternal.gradedAlgebra`, the inverse of the bijective
summation map. Its restriction identity and composition fields use the existing presheaf
laws. There is no selection of a ring, grading, gluing datum, or map from an existence claim.
Two named well-definedness theorems have `sorry` proofs:
`restriction_mem_symmetricDegree` and `gradedRestriction_isGradedBaseChangeAlong`.
Both are explicitly included in the new node's statement and each has its complete proof
in its docstring. Only these proof properties are postponed; every definition supplies
its data in full.

Edge cases checked against Stacks Morphisms 01W8(1) and Constructions 01OB: E = 0 has
only degree zero and yields the empty projective bundle; E = O_S gives P(E) = S; a finite
free module of rank n + 1 gives P^n_S; quasi-coherent finite-type modules which are not
locally free remain allowed; an empty base admits only an empty source. The counterexample
in the return is excluded: the two generators of O^2 both occur in symmetric degree one,
so the grading with deg x = 0 and deg y = 1 cannot be substituted. No Noetherian, rank,
local-freeness or separatedness hypothesis was added. All universes and variables are
explicit, and both modules set `autoImplicit false`.

Searches for the item in the retained packet were checked against scoped project and
Mathlib searches for `IsProjective`, `ProjectiveBundle`, relative Proj and projective
morphisms. No existing predicate gives this EGA convention: the upstream `IsProjective`
uses H-projectivity. For the canonical helper, real `msearch.py` searches used LeanSearch
("Canonical affine basis symmetric algebra of a quasi coherent module with symmetric
 degree grading and coefficientwise base change"), LeanFinder (canonical symmetric algebra
 as GradedAlgebraData), Loogle (`SymmetricAlgebra, GradedAlgebraData`), and scoped Mathlib
 grep (`symmetric.*GradedAlgebraData|GradedAlgebraData.*symmetric`). Results are recorded
in the new node, together with direct `rg` searches of upstream and `lean/Sheaf`, DAG
searches, and `tools/blueprint_refs.py search`. Mathlib has ring-level symmetric algebras;
the project has the sheaf construction, grading theorem, and a presentation structure in
`ProjectiveBundleTautologicalGeometry`. That structure accepts an equivalent graded
presentation; it does not construct the canonical affine-basis datum. The new helper
constructs it from E and its quasi-coherence proof alone. The current upstream sources
missing from the older checkout were read using the authorized `scompile.py --source`.

No mathematical statement correction or disputed statement is needed. The original node
already explicitly requires symmetric degree; the returned rendering failed to enforce it.

## New nodes

`def-trf-canonical-symmetric-graded-algebra` in the item's chapter records the canonical
construction of the symmetric-degree `GradedAlgebraData` from a quasi-coherent module E.
It cites the existing scheme, module, symmetric-algebra, symmetric-grading and relative-Proj
nodes. Source: Stacks Constructions 01OB, Modules 01CG/01CL and Constructions 01LN.
Its statement explicitly records preservation of degrees and degreewise coefficient
base change, matching the two postponed well-definedness theorems. The searches above
found ingredients and the equivalent presentation structure, but no canonical constructor
for an arbitrary quasi-coherent E. Its module is
`Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`, and all five declarations,
including the actual constructor and the named proof obligations, are listed in its
`lean.declarations`.

## Repairs of the returned delivery

1. H3: the freely graded algebra witness has been replaced by the constructed
   `SymmetricAlgebraSheaf.gradedAlgebraData E`. Its actual degree-n pieces and restrictions
   cannot be varied by a witness. The nonproper affine-line counterexample is excluded.
2. H4: the current landed `def-nagata-relative-proj` record is untouched, and the item
   uses its upstream `GradedAlgebraData.relProj` and `.relProjHom`. The stale dependency
   node copy and the `RelativeProjData` import have been removed from the packet.
3. H13: the current `pqf-def-coherent` record remains attached to
   `RingedSpace.IsCoherent`. The item uses `E.IsQuasicoherent` and `E.IsFiniteType` directly.
   `ProjectiveBundleCoherentRepair.lean` and the dependency-node replacement are removed.

## Second reading by NW

This is the worker's self-check; the maintainer supplies the independent review. I read
both final modules beside their nodes and Stacks morphisms.tex 10488–10501 and
constructions.tex 4671–4690. The original item statement requires precisely a
quasi-coherent finite-type E and a closed immersion over S into Proj Sym(E). Its Lean
uses that same E in the canonical graded datum and in the finite-type/quasi-coherent
hypotheses. Its immersion source is X, and the final equality uses the structural map
of that very relative Proj. In particular there is no independent algebra, grading or
gluing witness. The same scheme universe u is used throughout.

For the new node, I checked that `obj U` is the actual symmetric algebra of E(U),
`grading U n` is the nth power of the canonical inclusion range, and `res h` uses
`SymmetricAlgebraSheaf.restriction E` with the specified direction V to U. Identity and
composition follow the existing presheaf laws; the base-change hypothesis is exactly
quasi-coherence of E. The only `sorry`s are the two named proof obligations whose
statements and full natural-language proofs are recorded. The earlier proposed
statement_change and the presentation wrapper were removed: neither was needed to
render the original correct statement. The helper now constructs real canonical data.
