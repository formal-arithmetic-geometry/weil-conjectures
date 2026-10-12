## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`
without changing its signature or the coherence definition. The forward implication constructs
finite local presentations from finite generators and the coherence kernel clause, refining and
gluing the covers. The reverse implication uses the already proved, stronger upstream theorem
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_kernel` on each open subscheme and
transports its kernel through `overEquiv`.

Added four proved private helpers: preservation of finite presentation through the inverse
open/slice equivalence, preservation of quasi-coherence through its forward functor, finite
presentation of finite free modules, and construction of finite presentations from finite
generators with a finite-type kernel. They are constructions and transport glue for the
argument, with no postponed proofs. Added the proof-only import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` for `ofEpiFree`.

Updated the theorem docstring and the item node's proof, proof dependencies and proof origin.
Added a node recording the stronger existing kernel theorem; no new Lean declaration duplicates
that theorem. The source of the local-presentation construction is Stacks 01BW, and the
Noetherian argument is Stacks 01XZ (both read directly on the Stacks website, since the cited
literature files are absent from this clone). The blueprint unit's `realized` lists are empty;
the unit's proper-and-quasi-finite route is unchanged.

## Proved and sorry left

The item's only original sorry, in
`AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`
(node `pqf-lem-coherent-ft-locnoeth`), is replaced by a full proof.
No sorry remains in the delivered Lean module; no sorry is added elsewhere or split off.
The four private helpers are proved. The new node records the existing proved
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_kernel`.

The construction permits an empty scheme and empty covering index sets. Finite generator sets
of cardinality zero are reindexed by `ULift (Fin 0)`. A finite free module's presentation uses
`PEmpty` for its zero relations, so the rank-zero case is included. The reverse implication
applies to arbitrary maps, including the zero map, and does not require the map to be epi or
its target to have finite sections. Local Noetherianness supplies the Noetherian condition on
all open subschemes. No target or intermediate statement is changed.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.
The proof no longer uses its sorry-bearing `quasicoherent_finite_type_affine` theorem or node
`lem-weil-pbc-quasi-coherent-finite-type-affine` as a proof dependency: finite presentation
implies quasi-coherence directly in Mathlib, and the source-library kernel theorem proves the
reverse implication without this affine-criterion placeholder.

The item's former direct proof dependencies `lem-weil-pbc-affine-tilde-gamma-adjunction`,
`def-weil-pbc-noetherian-ring` and `lem-weil-pbc-quasi-coherent-module-kernel` are encapsulated
in the already proved upstream kernel theorem rather than separate obligations of this item.
Its source module and the Mathlib Noetherian/tilde results remain transitively imported; no
claim is made that these proved source dependencies disappear from the library closure.
The coherence and local-Noetherian definitions remain required public imports.

## Where the brief, the DAG or earlier work was wrong

The planned forward proof called the affine criterion just to deduce quasi-coherence from
finite presentation. Mathlib already provides this implication as an instance, so that
sorry-bearing dependency is unnecessary. The planned reverse proof overlooked the stronger,
fully proved `isFinitePresentation_kernel` in the module it already imported; the old kernel
node only names `isQuasicoherent_kernel`. The new node records precisely the stronger theorem
used, without altering the old node's statement.

The large concrete sheaf and equivalence expressions require explicit universes, ring sheaves,
source schemes and continuity arguments. Generic helpers avoid repeated unfolding of free
presentations. A local `maxHeartbeats 300000` budget is used for the complete main proof;
the project wrapper still enforces its unchanged 60-second wall-clock limit.

## New nodes

`lem-pqf-kernel-finite-presentation-noetherian` records the existing source-library theorem
that the kernel of a map from a finitely presented module to a quasi-coherent module on a
locally Noetherian scheme is finitely presented. Its Lean signature was read at
`lean/WeilConjectures/AlgebraicGeometry/Modules/QuasicoherentKernel.lean:287`, and its proof
at lines 284–310. No new Lean file or sorry is associated with this node. The node's proof
step applies that existing proved declaration and records its affine argument. Its source
is the Noetherian finite-module argument of Stacks 01XZ. LeanSearch was unavailable with HTTP
500; LeanFinder found only general finite-presentation facts; logged Mathlib grep found no
kernel declaration, while repository rg found the exact proved upstream theorem. DAG and
blueprint searches found no existing node with this stronger statement or Lean declaration.
The maintainer can attach the proved source declaration in `lean_audit`; its audit state is
left for the maintainer's tooling. No change record is needed.

## Second reading by H1

1. **Visible statements unchanged — pass.** Read the full source diff against the
   repository. The sole existing theorem's signature is byte-for-byte identical,
   including its universe, locally Noetherian hypothesis, and both conclusions.
   No existing definition changed. The four added helpers are private, proved
   propositions. Both public imports serve the statement; the added generators
   import is proof-only. There is no statement change requiring a change record.
2. **Proof and axioms — pass.** Independently compiled the delivered module with
   `lcompile.py`: no errors or warnings (55.1 seconds). Compiled a scratch copy
   printing the axioms of the main theorem, all four private helpers, and the
   upstream kernel theorem (52.6 seconds). Every list is exactly `propext`,
   `Classical.choice`, `Quot.sound`; none contains `sorryAx`. The source has no
   `sorry`, forbidden declaration, kernel-check bypass, or hollow definition.
3. **New obligations and edge cases — pass.** Nothing is split off. Read the
   existing `isFinitePresentation_kernel` statement and proof: its target needs
   only quasi-coherence, so its application to every finite free map is valid,
   without surjectivity or finite-type assumptions on that target. The new node
   records this existing theorem rather than duplicating it. Checked zero rank,
   the zero map, empty opens/schemes, and empty covers: the constructions do not
   assume positive rank or a point. The private finite-free presentation uses
   zero relations, and the generators/kernel construction composes an actual
   relation epimorphism with the restricted kernel inclusion.
4. **Shortest route, imports, and pruning — pass.** Searched Mathlib's sheaf
   modules with the additional logged pattern
   `free.*IsFinitePresentation|IsFinitePresentation.*free|IsCoherent` (no hits),
   and searched the repository for coherence, finite-free presentations, and
   slice-equivalence transport. The upstream coherence abbreviation denotes a
   different predicate, so it does not replace this argument. The available
   pushforward transport lemmas are already used. Every retained import is
   justified. Compared old and new `proof_deps`: all four removed nodes appear
   under `No longer needed`. Read the unit record; its statement and step
   realizations are empty, and this proof changes no unit route. The blueprint
   source files are absent locally, as already noted in the first report.
5. **DAG agreement — pass.** Only `proof`, `proof_deps`, and `proof_origin`
   change in the existing node. Their two implications match the Lean proof,
   including local finite presentations and kernel transport through `overEquiv`.
   The new node has source, proof, origin, search records, creation record,
   blueprint provenance, chapter/unit, and the existing Lean attachment.
   Its hypotheses and conclusion match the upstream declaration read directly.

Second-reading changes: appended this independent review and logged the
additional Mathlib search. No repair to the Lean proof or DAG was needed.
