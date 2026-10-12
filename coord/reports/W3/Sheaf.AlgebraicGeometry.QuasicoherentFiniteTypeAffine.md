## What changed

Proved `AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine` in
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`, with its original signature,
universes and visibility. All added helpers are private, proved theorems in the same module.
No definitions, public signatures, public imports or other modules changed.
The static scanner flags the additional elaboration commands (`open`, scoped universes and
helper variables) as an interface change. The requested record is
`coord/changes/quasicoherent_finite_type_affine_proof_scope.md`; it names the current holders
and explains why no downstream adaptation is forced.

Finite type uses finite generating families, the affine tilde equivalence, and descent of
finite generation along basic-open localizations. The helpers prove transport of finite
generators and locality for an arbitrary-universe cover, so the empty scheme and empty cover
are included. The reverse affine implication constructs the epimorphism from the linear
combination map of a finite spanning set. It does not construct an unnecessary presentation.
Finite presentation uses the already proved `FiniteDescent` declarations, transported through
`overEquiv`, restriction composition and `sectionsRestrictFromSpecLinearEquiv`.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`. Kept the original public statement
imports. Updated the item's DAG proof, proof dependencies and proof origin to this route.
The item is not one of the unit's realized statement/step nodes; the unit route is preserved.

Searches actually run through `msearch.py`: LeanFinder for the affine finite-type criterion;
Loogle for `SheafOfModules.IsFiniteType`; grep for `finite_sections_of_isFiniteType`.
They found the finite-type data APIs but no complete affine criterion. Local searches found
`finite_sections_top_of_isIso_fromTildeΓ`, `finitePresentation_sections_top`,
`exists_presentation_isFinite_of_finitePresentation`, and
`finitePresentation_sections_of_isFinitePresentation`; their source signatures and proofs
were read. The added proof import passed `import_direction.py may`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine`
(node `lem-weil-pbc-quasi-coherent-finite-type-affine`). This is a proof, not a decomposition:
1 hole closed, 0 holes added, 0 split off. No `sorry` remains in the delivered module, and no
new theorem with `sorry` is imported or introduced for this proof.

The full file compiles with `lcompile.py`, without warnings. The first delivery dry run also completed its axiom probe without reporting a disallowed
axiom. Its only static issues were the requested elaboration-command change record and the
second reader's pending section. The change record is now supplied.

## No longer needed

Removed these direct proof imports and pruned their theorem nodes from this item's proof:

- `Sheaf.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType`:
  `lem-weil-pbc-finite-presentation-kernel-surjection-finite-type`.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`:
  `lem-weil-pbc-quasi-coherent-module-cokernel-image`.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`:
  `lem-weil-pbc-quasi-coherent-module-kernel`.

Also removed `lem-weil-pbc-principal-localization-open-immersion` from this item's proof
route: the argument uses the existing basic-open localization APIs, without constructing
`Spec R_f → Spec R` and invoking that immersion theorem separately. It had no direct proof
import in the original module.

The last module remains a transitive import of `FiniteDescent`; this proof uses its proved
finite-generating-sections lemma, not its quasi-coherent-kernel theorem. The first two modules
are not needed by the delivered argument. Global pruning of any module still reached by
another target is the maintainer's determination. All other original mathematical dependency
nodes remain: restriction, tilde/free modules, localization, basic-open cover/unit-ideal
comparison, and finite generation descent are used directly or by the selected source proofs.

## Where the brief, the DAG or earlier work was wrong

The original nine-step plan was longer than necessary. The current public definition of
quasi-coherence is Mathlib's local-presentation definition, so finite presentation implies
quasi-coherence by an instance; the old docstring's cokernel argument for clause (0) is
unnecessary. The source library already proves the needed finite-presentation section and
presentation results, eliminating the planned finite-type-of-kernel argument.

The expected Stacks `.tex` paths are absent on this machine. Read the official tag pages
[01PB](https://stacks.math.columbia.edu/tag/01PB),
[01PC](https://stacks.math.columbia.edu/tag/01PC), and
[01BO](https://stacks.math.columbia.edu/tag/01BO), together with the local proved source-library
files. No new unproved statement or unsupported construction was necessary. The first dry run's
conservative command-interface classification is documented in the change record rather
than bypassed; all actual exported signatures and public imports stay identical.

## Second reading by W3

1. PASS: compared the complete delivered module with the repository using `diff`, and
   checked the existing public theorem's signature byte for byte from `theorem` through
   `:= by`. Its hypotheses, conclusion, universes and visibility are unchanged. No
   definition changed. The two public imports are unchanged; the replacement import is
   proof-only. Read the elaboration-scope change record: the extra commands scope private
   helpers and do not change the theorem's interface. No forced adaptation is needed.
2. PASS: independently compiled the original delivered file without errors or warnings,
   then compiled a scratch copy of the revised file with `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine`. It reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered source
   contains no `sorry`, axiom, unsafe/opaque declaration, implemented_by or extern.
   The 18 remaining private helper theorems are proved. The finite spanning set is extracted
   from proved finite-generation data; the surjection is the explicit linear-combination
   map. There is no arbitrary witness chosen from an unproved existence theorem.
3. PASS: no statement is split off and no hole is added. Read the finite-type transport,
   cover composition, localization descent, finite-free surjection and affine equivalence
   arguments, and the existing finite-presentation proofs in `FiniteDescent`. Checked the
   zero module, empty spanning set, zero ring/empty affine scheme, and an empty cover of
   the empty scheme: none of these arguments assumes a nonempty index type or scheme.
   Independent `msearch.py` grep searched finite-type isomorphism, pushforward, cover and
   local-generator APIs; local `rg` also checked Mathlib's sheaf generators and
   quasi-coherence files and the library. No existing complete finite-type affine criterion
   or shorter matching transport API was found. There is no restatement with a new hole.
4. PASS after pruning: the proof uses the proved upstream affine finite-presentation
   APIs directly, and constructs only the needed finite generating surjection for the
   finite-type converse. The added import is needed for these APIs; retained public imports
   serve the statement. `No longer needed` lists all four old proof dependencies removed
   from the route, including the principal-localization node with no direct import.
   Read `dag/units/sk-thm-p1.json`: this item is absent from its realized statement/steps,
   which remain unchanged. Removed the unused private helpers `finiteType_over` and
   `finitePresentation_over`; neither was called by the proof.
5. PASS after correction: only `proof`, `proof_deps`, and `proof_origin` differ in the
   existing node. Checked that `proof_deps` equals the union of the proof steps' `uses`
   and that the described steps follow the Lean proof. Removed the stale mention of
   `finiteType_over` from the node's transport step. The node's statement and Lean record
   are unchanged; no new nodes are required.

Second-reader changes: removed two unused proved private helpers and corrected the DAG's
helper inventory. The original hole remains closed, with zero holes added and zero split off.
The revised axiom-checking scratch copy compiles without warnings in 40.7 seconds.
