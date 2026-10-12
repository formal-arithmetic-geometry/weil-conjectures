## What changed

The existing signature of `Algebra.exists_popescu_flat_coordinates` is unchanged.
Its proof extracts an admissible A₀ containing E, constructs flat coordinates in an admissible
enlargement A, and explicitly transfers containment along A₀ ≤ A. The two strict intermediate
statements live in separate modules. Proof-dependency imports were moved to those modules;
all original public imports of the main module remain unchanged. No definitions were changed.

## Proved and sorry left

Closed the original hole `Algebra.exists_popescu_flat_coordinates` by reduction.
Added two holes: `Algebra.exists_popescu_admissible_containing_finset`
(node `lem-weil-pbc-popescu-flat-coordinates-a0`) and
`Algebra.exists_popescu_flat_coordinates_given_admissible`
(node `lem-weil-pbc-popescu-flat-coordinates-given-admissible`).
Both remain named public theorems with complete natural-language proofs in their docstrings.
This is a decomposition, not an axiom-free proof: one hole closed, two added (net -1).
The main theorem depends on sorryAx through those intermediates. No hole was added to a definition.

## No longer needed

The main module's following direct proof imports were replaced by the two intermediate modules;
they remain dependencies of those intermediate proof plans and no transitive pruning is claimed:

- `Sheaf.RingTheory.ArtinianFlatSubalgebras`
- `Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`
- `Sheaf.RingTheory.FlatOverRegular`
- `Sheaf.RingTheory.GeometricallyRegularH1Injective`
- `Sheaf.RingTheory.GeometricallyRegularOverFieldFlat`
- `Sheaf.RingTheory.LocalizationOfRegularRing`
- `Sheaf.RingTheory.PolynomialOriginRegularLocal`
- `Sheaf.RingTheory.PopescuSolutionModuloChoose`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`

All old direct proof_deps of the main node were replaced by the two intermediate nodes.
The complete old direct dependency list is:

- `def-weil-pbc-flat-ring-map`
- `def-weil-pbc-g-ring`
- `def-weil-pbc-kahler-differentials`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-mv-polynomial-ring`
- `def-weil-pbc-regular-sequence`
- `def-weil-pbc-smooth-ring-map`
- `def-weil-regular-scheme`
- `lem-weil-pbc-criterion-flatness-fibre-noetherian`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-flat-over-regular`
- `lem-weil-pbc-geometrically-regular-h1-injective`
- `lem-weil-pbc-geometrically-regular-over-field-flat`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-localization-of-regular-ring`
- `lem-weil-pbc-nakayama-local-generators`
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`
- `lem-weil-pbc-polynomial-ring-origin-regular-local`
- `lem-weil-pbc-popescu-artinian-flat-subalgebras`
- `lem-weil-pbc-popescu-solution-modulo-choose`
- `lem-weil-pbc-regular-local-generators-regular-sequence`

These are removed direct edges, not claims that the corresponding modules left the targets' closure.
No module is claimed pruned. The unit `sk-thm-p1` and all its realized statement/step nodes remain intact.

## Where the brief, the DAG or earlier work was wrong

The prior conditional intermediate repeated the full target conclusion with extra inputs.
Second reading replaced E and its containment hypothesis with the structural conclusion A₀ ≤ A,
so the main proof itself derives the finite-set part. The prior docstrings did not contain complete
proofs, and the split-node proof plans omitted most dependencies. Both faults were repaired.
The previously reported `refuse_missing` import failure no longer reproduces: deliver3.py now
reaches preflight. No workaround or modification of project or launcher tools was made.

## New nodes

`lem-weil-pbc-popescu-flat-coordinates-a0`: localization, prime-power Artinian quotient,
finite residue cotangent homology, then directed-cover finite-set extraction (Tag 07FG).
`lem-weil-pbc-popescu-flat-coordinates-given-admissible`: corrected admissible enlargement,
first polynomial flat map, regular closed-fibre parameters, and fibre-flatness (Tag 07FH).
Both nodes carry source, searches, creation metadata, Lean signatures verbatim, and detailed
proof dependencies. No existing statement change and no change record is required.

## Second reading by M2

1. Compared the main module with the repository by diff and checked its declaration signature
   byte for byte. PASS: only its proof and private proof imports changed. No existing definitions,
   declaration visibility, targets, or other existing modules were changed.
2. Compiled all three modules with lcompile.py in import order. Checked the source for forbidden
   declarations and checked axioms in scratch copies. PASS with the two explicitly listed holes:
   only propext, Classical.choice, Quot.sound and sorryAx are allowed/observed. No hollow definition
   or arbitrary-witness definition exists in the delivery.
3. Read both new statements against Tags 07FG/07FH and the upstream admissible enlargement.
   Checked E empty, n = 1, q = 0 in a field, and the zero-dimensional closed fibre (no added
   parameters). The cover is nonempty because B is nontrivial and 0 belongs to a covering member;
   the empty finite set causes no failure. Both statements are true strict argument parts.
   Searched leanfinder, loogle, Mathlib sources through msearch.py, and local Lean sources with directed-cover and flat-coordinate
   queries. Mathlib supplies finite-set extraction, but not the geometric hypotheses needed to
   apply it here. LeanSearch was also attempted for both nodes and returned Internal Server Error;
   this unavailability is recorded without a search verdict. The full split proofs require substantial remaining work, not a few-minute closure.
4. PASS after repairs: the main proof combines the extraction and coordinate construction and
   transports E along inclusion. Original proof-dependency routes are preserved inside the split
   modules, imports used only by these plans are private, and the full removed-edge list is above.
   Read `dag/units/sk-thm-p1.json`: this node is below the unit's realized nodes; none is bypassed.
5. PASS after repairs: main-node steps/dependencies now match the Lean reduction; split-node
   steps partition the old argument, with complete dependency unions and verbatim Lean signatures.

Changed the conditional intermediate to return A₀ ≤ A; repaired the main proof accordingly;
expanded both split proof docstrings; corrected split DAG statements, signatures, proof plans,
search records and dependencies; removed the unused public Kaehler import from the A₀ module;
restored private proof-plan imports in the split modules; corrected progress and pruning claims.
