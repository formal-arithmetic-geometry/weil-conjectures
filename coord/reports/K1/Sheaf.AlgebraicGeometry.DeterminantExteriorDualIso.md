## What changed

Replaced the sorry in `AlgebraicGeometry.exteriorSheaf_dual_iso` with a complete Lean
assembly of a determinant-formula morphism and its bijectivity on trivializing opens.
The proof obtains a finite free cover, applies the local bijectivity theorem below
every covering open, invokes the existing coversTop criteria and the sheaf
local-bijectivity criterion, reflects the resulting isomorphism, and uses `asIso`.
The original signature and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.DeterminantDualPairing` and
`Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal` as two distinct mathematical
parts of the original route. Construction holds for every sheaf and degree, without
local freeness; local perfection concerns a specified map on one free open, without
a global finite local freeness hypothesis. Neither new statement restates the goal.
The source is the determinant inversion in Stacks Tag 0BRT, with its implicit local
argument expanded, and Mathlib's finite-free exterior determinant pairing.

Both new statements and the original module compile cleanly using lcompile.py.
The local statements were checked on n=0, r=0, n>r, zero section rings, and empty
opens: empty determinants give 1; higher exterior modules vanish; zero rings and
empty opens yield bijections of zero modules. No nontriviality hypothesis was added.
No definition was added and no data was chosen for a definition.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exteriorSheaf_dual_iso` (node
`lem-sc-determinant-dual-evaluation-dual-identification`); the item's module has
no sorry left.

Added two holes, each with its complete proof in words:

- `AlgebraicGeometry.exterior_dual_pairing_exists`, node
  `lem-sc-exterior-dual-pairing-construction`.
- `AlgebraicGeometry.exterior_dual_pairing_app_bijective`, node
  `lem-sc-exterior-dual-pairing-local-bijective`.

This is a decomposition: one original hole closed, two lower holes added, net -1
before pruning. It does not claim an independent sorry-free proof of determinant
exterior duality. The named external dependencies of the exterior-sheaf definition
are retained as existing dependencies.

## No longer needed

Removed the redundant proof imports
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` and
`WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective`, and the direct proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: the statement API
already comes through the unchanged public import of `Modules.Dual`.
No entire module is claimed to leave the targets' transitive import closure.
The old direct proof dependencies `def-pur-sheaf-hom`,
`def-sc-sheaf-exterior-power`, `lem-sc-exterior-power-dual-pairing`, and
`lem-weil-pbc-exterior-power-free-basis` are no longer direct steps of the assembly
proof; all remain used by the two new nodes. No mathematical node is discarded. The original theorem directly
uses the two new nodes and finite local freeness; its proof_deps were updated.
The unit's route and its realized statements and proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The ring-module pairing and basis declarations do not themselves construct a
morphism involving exterior sheafification and internal Hom. The DAG had no usable
sheaf-level statements for construction or local section bijectivity. The delivery
isolates these as two strictly smaller steps instead of moving the whole target.
The blueprint ancestor command returns None for the original node's created-item
chain (its created.item is a module name); the new nodes inherit its explicit
blueprint.from anchor `lem-sc-finite-duality` and extend its via chain.

The source checkout has no local literature/stacks-project/duality.tex; the source
was read at https://stacks.math.columbia.edu/tag/0BRT. This tag uses the final
inversion but does not spell out the general exterior-degree pairing. The local
proof is explicitly recorded as the expanded argument of the original node,
supported by Mathlib pairingDual, basis_coord and the finite dual basis.
The original docstring and inherited search results mention bijective_pairingDual,
but that declaration is absent in the installed Mathlib; the second reading
corrected the new local lemma docstring and proof metadata accordingly.

LeanFinder, Loogle and grep found the ring-module pairing and basis results, not a
sheaf-level comparison. LeanSearch returned Internal Server Error and is recorded
as unavailable. Searches of the project and imported blueprint found no duplicate
of either new statement.

## New nodes

`lem-sc-exterior-dual-pairing-construction`: a determinant-formula morphism for every
sheaf in every exterior degree; its remaining work is alternating universality,
restriction compatibility and the two sheafification extensions. Module
`Sheaf.AlgebraicGeometry.DeterminantDualPairing`. Source: original determinant
pairing argument for Tag 0BRT and Mathlib Pairing.lean:64-74.

`lem-sc-exterior-dual-pairing-local-bijective`: sectionwise bijectivity of any map
with that formula below a single finite-free trivializing open, in every degree.
Module `Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal`. Source: original local
trivialization argument and the wedge-basis perfect pairing in Mathlib Basis.lean.
Both nodes record the actual searches in searches.jsonl. No change record is needed:
no existing statement, definition, or public import changed.


## Second reading by K1

1. **Unchanged interface — pass.** Read all three delivered modules and diffed
   DeterminantExteriorDualIso against the repository. Its sole existing declaration,
   `AlgebraicGeometry.exteriorSheaf_dual_iso`, retains its signature and docstring
   byte for byte. The three existing public imports remain unchanged. The new
   modules introduce only two named theorems, no definitions or modified objects.
   No change record is required.

2. **Proof and trust — pass as a decomposition.** Compiled the three files in import
   order with lcompile.py. The original theorem uses the existence lemma, unpacks
   `isFiniteLocallyFreeOfRank_iff_exists_over_iso_free`, applies the local lemma to
   every subopen, then uses the coversTop injectivity/surjectivity criteria,
   `Sheaf.isLocallyBijective_iff_isIso`, reflection and `asIso`. There are exactly
   two new `by sorry` bodies, in the reported named theorems; no forbidden
   declaration and no definition is added. An explicit scratch `#print axioms`
   check of all three declarations finds only propext, Classical.choice, Quot.sound
   and sorryAx, as expected from the open lower statements and exterior-sheaf API.
   The existential map is eliminated inside a proof of Nonempty; no arbitrary
   witness is used to define data.

3. **Split statements — pass.** Construction quantifies over every scheme, module
   and degree and only asserts a determinant-formula morphism; it asserts neither
   perfection nor an isomorphism. Local perfection takes a specified morphism and
   its formula, one actual rank-r trivialization, and a subopen inclusion; it has
   no global covering claim. Thus each is a strict part of the original argument.
   The formula is multilinear and alternating in each tuple, with restriction
   compatibility from naturality and preservation of determinants. The two
   sheafification universal properties produce the construction. On a free open,
   finite coordinate powers of the structure sheaf are sheaves; wedge coordinates
   identify the exterior sheaves, and internal Hom sections are determined by the
   finite basis. The determinant matrix on increasing basis wedges has diagonal
   1 and off-diagonal 0. Its functionals form the finite dual basis, proving local
   bijectivity. Checked n=0 (empty determinant 1), r=0 with n>0, n>r (empty wedge
   basis), n=1 (ordinary evaluation), zero rings and empty opens. No affine-open,
   nontrivial-ring or field hypothesis is used. Read Stacks Tag 0BRT online: it
   uses determinant inversion but leaves this general-degree argument implicit;
   read the installed Pairing.lean and Basis.lean and Dual/Basis.lean for the
   expanded argument. Independent LeanFinder query 'sheaf exterior power evaluation
   perfect pairing locally free internal hom' returned freeHomEquiv and freeMap
   tools, not either statement. Loogle homObj search had no recognized identifier;
   msearch grep and rg in lean/ and the upstream sheaf/module directories found no
   duplicate. These two sheafification/coordinate arguments cannot be closed by a
   few-minute application of the available ring pairing API.

4. **Route and pruning — pass after import cleanup.** Read the old proof plan,
   the ring pairing and free-basis nodes, and the sheafification interface node.
   The submitted proof follows the same determinant construction/local perfection
   route and retains the original item in its callers. The unit
   sk-thm-picard-duality has empty realized arrays in the repository; this delivery
   does not alter them or bypass a realized unit step. No shorter existing
   sheaf-level isomorphism was found. Removed redundant direct proof imports
   Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification and
   WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective: the unchanged
   public APIs already supply them. Recompiled the original module successfully.
   The No longer needed section now explicitly lists every old proof dependency
   absent from the new direct proof_deps, distinguishing their continued use below.
   No module leaves the transitive target closure.

5. **Nodes — pass after citation repair.** Checked the original node's new steps
   against the actual Lean assembly and its proof_deps union. Checked both new
   statements against their verbatim lean.statement fields, their sources,
   step/dependency unions, blueprint anchor, chapter/unit and created records.
   The construction and local node retain the original ring pairing/basis route.
   The installed Mathlib has no bijective_pairingDual despite the older search
   results. Corrected the new local theorem docstring and new-node proof metadata
   to the actual basis_coord/finite-dual-basis argument. The inherited original
   docstring stays unchanged, and its inaccurate citation is disclosed above.

Second-reading changes: removed two redundant proof imports, corrected the new
local lemma's unavailable Mathlib citation and the new nodes' proof metadata,
and completed the direct-dependency pruning report. No statement or definition
changed. One upper hole closed, two lower holes added: decomposition, net -1 before
any ledger pruning; no claim of a sorry-free proof.
