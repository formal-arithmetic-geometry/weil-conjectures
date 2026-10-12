## What changed

Corrected AlgebraicGeometry.grothendieckExistenceEasy to retain Stacks 0889's
ideal-power-torsion condition on the actual coherent map a, both in the resulting
triple and in every comparison triple. The old Lean statement is false, while the
DAG's natural-language statement was already correct. No target or definition changes.
The change record is coord/changes/grothendieckExistenceEasy-torsion.md.

Part (1) now uses the existing AlgebraicGeometry.grothendieckExistenceEasy_torsionTriple
from C1's concurrent landing. Part (2) is reduced to two strictly smaller statements:
outgoing existence without uniqueness, and unique descent of arbitrary compatible
Hom maps without algebraization existence. The parent proof lifts a formal comparison
and its inverse, proves both inverse identities using unique Hom descent, forms the
isomorphism, verifies its two equations, and proves its uniqueness. The DAG follows
these actual dependencies. Each new statement has a complete proof in words and a node.

## Proved and sorry left

The original module had one hole, AlgebraicGeometry.grothendieckExistenceEasy. Its
corrected, source-faithful statement now has a complete Lean proof from named
statements; no direct sorry remains in the item. The old false signature is not
claimed proved. This is a decomposition, not a sorry-free proof from Mathlib.

Two new holes remain, each exactly the whole proof of a public theorem:

- AlgebraicGeometry.grothendieckExistenceEasy_exists_from —
  lem-weil-pbc-grothendieck-existence-easy-from-exists, in
  Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists.
- AlgebraicGeometry.completion_isogeny_from_hom_lift —
  lem-weil-pbc-completion-isogeny-from-hom-lift, in
  Sheaf.AlgebraicGeometry.CompletionIsogenyFromHomLift.

The existing imported theorem AlgebraicGeometry.grothendieckExistenceEasy_torsionTriple
also still has its pre-existing sorry, node lem-weil-pbc-easy-algebraization-torsion-triple;
this delivery does not add or alter that hole. One direct hole is replaced by two new
holes: do not count this as a net reduction. On the current base C1's devissage landing
has already removed this item from the target import closure, so no improvement to
that closure is claimed. Both new intermediate modules compile through lcompile.py. The earlier complete
assembly in both orientations also compiled, before the concurrent C1 theorem was
reused. The first worker could not validate the narrowed item because the imported C1
theorem had no compiled olean then. At second reading the shared olean is present;
the main module and both new modules compile. The unchanged C1 source copy was
removed from the sandbox, so this delivery uses the shared compiled dependency.
The earlier tool failure below is historical and resolved at second reading.

## No longer needed

The item's direct imports removed are:

- Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated
- Sheaf.AlgebraicGeometry.Coherent
- Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
- Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
- Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness
- Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
- Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
- Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
- Sheaf.RingTheory.FiniteIffFormalGlueing
- Sheaf.RingTheory.FormalGlueingComplexExact
- Sheaf.RingTheory.FormalGlueingIsogeny
- Sheaf.Topology.GlueSheavesOfModules
- WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

These dependencies are relocated under the existing first-direction theorem or the
new existence/Hom statements where their arguments need them; they are not globally
pruned. Sheaf.AlgebraicGeometry.Coherent is already a public dependency of the retained
CoherentFormalModule import, so its separate import was redundant. No whole-library
module is claimed pruned. The new Hom lemma only states the under-G orientation;
the unneeded over-G clause and the duplicate first-direction existence were dropped
once C1's existing declaration became available. No unit statement or realized step
was bypassed: sk-thm-p1 and its realized nodes are unchanged.


All old direct proof dependencies removed from the parent node (these remain
statement dependencies or occur below its new proof dependencies where needed;
no global pruning is claimed):

- lem-weil-pbc-coherent-formal-modules-local-exactness
- def-weil-pbc-coherent-formal-module
- lem-weil-pbc-formal-systems-annihilated-by-power
- lem-weil-pbc-ideal-times-quasi-coherent-affine-sections
- def-weil-pbc-noetherian-ring
- def-weil-pbc-adic-completion
- lem-weil-pbc-affine-tilde-gamma-adjunction
- pqf-lem-coherent-ft-locnoeth
- lem-weil-pbc-quasi-coherent-finite-type-affine
- lem-weil-pbc-quasi-coherent-module-kernel
- lem-weil-pbc-quasi-coherent-module-cokernel-image
- lem-weil-pbc-coherent-formal-modules-affine
- lem-weil-pbc-completion-finite-module-tensor
- lem-weil-pbc-noetherian-completion-flat
- lem-weil-pbc-adic-completion-mod-ideal
- lem-weil-pbc-formal-glueing-isogeny
- lem-weil-pbc-formal-glueing-complex-exact
- lem-weil-pbc-formal-glueing-finite-modules
- def-weil-pbc-module-localization-away
- def-weil-finitely-generated-module
- def-weil-module-base-change
- pqf-def-locnoeth
- def-weil-affine-spectrum
- lem-weil-pbc-principal-localization-open-immersion
- lem-weil-pbc-localization-noetherian
- lem-weil-pbc-glue-sheaves-of-modules
- pqf-def-coherent

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old Lean signature omitted the torsion condition on a and a'.
For X = Spec k, k a nonzero field, and I = O_X, all completions are zero. With G=0
and F=0, the old comparison clause would make every coherent H (with its zero map)
isomorphic to the chosen one, in particular identifying 0 with O_X. The same defect
occurs in the other orientation. Stacks 0889(1)(b) and (2)(b), read in the local copy
/home/ubuntu/work-bp/sheaf/literature/stacks-project/coherent.tex, lines 6487–6550,
explicitly impose the missing condition. The online source at
https://stacks.math.columbia.edu/tag/0889 was checked too. The source and natural-language
DAG statement are correct; this was a stage-2 encoding omission. It is restored in
this delivery with the required change record. No weakening of the source is made.

C1 independently repaired its use by introducing the torsion-triple statement. That
landing arrived during this session, and I reused it instead of restating its clause.
The brief's claim that this module is still reached from the targets was true at the
start and is false on the new base: downstream.py now reports zero importers.
No forced adaptation is required, and no other group's module is changed.

The two new statements were checked at I=0 (completion is the identity), I=O_X
(the ordinary isogenies must be isomorphisms), zero modules, and the empty scheme.
The existence proof uses a positive maximum on a finite cover, choosing one on the
empty scheme. Hom descent glues on affine refinements of overlaps and does not assume
those overlaps are affine. The Hom morphism need not be invertible; its inverse in
the parent is constructed by lifting the inverse formal comparison separately.
LeanFinder and Mathlib grep found only ring-level completion material. LeanSearch
returned Internal Server Error and is honestly recorded as unavailable. Searches of
the blueprint and existing library found no other needed second-direction statement.

Historical first-worker failure (resolved at second reading): the dry run was
BLOCKED by a launcher/repository tool mismatch. Command:

```text
python3 /home/ubuntu/weil-launcher/deliver3.py P1 Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy --no-push
```

It fails in check_import_sources, before its compile and preflight:

```text
ImportError: cannot import name 'refuse_missing' from 'import_cycles'
```

The launcher imports this name from
/home/ubuntu/weil-conjectures-sheaf-P1/tools/import_cycles.py, which does not define it.
No script was edited and no workaround was attempted, in accordance with AGENTS.md §3
and §6. Nothing was pushed. The narrowed main module also currently fails import
resolution because the compiled GrothendieckExistenceEasyTorsionTriple.olean has not
arrived in the last-green cache, although its node records a landed review. The
project's wait-for-green rule was followed; the dependency was not restated or copied.
The two new modules compile, but this is not a validated READY delivery.

A source-only DAG closure check also found pre-existing cycles in the sheaf-algebraic-
structures and derived-functor branches, and an existing dependency reference
`def-weil-pbc-ideal-module-product-stalk` with no node of that id. Those lie below
unchanged existing dependencies and were not introduced or altered here. They are
reported for the maintainer, not silently repaired in another worker's files.

## New nodes

lem-weil-pbc-grothendieck-existence-easy-from-exists isolates the existence and descent
part of 0889(2), from its affine dictionary, formal gluing 0ALK(2), finiteness 05EU,
and unique local Hom lifting. It asserts no uniqueness of triples and cannot by
itself prove the parent's second clause.

lem-weil-pbc-completion-isogeny-from-hom-lift isolates descent and uniqueness of
compatible Hom maps under a fixed coherent G, using the exact gluing complex 05EK
and gluing of sheaf maps 04TN. It assumes both coherent modules already exist and
does not algebraize a formal object. It supplies arbitrary morphisms; the categorical
argument forming the isomorphism and proving its uniqueness is actual Lean in the
item. The two new nodes inherit the chapter, unit and nearest blueprint ancestor.
The change record is coord/changes/grothendieckExistenceEasy-torsion.md.

## Second reading by P1

1. Interface comparison: PASS with the declared correction, not a proof-only change.
   Diffed the parent against the repository. The only signature edits are the four
   torsion clauses in grothendieckExistenceEasy-torsion.md (produced and comparison
   triples in both orientations). Its Old and New signatures agree with the source
   files. Stacks coherent.tex, Lemma 0889, explicitly requires these clauses; the
   unit-ideal counterexample to the old signature is valid. No definition or target
   changes. The C1 torsion-triple source was byte-identical to the repository and
   has been removed from this delivery. All other delivered declarations are new.

2. Proof and axioms: PASS as a decomposition. Compiled the three delivered modules
   in import order using lcompile.py, including the parent against the shared C1
   olean, with no errors or warnings. Scratch copies with #print axioms for each
   declaration show only propext, Classical.choice, Quot.sound, and sorryAx.
   The only direct holes delivered are the two public named theorems listed above;
   no definition, axiom, unsafe, opaque, implemented_by, or extern was added.
   Read the parent's composition orders, both inverse identities, cancellation
   of beta', and Iso.ext uniqueness argument: they match the corrected statement.

3. New statements: PASS. Both have source citations, detailed docstring proofs,
   and matching nodes. Rechecked I=0 (identity completion), I=O_X (ordinary maps
   are isomorphisms), zero modules, and the empty scheme. Hom descent is justified
   by the injective exact formal-gluing complex: localized isogenies determine
   the punctured maps, and the formal equation supplies compatibility. Existence
   is the opposite-direction clause of 0ALK plus finiteness and local gluing;
   the finite-cover maximum supplies the uniform positive exponent. Overlaps
   are covered by affines, not assumed affine. Existence omits uniqueness and Hom
   descent assumes the algebraic objects already exist, so neither merely restates
   the parent. Fresh LeanFinder searches for gluing from completion/localizations
   and algebraization of a completed coherent map, plus Mathlib grep for formal
   descent/lifting and repository searches for compatible Hom lifts, found no
   replacement. Hits were localization lifting or ring-level completion, not
   these statements; proper completion full faithfulness needs properness absent
   here. Neither hole can be closed by a short application of the existing API.

4. Route and pruning: PASS after report repair. The parent retains exactly its
   statement import and three proof imports; the new modules keep the imports of
   their documented proof plans, all proof-only. Completed the list of every old
   proof_deps removed from the parent, distinguishing relocation from global
   pruning. No globally pruned module is claimed. Read sk-thm-p1.json, including
   realized: no unit statement or realized step is replaced or bypassed.

5. Nodes: PASS. Each Lean signature matches lean.statement verbatim; each node's
   proof_deps is exactly the union of its proof-step uses. All direct references
   exist. The parent route matches its compiled assembly, and both new proof
   plans match their docstrings. New nodes have the required source, creation,
   search, blueprint, chapter, unit, and Lean fields. Existing natural-language
   statement and statement dependencies are unchanged; the correction is confined
   to its Lean encoding and is documented by the change record.

Second-reading changes: removed the unchanged C1 module and its local artifacts,
removed the obsolete STATEMENT-DISPUTED marker from the repaired Lean statement,
completed the old-dependency inventory, updated validation status, and added this
review. No mathematical proof was rewritten and neither split-off hole was closed.
The earlier ImportError and missing shared olean are resolved. Delivery remains a
statement correction and decomposition, with no net reduction claimed.
