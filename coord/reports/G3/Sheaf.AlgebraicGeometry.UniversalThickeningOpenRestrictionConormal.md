## What changed

Proved `AlgebraicGeometry.universalFirstOrderThickening_open_restriction_conormal`
with its signature unchanged. The formal-unramified witness follows from Mathlib's
composition property and `FormallyUnramified.of_comp`. The restricted universal
thickening witness is already supplied by `hdata`. The conormal comparison is an
explicit composition of the open restriction/tensor pullback comparison, two
pullback composition isomorphisms, transport through the given square equality,
and pullback of the kernel ideal comparison.

Added the fully proved module `Sheaf.AlgebraicGeometry.OpenRestrictionKernelModule`
and declaration `AlgebraicGeometry.nonempty_tensorPullback_open_kernel`. It applies
to any closed immersion and its open restriction: no universality, formal
unramifiedness, or square-zero assumption is involved. The proof constructs a
kernel lift from the restricted ideal inclusion and proves that lift bijective
on every open. The existing private range theorem in FormallyUnramifiedConormal is reused
through a proof-only `import all`; the remaining proved private helper transports
zero equations through the open square. The comparison with tensor
pullback comes from uniqueness of left adjoints. No definitions or existing
interfaces changed. Updated the item's proof, proof dependencies, and proof origin.

Read Mathlib's open section and restriction APIs, the source library's ideal-module
kernel construction, and Stacks Tags 00A0, 09ZU and 01R2 on the official website.
LeanSearch returned Internal Server Error; LeanFinder and Loogle succeeded.
The existing invertible-ideal pullback result is inapplicable because the kernel
ideal need not be invertible. No shorter existing module comparison was found.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.universalFirstOrderThickening_open_restriction_conormal`
(node `lem-weil-pbc-universal-thickening-open-restriction-conormal`).

Also proved the new declaration
`AlgebraicGeometry.nonempty_tensorPullback_open_kernel`
(node `lem-weil-pbc-open-restriction-kernel-module`), including the private
`AlgebraicGeometry.open_kernel_zero_iff` helper. The range theorem is imported,
not newly proved.
There are no direct `sorry`s in either delivered module. Holes closed: 1; holes
added: 0. This is a proof, not a decomposition with postponed kernel theory.
Existing imported dependencies retain their own proofs and any transitive holes;
this report does not claim the whole target import closure is axiom-free.

Both modules compiled cleanly with lcompile.py, in dependency order. The proof
checks every open, including the empty open. The whole ambient open reduces to
the same kernel module; an isomorphic closed immersion gives the zero kernel.
No finite type, affineness, or nonemptiness hypothesis was introduced.

## No longer needed

Current second reading: removed the redundant proof-only import
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` from the new kernel module.
It is already publicly supplied by the required `import all` of
`FormallyUnramifiedConormal`. The adjunction node and theorem remain used.

Repair: removed the duplicate private `AlgebraicGeometry.range_kernelIdeal`
declaration from `Sheaf.AlgebraicGeometry.OpenRestrictionKernelModule`. All five
uses now refer to the existing theorem in
`Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal` via `import all`. No existing
library module is adapted and no new postponed theorem is introduced.

Removed the proof import `Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestrictionCore`:
its existence result is unnecessary when the actual restriction data is already
supplied. Its node `lem-weil-pbc-universal-thickening-open-restriction-core` is not
used by this theorem; other consumers may still require it.

Removed the direct import `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists`
and the item's proof dependency
`lem-weil-pbc-universal-first-order-thickening-exists`: no new universal thickening
is chosen and no independence theorem is used. That module remains publicly
reachable through `FormallyUnramifiedConormal`; this is removal of a redundant
local import and proof dependency, not a claim of global unreachability.

Removed the redundant direct import `Sheaf.AlgebraicGeometry.TensorPullback`:
its composition declarations are publicly available through the conormal and new
kernel comparison modules. The node `def-pc-module-pullback` remains a proof
dependency and its module remains needed.

Removed `lem-weil-pbc-thickening-open-restriction` from the item's proof dependency
list. No restricted square-zero calculation is needed: `hdata` already contains
`HV`. The kernel module restriction is now proved directly in the new module,
rather than relying on this node's ideal-data Mathlib match to supply a module
isomorphism. No blueprint unit statement or step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the existing private range theorem. The earlier
second reading below incorrectly concluded that private visibility prevented
reuse. Lean supports `import all`, which makes the existing private theorem
available to this proof without changing any library declaration or visibility.
The duplicate declaration and its proof have been removed; the helper module
compiled successfully with all range uses resolving to the imported theorem.
The kernel node now records this reuse and its conormal-module dependency.
The earlier second reading is retained as historical review of the returned
version; its statements about two newly proved helpers are superseded by this
repair and require the next reader's confirmation.

The old plan said the existence theorem supplies formal-unramifiedness and `HV`.
Its Lean statement assumes formal unramifiedness and cannot supply that witness;
`HV` is already an input. Mathlib's composition and cancellation results supply
the formal-unramifiedness witness directly.

The old thickening restriction match describes ideals on affine opens; it does
not state an isomorphism of the kernel modules built from subscheme maps. The
new lemma proves that bridge, with explicit injectivity and surjectivity on all
opens, before using tensor pullback composition.

`blueprint_refs.py ancestor` reports None for the item because its earlier
`created.item` is a module name rather than a DAG node id. The new node follows
the established ancestry on the parent restriction node, through
`thm-weil-pbc-finite-etale-lifting`, with the intervening node ids recorded in
`blueprint.from.via`. The existing item's unrelated metadata is unchanged.

## New nodes

`lem-weil-pbc-open-restriction-kernel-module`, in
`dag/nodes/sec-proper-base-change/`, records the fully proved theorem
`AlgebraicGeometry.nonempty_tensorPullback_open_kernel` of
`Sheaf.AlgebraicGeometry.OpenRestrictionKernelModule`. Its statement compares
only ambient kernel ideal modules, strictly below the conormal pullbacks in the
item. It records actual search results (including the unavailable LeanSearch),
the kernel construction and componentwise proof, and the Stacks sources.
Blueprint searches for kernel ideal restriction, ideal sheaf, and restriction
found no exact blueprint duplicate. No change record is necessary: there are
no changes to existing statements, definitions, visibility, or instances.

## Earlier second reading (a previous round; superseded)

1. Interface verdict: PASS. Diffed the entire original module against the
   repository. Its universe, declaration name, all arguments (including `hform`
   and every conjunct of `hdata`), existential witnesses and module-isomorphism
   conclusion are byte-for-byte unchanged. Only proof imports and the proof body
   changed. There are no changed definitions, instances or existing visibility.
   The kernel comparison is a new theorem, not a replacement for an old statement.

2. Proof verdict: PASS. Independently compiled both modules in dependency order
   with `lcompile.py --all`, then compiled scratch copies with `#print axioms` for
   the original theorem, the new theorem and both private helpers. All four use
   exactly `propext`, `Classical.choice`, `Quot.sound`; none uses `sorryAx`.
   Neither module contains a `sorry`, axiom, unsafe/opaque declaration, external
   implementation, or a new data definition. The adjunctions chosen in proofs
   supply isomorphisms by uniqueness of left adjoints; no arbitrary object is
   defined from an unproved existence assertion.

3. New-statement verdict: PASS. There are no postponed statements. Read the
   complete new kernel theorem and its node against Stacks 00A0 (restriction on
   opens, including modules), 09ZU (base change of thickenings), and 01R2 with
   its preceding kernel-ideal description; read 04FA for the original conormal
   clause. These sources were opened on the official Stacks website because
   the literature .tex files are absent on this machine. The new lemma only
   assumes closed immersions, the full preimage equality and the commuting
   square. It does not use square-zero or universal properties. In its proof,
   `hpre` ensures that source sections are restricted inside V; `hcomm` transports
   the section maps. The kernel lift is injective by the two injective section
   maps and surjective by lifting through their computed ranges. Empty opens,
   the whole open, and an isomorphic closed immersion (zero kernel) introduce
   no exception; no affine-open or nonempty-open assumption occurs.
   Independently searched LeanFinder for "ideal sheaf module inverse image under
   open immersion is kernel of restricted closed immersion", and msearch grep
   for `ker_morphismRestrict|toModules.*restrict|restrict.*toModules`. The hits
   are ideal-data statements, not this module isomorphism. Also searched project
   Lean and upstream ideal-sheaf/module sources. No usable duplicate was found.
   The identical range calculation in FormallyUnramifiedConormal is private and
   cannot be reused across modules.

4. Route/pruning verdict: PASS, with one import repair. Checked the proof from
   its top: formal unramifiedness uses Mathlib composition and `of_comp`; HV is
   the input witness. The remaining chain is open restriction, tensor pullback
   composition, equality transport and the proved kernel comparison. The new
   comparison is strictly below the conormal argument and is fully proved.
   The report accounts for every removed original proof dependency, notably
   thickening-open-restriction and universal-first-order-thickening-exists;
   the three retained original dependencies are still used. Read the unit
   `dag/units/sk-thm-p1.json` and its `realized` lists: neither this item nor a
   pruned dependency realizes a unit statement or step. The curve calculations,
   strictly henselian comparison and geometric-stalk route remain intact.
   Replaced the new module's public adjunction import by public TensorPullback
   plus a plain adjunction import: only the proof needs the adjunction theorem.
   The original module's public FormallyUnramifiedConormal import remains needed
   by its signature. Its old docstring incorrectly attributes the supplied HV
   and formal-unramified witness to independence; this pre-existing prose fault
   is recorded here, without changing the existing docstring or interface.

5. Node verdict: PASS. Diffed the existing node: only `proof`, `proof_deps` and
   `proof_origin` changed. The three steps describe the actual factorization,
   closed-immersion kernel restriction and five-isomorphism conormal chain.
   Read each cited definition/Mathlib leaf and checked its use, including the
   tensor composition declarations supplied by TensorPullback and the open
   restriction adjunction. The new node has its source, explicit kernel-lift
   proof, exact Lean signature, statement dependencies, matching proof-dependency
   union, search records, creation record and blueprint ancestry. Its theorem
   does not merely rename the item's conormal conclusion. The new node's Lean
   signature matches the file verbatim. No change record is needed.

Second reading changed only the import visibility in
`Sheaf.AlgebraicGeometry.OpenRestrictionKernelModule` and this report. No proof
or mathematical statement required repair. Holes closed remain 1; holes added
remain 0; split-off holes remain 0.


## Second reading by G3

1. Interface: PASS. Read the complete original and delivered item and their diff.
   The original theorem signature, universe, arguments, visibility, and docstring
   are byte for byte unchanged. The original node changes only `proof`,
   `proof_deps`, and `proof_origin`. There are no existing definition or statement
   changes, forced adaptations, or change records.

2. Proof: PASS. Independently compiled both delivered modules in import order
   through `lcompile.py --all`, including after removing the redundant import.
   Compiled scratch copies with `#print axioms` for the original theorem,
   `nonempty_tensorPullback_open_kernel`, `open_kernel_zero_iff`, and the imported
   `range_kernelIdeal`: each uses exactly `propext`, `Classical.choice`,
   `Quot.sound`, and no `sorryAx`. Read all proof bodies and checked that neither
   delivered module contains any `sorry`, forbidden declaration, or new data
   definition. The repaired `import all` resolves the existing private range
   theorem without duplicating it. Adjunction choices occur in proofs, where
   uniqueness of left adjoints supplies the comparison isomorphisms.

3. New statements: PASS. No statements remain split off with `sorry`. The new
   proved kernel comparison is strictly below the original conormal argument and
   does not restate it. Its sectionwise proof transports zero equations across
   the commuting open square, factors the restricted inclusion through a kernel,
   and checks injectivity and surjectivity on every open. Checked the empty open,
   the whole ambient open, and the identity closed immersion (zero ideal); no
   nonemptiness, affineness, square-zero, or universality hypothesis is needed.
   Independently searched LeanFinder with "Restriction of a closed subscheme
   ideal module to an open subscheme equals the ideal module of the inverse image
   subscheme", and searched project and Mathlib ideal-sheaf sources with `rg`.
   The results concern affine ideal data, not this module isomorphism. Read the
   existing private range theorem and confirmed its exact reuse. Sources checked:
   [00A0](https://stacks.math.columbia.edu/tag/00A0),
   [09ZU](https://stacks.math.columbia.edu/tag/09ZU),
   [01R2](https://stacks.math.columbia.edu/tag/01R2), and
   [04FA](https://stacks.math.columbia.edu/tag/04FA).

4. Route and pruning: PASS. Read the argument from the item down to the kernel
   comparison. Mathlib composition and `FormallyUnramified.of_comp` provide the
   formal-unramified witness; `HV` is supplied by `hdata`; the remaining argument
   composes the restriction comparison, tensor composition, square equality,
   and pulled-back kernel comparison. No shorter existing kernel comparison was
   found. Every removed original proof dependency is accounted for under
   `No longer needed`; the remaining three original dependencies are used.
   Read `dag/units/sk-thm-p1.json`: neither the item nor its pruned dependencies
   realizes a unit statement or step, and the unit route is preserved. Removed
   one redundant proof-only adjunction import; all signature imports remain
   public and all imports added only for proofs remain nonpublic.

5. Nodes: PASS. Checked both node files against the actual proofs and declarations.
   Each `proof_deps` is exactly the union of step `uses`. The new node has its
   source, complete proof, searches, creation record, blueprint ancestry, chapter,
   unit, and exact multiline Lean signature. All dependencies resolve to existing
   library declarations or recorded Mathlib leaves. The new proof explicitly
   records reuse of `range_kernelIdeal` through the conormal module; the previous
   reader's claim that it could not be reused is superseded. No new node is needed
   for a postponed statement because none is postponed.

This second reading changed only the redundant proof-only adjunction import in
`OpenRestrictionKernelModule` and this report. No proof body, statement,
definition, or node required repair. Holes closed: 1 of 1 original holes; holes
added: 0; split-off holes: 0. The new kernel theorem and its private zero-equation
helper are fully proved.
