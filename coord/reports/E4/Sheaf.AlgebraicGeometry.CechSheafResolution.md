## What changed

Replaced the hole in `AlgebraicGeometry.exists_cech_sheaf_resolution` with a compiling
reduction following the source's construction, insertion contraction, and globalization.
Its signature, universes, visibility, and existing docstring remain unchanged.

Added proof-only imports of `Sheaf.AlgebraicGeometry.CechSheafConstruction`,
`Sheaf.AlgebraicGeometry.CechSheafLocalQuasiIso`, and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`. The last supplies the
already-proved `Scheme.Modules.preservesLimitsOfSize_restrictFunctor` instance.

The new construction theorem works for any family of opens, without a covering assumption,
and asserts no exactness. The new local theorem works for any augmented complex with the
specified section isomorphisms and differential/augmentation formulas; it proves only
quasi-isomorphism on a chosen family member, without a cover or a term-product hypothesis.
These are distinct, strictly smaller steps; neither restates the original resolution theorem.

The original module now proves globalization in two private helpers. `isIso_of_restrict`
uses local monomorphisms and the vanishing of the cokernel on the cover. Its dual condition
uses the restriction/direct-image adjunction to preserve cokernels.
`quasiIso_of_restrict` applies that result to the homology map in every degree. Exact
restriction and `ShortComplex.mapHomologyIso_inv_naturality` identify its local homology
maps with the maps on homology of the restricted complexes. The resolution theorem obtains
the constructed complex, applies the local theorem separately at each index, and invokes
this proved globalization argument.

Updated the original node's proof, proof dependencies, and proof origin to match this route.
Added two nodes for the remaining steps. No definitions or existing statements changed,
and no downstream adaptation is required.

All three delivered modules compile together, in import order, with no warnings using
`lcompile.py --all`. The import-direction check permits the existing source-library import.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_cech_sheaf_resolution`
(node `lem-pc-cech-sheaf-resolution`), by decomposition into two smaller statements.
The original module has no remaining `sorry`.

Added exactly two holes:

- `AlgebraicGeometry.exists_augmented_cech_sheaf_complex`, in
  `Sheaf.AlgebraicGeometry.CechSheafConstruction`, node `lem-pc-cech-sheaf-construction`.
- `AlgebraicGeometry.augmented_cech_sheaf_quasiIso_restrict`, in
  `Sheaf.AlgebraicGeometry.CechSheafLocalQuasiIso`,
  node `lem-pc-cech-sheaf-local-quasi-iso`.

Both have named public statements, standalone modules, source citations, and complete
proofs in words. The private globalization helpers are completely proved. This is a
one-to-two decomposition, with net hole change +1, not an axiom-free completion of the
resolution theorem. Its proof still depends transitively on those two holes.

## No longer needed

None. The original module had no proof-dependency imports and its node had no proof
dependencies to prune. All three original public imports are needed by the unchanged
statement. Every added proof import is used. No node or module is claimed to leave the
target closure.

## Where the brief, the DAG or earlier work was wrong

The original node labelled the construction and local exactness as elementary and gave
neither a supporting declaration nor a proof dependency. They comprise substantial
module-sheaf construction/comparison and contracting-homotopy arguments. This delivery
makes them independently claimable while proving their local-to-global combination.

The source was read in the locally available blueprint copy under `work-bp/sheaf`:
`sec-picard-framework/sk-thm-picard-semicon/lem-pc-cech-resolution.md`, displayed complex
and first proof paragraph. The repository's literature directory lacks that file. The
source displays the ordered alternating complex; the existing item's full unnormalized
complex with repeated indices is preserved, and its insertion argument applies directly.
No bounded-above claim, affine hypothesis, or finiteness hypothesis has been introduced.
The unit record `sk-thm-picard-semicon` has empty realized statement/step lists; the
source's construction, local contraction, and local-to-global route is retained.

A detail checked while writing the local statement: the given `e` is an isomorphism of
presheaves of global modules, so it need not respect all local structure-sheaf scalars.
The new local proof therefore transports the insertion homotopy only on underlying
abelian sheaves and then reflects exactness in module sheaves. It does not assert a
module-linear homotopy after an arbitrary such `e`.

Edge cases checked: an empty index type gives empty product terms in the construction;
an empty cover can cover only the empty scheme, and the globalization proof works
vacuously through vanishing on that cover. A chosen empty cover member has zero sheaves
on its open subscheme, the zero module satisfies the same identities, and repeated
indices are retained. Infinite index sets cause no stalk/product interchange: the
contraction is natural on sections over opens contained in the chosen member.

Mathlib searches: LeanSearch returned an Internal Server Error; LeanFinder and Loogle
found the Čech functor and unrelated quasi-isomorphism lemmas. Text searches of Mathlib,
`lean/WeilConjectures`, `lean/Sheaf`, and the DAG found no suitable existing statement
for either new intermediate. Mathlib's `FormalCoproduct.extraDegeneracyCech` is useful
in constructing an insertion contraction, but does not supply the comparison with the
specified module-sheaf augmentation. The source library's proved restriction-limit
instance was found and used rather than copied into the delivery.

## New nodes

`lem-pc-cech-sheaf-construction` states construction and all section/term comparisons for
an arbitrary family of opens, without exactness or a covering hypothesis. Its module is
`Sheaf.AlgebraicGeometry.CechSheafConstruction`; its source is the original blueprint's
displayed complex and first proof paragraph. The node records the functorial open direct
image construction, product comparisons, and augmentation construction.

`lem-pc-cech-sheaf-local-quasi-iso` states exactness only after restriction to one chosen
member, for an already given complex and its section/differential/augmentation formulas.
Its module is `Sheaf.AlgebraicGeometry.CechSheafLocalQuasiIso`; its source is the insertion
homotopy in the first proof paragraph. The node records the insertion/deletion cancellation
on abelian sheaves and reflection of exactness to module sheaves. Both nodes record all
three required kinds of searches. No change record is needed.

## Second reading by E4

1. **Visible interface: pass.** Read all three modules and diffed the existing
   `CechSheafResolution` against the repository. Its theorem signature, universes,
   visibility, and docstring are byte-for-byte unchanged. The only existing-file
   additions are three plain proof imports and two private proved helpers. There
   are no definition changes or forced adaptations. The two other modules are new.

2. **Proof and axioms: pass as a decomposition.** Independently compiled the three
   modules with `lcompile.py --all`: no errors or warnings (2.8, 2.7, and 3.8 seconds).
   A scratch copy with `#print axioms` confirms that both private globalization
   helpers use only `propext`, `Classical.choice`, and `Quot.sound`. The resolution
   and the two named open statements additionally use `sorryAx`, as reported.
   Scanned all delivered Lean: exactly the two listed named theorem holes, no
   forbidden declarations or attributes, and no definitions containing holes.
   The construction existential is eliminated in a proposition, not used to choose
   arbitrary data in a definition. In the first helper, restriction preserves
   cokernels and local vanishing kills the global cokernel; together with local
   monomorphism this gives invertibility. In the second, homology-comparison
   naturality and invertible comparison maps give the required local homology maps.

3. **Split statements: pass.** Read both node statements, Lean signatures, and
   docstring arguments. Construction has no cover hypothesis and no quasi-isomorphism
   conclusion; local exactness takes an existing augmented complex and claims only
   exactness on a specified member. Neither merely renames the original theorem.
   For construction, empty index sets give zero product terms and the zero
   augmentation. For local exactness, empty index sets have no chosen member;
   empty chosen opens and the zero module give zero sheaves. Repeated indices are
   handled by insertion/deletion cancellation, with no finite-cover assumption or
   infinite-product/stalk interchange. In degrees zero and one the identities are
   respectively the restriction/projection left inverse and cancellation of the
   two faces besides the inserted-index face. The arbitrary presheaf comparison
   need not preserve local scalars: its underlying additive comparison suffices,
   since forgetting module sheaves preserves and reflects exactness. Independent
   LeanFinder search for contractibility when a cover contains the entire space
   returned extra degeneracies and unrelated contractible spaces; Loogle returned
   only `cechComplexFunctor`. The independent logged grep and source searches found
   no matching module-sheaf construction or local augmentation theorem. Read the
   upstream Cech module, Mathlib's Cech functor, the existing alternating-restriction
   homotopy, and the restriction-limit instance: none closes these two statements
   in a few minutes. The alternating-restriction theorem compares ordered and full
   complexes and does not assert exactness of the augmentation.

4. **Route and pruning: pass.** Read the displayed complex and first proof paragraph
   of `lem-pc-cech-resolution.md` in
   `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/`.
   Its construction, insertion contraction, and local-to-global exactness route is
   retained, using the existing item's full complex with repeated indices. No affine,
   separatedness, or finiteness hypothesis is needed for these steps; those belong
   to the source's later acyclicity argument. Read the unit record
   `sk-thm-picard-semicon`: its realized statement and step lists are empty, and
   this delivery bypasses no realized unit node. All public imports supply signature
   data, and the three new imports are proof-only and used. The old node has empty
   `proof_deps`, so `No longer needed: None` is complete.

5. **DAG agreement: pass after metadata repair.** The resolution's three proof steps
   match the two new lemmas followed by the fully proved globalization helpers.
   Its `proof_deps` are exactly the two new nodes, and its proof origin records the
   source and formal reduction. Both new nodes have matching verbatim Lean signatures,
   sources, proof descriptions, creation records, blueprint ancestry, searches, and
   the item's chapter and unit. The existing resolution node had its unchanged Lean
   signature stored on one flattened line; replaced only `lean.statement` with the
   exact multiline declaration text to satisfy the verbatim-record requirement.

Second reading changed only that node metadata and this report. No Lean repair was
necessary. One original hole is closed by decomposition and two smaller holes remain;
this is net +1 holes, not an axiom-free proof of the resolution.
