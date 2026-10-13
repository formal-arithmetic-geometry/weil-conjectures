## What changed

Completed the earlier sandbox reduction of
`Sheaf.AlgebraicGeometry.FiniteAffineCechSectionBaseChange` and supplied its missing
DAG records and report. The signature and docstring of
`AlgebraicGeometry.Scheme.Modules.finiteAffineCech_section_baseChange` are unchanged.
The proof obtains natural, locally linear ordered section coordinates; obtains a
module-sheaf homotopy equivalence from those coordinates and the given usual Čech
presentation; then composes `HomotopyEquiv.toHomologyIso` with
`HomologicalComplex.extendHomologyIso` at the natural degree. The model's
`IsStrictlyGE 0` property is proved from the existing `finiteAffineCechModel_ge` and
preservation under additive pullback.

The two missing parts have separate new modules, each containing one public theorem
with exactly `:= by sorry`, a source, and a complete natural-language proof. They
separate termwise affine geometry from the purely Čech combinatorial comparison.
The first does not mention D or homology. The second does not mention f, U, V,
quasi-coherence, affineness, separatedness, a cartesian square, or the specified model.
Neither is the original statement renamed or repackaged. No data definition is added.

Read the existing model, affine-intersection base-change, affine-pullback sections,
ordered restriction homotopy, and linear Čech resolution interfaces. Searches in the
source library, Mathlib, and the imported blueprint found no replacement giving the
needed local module compatibility. LeanSearch was unavailable (HTTP 500), recorded
as unavailable. Loogle, LeanFinder and source grep were run. The sorting formulas were
checked against Stacks Tags 01FK and 01FM; the termwise calculation against Tag 02KE,
Lemma 30.5.1 and the complex calculation in the proof of Lemma 30.5.2.

Compilation: all three sandbox modules compile in dependency order through
`lcompile.py --all`. The main proof is complete relative to the two named holes.
The final `deliver3.py --no-push` dry run is the delivery gate. The second reader is authorized to push after a successful dry run.

Edge cases checked mathematically: r = 0 and p + 1 > r give empty increasing-tuple
products; empty coefficient intersections have zero sections; negative terms are
zero. Repeated indices in usual Čech cochains are contracted by the sorting homotopies.
No covering, augmentation, acyclicity, flatness, or tensor-homology exchange is used.
For a nonaffine new base, the termwise maps are constructed on its affine basis and
glued, including their inverses, by the pure-tensor restriction identities. The unit's
finite affine Čech/base-change route is retained.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.finiteAffineCech_section_baseChange`
(node `lem-pc-finite-affine-cech-section-base-change`).

Added two strictly intermediate holes:

- `AlgebraicGeometry.Scheme.Modules.finiteAffineCech_baseChange_coordinates`
  (node `lem-pc-finite-affine-cech-base-change-coordinates`, module
  `Sheaf.AlgebraicGeometry.FiniteAffineCechBaseChangeCoordinates`).
- `AlgebraicGeometry.Scheme.Modules.orderedCech_module_comparison`
  (node `lem-pc-ordered-cech-module-comparison`, module
  `Sheaf.AlgebraicGeometry.OrderedCechModuleComparison`).

There are no other sorries in the delivered files. This is a decomposition:
one upper hole closed, two lower holes added, net -1 in this delivery's direct hole
count. It is not a proof independent of sorry. Existing dependencies' holes are
untouched. The coordinates are consumed within a theorem proof, not used to define
an arbitrary object.

## No longer needed

Removed the main module's ordinary proof import
`Sheaf.AlgebraicGeometry.AlternatingCechComputes` and its direct proof dependency
`lem-pc-alternating-cech-computes`: its theorem concerns abelian-group cochains,
whereas the new comparison records local module actions and homotopies of module
sheaves. The new comparison is proved by the explicit sorting formulas of the same
source, rather than assuming naturality or local linearity of an arbitrary homotopy
witness from the abelian-group result. It imports neither AlternatingCechComputes nor
AlternatingCechRestrictionHomotopy.

Removed the main module's ordinary imports of
`Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange` and
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`; both are retained as ordinary
proof imports and proof dependencies of the new coordinates item. Their nodes
`lem-pc-finite-affine-cech-intersection-base-change` and
`lem-weil-pbc-module-pullback-affine-sections` are still needed below that item and
are not globally pruned.

The parent no longer directly uses `lem-pc-linear-cech-sheaf-resolution`: the given
D, e, hd and hlinear suffice, and no augmented resolution is constructed here.
The module-sheaf and alternating-complex definition nodes remain needed in the new
items' statement/proof closures. Public statement imports of the existing module
are preserved. No claim is made that another target path stops using any named node.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's Lean reduction compiled but had no new node records or report.
Those omissions are repaired here. The existing DAG's final affine-local homology
and gluing step can be simplified: assemble termwise module maps and explicit sorting
homotopies first, then take homology of the resulting module-sheaf homotopy equivalence.
There is no need to identify sections of a homology sheaf with homology of sections.

The existing abelian-group ordered comparison does not state that its existentially
chosen homotopies are natural in B or locally module-linear. Those properties must
come from the explicit sorting formulas, as the new module comparison states. Its
proof does not infer them from the existing existence theorem. No statement is
disputed, no existing interface is changed, and no forced adaptation is needed.

## New nodes

`lem-pc-finite-affine-cech-base-change-coordinates`: local, additive ordered-coordinate
equivalences for the pulled-back specified model, with restriction, local scalar,
and signed differential compatibility. Source: Stacks Tag 02KE, termwise affine
calculation. It retains the existing affine-intersection and affine-pullback-section
theorems as proof dependencies. Its scope is strictly before homology and usual Čech
comparison.

`lem-pc-ordered-cech-module-comparison`: homotopy equivalence between any locally
linear ordered presentation and the direct image of a locally linear usual Čech
presentation. Source: Tags 01FJ, 01FK and 01FM, including both sorting homotopies.
Its proof is independent of affine geometry and constructs the natural locally linear
maps from the explicit source formulas. Both nodes inherit the parent's chapter,
unit, and blueprint ancestor. No change record is required: no existing statement,
definition, or public import changes.


## Second reading by A2

1. Interface check: PASS. Diffed the sole existing delivered module against the
   repository version. Its full theorem signature is byte-for-byte identical; its
   docstring and all three public imports are identical too. Only ordinary proof
   imports and the proof body differ. The two other modules are new; no definitions,
   instances, existing statements, or downstream modules are changed. No change
   record or forced adaptation is required.
2. Proof check: PASS as a decomposition. All three modules compiled through
   `lcompile.py --all`, without errors or warnings. Independently appended
   `#print axioms` to scratch copies of each module: each declaration uses only
   `propext`, `Classical.choice`, `Quot.sound`, and the allowed `sorryAx`.
   The original theorem has no sorry; exactly the two reported public theorems
   have `:= by sorry`. No forbidden declarations, proof-check bypasses, or data
   definitions occur. The coordinate witness is eliminated inside a proposition
   proof; it supplies no arbitrarily chosen public data.
3. Intermediate statements: PASS. Read both statements and complete proof docstrings,
   and compared them with Stacks Tag 02KE (the affine termwise tensor calculation)
   and Tag 01FM (both sorting homotopies). Affine intersections over the affine
   base justify arbitrary base change before homology; no flatness is needed.
   Local scalar compatibility of both coordinate systems gives module-sheaf maps
   and homotopies, including their inverses. Naturality of e is part of its
   presheaf-isomorphism type. Checked empty family, empty coefficient open, degrees
   above r, and negative terms. For r = 1 the usual repeated-tuple complex has
   differentials alternating zero and identity; its positive tail contracts, as
   required. The two statements separately isolate affine termwise geometry and
   general ordered-versus-usual combinatorics, and neither restates the item.
   Repeated independent searches with Loogle (`HomotopyEquiv`) and LeanFinder
   (signed sorting natural homotopy; affine fiber-product coefficient sections),
   and grep of Mathlib, Sheaf and WeilConjectures. Loogle's exploratory NatTrans
   query was invalid and was replaced by the valid query. No exact replacement
   was found. Existing AlternatingCechRestrictionHomotopy, AlternatingCechSection,
   AlternatingCechKernelNullHomotopic and sorting operators concern abelian-group
   section complexes. Their existential homotopies do not supply the restriction
   naturality and local scalar equations needed here. The explicit operators are
   useful material for the eventual module-sheaf proof, but do not close either
   new statement by a short application. Both remaining holes are substantial.
4. Route and pruning: PASS. The main proof explicitly obtains coordinates, proves
   zero negative terms by the existing model bound and additive pullback, applies
   the comparison, and composes homology and extension isomorphisms. All ordinary
   main proof imports serve those steps; new modules' public imports serve their
   signatures. The No longer needed section accounts for all removed old direct
   dependencies, including those retained transitively. Read the coherence unit
   and its realized record (currently empty statement and step arrays): this
   reduction retains the finite affine Cech/base-change step of part (a), and
   changes no unit or chapter route. Pruning is direct dependency pruning; it
   does not assert global unreachability of the old modules.
5. DAG check: PASS. Read all three delivered node records. Each Lean statement
   field exactly matches its file's signature, and each proof_deps list is the
   union of the proof steps' uses. The original node describes the actual Lean
   reduction and records its two new dependencies; new nodes contain their
   sources, full proof steps, searches, created and blueprint records, inherited
   chapter/unit, and complete Lean records. No out-of-scope original node field
   is changed by this delivery.

Changes by the second reader: added this independent review and corrected the
report's obsolete no-push wording. No Lean proof or statement required repair.
The result remains one upper hole closed and two strictly intermediate holes
added (net -1 direct holes), not a sorry-free proof.
