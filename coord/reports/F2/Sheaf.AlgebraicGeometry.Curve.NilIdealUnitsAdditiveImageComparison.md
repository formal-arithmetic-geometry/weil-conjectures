## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.nonempty_nilIdealUnitsAdditiveImageIso` with a complete
Lean composition of three isomorphisms. Its signature and both existing public
imports are unchanged. Added three proof-only imports, each naming one new
statement module:

- `Sheaf.AlgebraicGeometry.Curve.NilIdealUnitImageRelativeKernel` identifies the
  unit image with the pushforward of the relative unit kernel on Z_J.
- `Sheaf.AlgebraicGeometry.Curve.IdealAdditiveImageRelativeKernel` identifies the
  additive image with the pushforward of the relative additive kernel on Z_J.
- `Sheaf.AlgebraicGeometry.Curve.SquareZeroRelativeUnitsAdditiveKernel` linearizes
  the relative kernels on Z_J, where the ideal I/J is square zero.

The proof pushes forward the relative isomorphism using `Functor.mapIso` and
composes it with the first identification and the inverse of the second.
No data definition, existing signature, target, or module held by another group
was changed. The item's node now follows this proof.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.nonempty_nilIdealUnitsAdditiveImageIso`
(node `lem-sc-nil-ideal-units-additive-image-comparison`). There are no sorries
left in the assigned module.

Added exactly three named public theorem holes, each in a separate module:

- `AlgebraicGeometry.Scheme.nonempty_nilIdealUnitImageRelativeKernelIso`
  (`lem-sc-nil-ideal-unit-image-relative-kernel`).
- `AlgebraicGeometry.Scheme.nonempty_idealAdditiveImageRelativeKernelIso`
  (`lem-sc-ideal-additive-image-relative-kernel`).
- `AlgebraicGeometry.Scheme.nonempty_squareZeroRelativeUnitsAdditiveKernelIso`
  (`lem-sc-square-zero-relative-units-additive-kernel`).

This is a decomposition, not a proof free of additional holes: one upper hole
closed and three lower holes added, for net -2 in holes closed minus added.
Each lower statement is a separate part of the argument: the first contains
only units and needs no square-zero condition, the second contains only
additive functions and needs neither nilpotence nor square zero, and the third
compares kernels on Z_J and needs no nilpotence assumption on I in X. Each
has a source, a complete proof in words, and its own DAG node.

The four-module set compiles in import order with `lcompile.py --all`, without
warnings. Small cases were checked mathematically before stating the lemmas:
I=J, I=0, J=0 with I square zero, and X empty all give the expected trivial
images or the usual square-zero ideal. The additive lemma also handles I=top:
the relative kernel and image are the entire additive sheaf on Z_J. The
square-zero lemma handles X=Spec Z, I=(2), J=(4): subtraction of one identifies
{1,3} in (Z/4)^units with {0,2} additively. Thus this lemma does not require I
to be nil. Nilpotence cannot simply be removed from the unit-image lemma:
for Spec Z, I=(2), J=(8), all four units mod 8 map to one mod 2, whereas only
1 and 7 lift to integral units. This excluded case explains its nil hypothesis.

## No longer needed

None. No existing import was removed. Every original definition dependency
remains needed through the new lemmas: ideal sheaves and products, nilradical,
unit restrictions, and additive restrictions. The assigned module's direct
proof dependencies are now the three new nodes; the four former direct
proof-dependency nodes remain prerequisites of those nodes and are not pruned.
The former direct dependencies are, explicitly:
`def-sbc-ideal-sheaf-powers`, `def-weil-pbc-scheme-reduction`,
`def-sc-etale-additive-structure-restriction`, and `def-sc-gm-torsor`.
All four remain used transitively; none is no longer needed in the import closure.
No unit statement or realized unit step was bypassed (`sk-prop-h2` has empty
realized lists in this repository).

The unit-image module imports the existing Gm module directly and does not
import the additive structure module, since its statement involves only units.

## Where the brief, the DAG or earlier work was wrong

The previous node's proof cites only definitions for the affine calculations
and passage to categorical sheaf images. Those definitions do not themselves
supply the local lifting, relative-image identification, or square-zero kernel
isomorphism as usable Lean theorems. The three new statements expose these
parts without changing any hypothesis or conclusion of the assigned theorem.
The common relative-kernel route preserves the original affine formulas and
descent argument.

The literature source named by the node is not present in this read-only
checkout. The same source is reproduced in the assigned declaration's complete
proof docstring and DAG proof, which were read in full. An attempt to retrieve
the pinned public raw source returned HTTP 404. The new proof docstrings and
nodes extract the affine argument recorded there; no replacement source or
unsupported existence-based construction was introduced.

LeanFinder returned local ring infrastructure, including nilpotent quotient
unit lifting and trivial square-zero extension lemmas, but no comparison of
these etale sheaf images or relative kernels. Loogle found
`IsNilpotent.isUnit_add_one`, which supplies only the local unit fact. Grep
found general categorical image-to-kernel maps, but no geometric relative
kernel identification. Searches in both library roots and the DAG found no
existing statement of any of the three new comparisons. LeanSearch was
unavailable (Internal Server Error); the actual search records are in
`searches.jsonl`.

## New nodes

`lem-sc-nil-ideal-unit-image-relative-kernel` records affine lifting of a
relative unit kernel through a nil ideal, followed by descent and uniqueness
of image factorizations. Source: the original blueprint's Step 1 and Claim,
as reproduced in the assigned node and docstring. It also cites the existing
closed direct-image left-exactness node for preservation of kernels.

`lem-sc-ideal-additive-image-relative-kernel` records the equality of the
image of I_B in B/J_B and the kernel of B/J_B to B/I_B, followed by descent.
It uses the same source and existing direct-image left-exactness node.

`lem-sc-square-zero-relative-units-additive-kernel` records the mutually
inverse formulas u ↦ u-1 and a ↦ 1+a on the relative kernel on Z_J, with
inverse unit 1-a and multiplication becoming addition because products in
I/J vanish. It uses the same source and restriction definitions.

All three nodes carry the actual three kinds of Mathlib search and belong
to sec-curve-estimates / sk-prop-h2. No change records are needed.


## Second reading by F2

1. **Unchanged interface — pass.** Compared every delivered module with the
   repository. Only the assigned module already exists; its sole theorem's
   signature is byte-for-byte unchanged. Its two public imports are unchanged.
   The differences are three ordinary proof imports, a docstring explanation,
   and the proof body. The other three files are new theorem modules. There
   are no definition changes, forced adaptations, or change records.

2. **Proof and axioms — pass as a decomposition.** Independently compiled all
   four files in import order through `lcompile.py --all`, without errors or
   warnings. A scratch module printed axioms for all four declarations: each
   uses only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The
   latter is expected because the three listed lower theorems remain open.
   The assigned theorem has no `sorry`; its composition has the correct
   direction, maps the relative isomorphism through the same lower-star
   functor, and ends with the inverse additive image identification. There
   are no data definitions, forbidden declarations, or arbitrary witnesses
   chosen into definitions. The scratch module was removed before delivery.

3. **Split statements — pass.** Read all three signatures, source references,
   complete affine proofs in words, and matching nodes. Checked the cases
   I=J, I=0 (hence J=0), J=0 with I square zero, empty X, I=top for the
   additive statement, and I=(2), J=(4) on Spec Z for the relative square-zero
   statement. In the latter case the units {1,3} and additive kernel {0,2}
   correspond by subtraction of one. Independently checked the nil-unit
   lifting argument: a representative b of a relative kernel element has
   b-1 in the extended nil ideal, so b is a unit. In Spec Z with I=(2),
   J=(8), removal of the nil hypothesis fails, as documented. None of the
   statements restates the whole item: two identify separate images without
   comparing units to additive functions, and the third compares relative
   kernels without the nil hypothesis on X or either image.

   Repeated Mathlib searches with different wording using LeanFinder
   (nilpotent closed immersion and square-zero unit kernel), Loogle
   (`CategoryTheory.Limits.image, CategoryTheory.Limits.kernel`), and grep
   (units/ker/square and image/kernel). Also searched both repository Lean
   roots. The categorical results `kernelFactorThruImage`,
   `Abelian.coimageIsoImage'`, `imageToKernel'`, and
   `ShortComplex.Exact.isIso_imageToKernel'` do not supply the geometric
   exactness or local quotient identification needed here. The nearby
   `nonempty_additiveIdealImageTensorIso` remains open and has a different
   codomain and a quasi-coherence hypothesis. No duplicate or immediate
   closure of a lower theorem was found. Search records are in searches.jsonl.

4. **Route and pruning — pass.** The reduction retains the original affine
   unit lifting, quotient-image calculation, and square-zero multiplication
   argument. All three new imports are used; each public import supplies
   notation or definitions in a signature. Explicitly checked the four old
   proof dependencies: all remain used transitively, so no node or module
   is pruned. Read `dag/units/sk-prop-h2.json`; its realized statement and
   step lists are empty, and this decomposition bypasses no realized unit.
   Count remains one upper hole closed and three lower holes added, net -2;
   this is not claimed as a sorry-free proof.

5. **DAG agreement — pass.** Checked all four node records against their
   modules. Each `lean.statement` exactly matches its theorem signature;
   each `proof_deps` equals the union of its proof steps' `uses`. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`. The three new
   nodes contain the required creation, source, blueprint, searches, Lean,
   chapter, and unit fields. Their affine arguments are the separate parts
   actually used by the Lean composition.

Second-reading changes: clarified `## No longer needed` by explicitly naming
all four former direct proof dependencies and their continued transitive use;
added this independent review and its validation evidence. No Lean proof or
statement repair was needed, and no additional hole was introduced.
