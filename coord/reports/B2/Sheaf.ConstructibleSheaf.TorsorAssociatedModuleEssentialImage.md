## What changed

Replaced the single hole in
`AlgebraicGeometry.Scheme.GaloisCover.associatedModuleFunctor_essentialImage`
with a compiling proof from two strictly partial section-evaluation statements.
The existing declaration's signature, visibility, and docstring are unchanged.
The two added proof imports are ordinary imports, so no existing public interface changes.

Added `Sheaf.ConstructibleSheaf.TorsorSectionRepresentation`, which constructs
`sectionRepresentation` directly on the actual module of sections `F(Y)` of the
cover. Scalars are restricted along the inverse coefficient-ring equivalence.
The action is restriction along the inverse deck transformation. Its identity
and multiplication laws are proved, as are the auxiliary deck-transformation
laws; no definition contains a hole or chooses a representation from a mere
existence theorem. This module also defines the corresponding lifted presheaf
and the diagonal normalization condition.

Added `Sheaf.ConstructibleSheaf.TorsorSectionEvaluation` for existence of a
normalized natural evaluation map, and
`Sheaf.ConstructibleSheaf.TorsorSectionEvaluationBijective` for bijectivity of
any supplied normalized map. These are separate steps: the first supplies a
natural morphism without an isomorphism claim; the second has no existential
representation or morphism conclusion, and proves the local descent/gluing
property of a supplied map. The main proof converts componentwise bijectivity
to a presheaf isomorphism, applies sheafification to its inverse, and composes
with the invertible counit at F. It uses the existing associated-module definition.

The existing node's proof and proof dependencies now describe this construction.
No existing definition, theorem statement, unit route, or other group's module
was changed. All four delivered Lean modules compiled in dependency order,
with no compiler warnings. The source import graph is acyclic: the three new
modules only import the associated-module definition and its new section
representation, and do not import the descent equivalence or this item's module.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.associatedModuleFunctor_essentialImage`
(node `lem-weil-pbc-torsor-associated-module-essential-image`). No hole remains
in the item's module.

Added exactly two named holes:

- `AlgebraicGeometry.Scheme.GaloisCover.exists_sectionEvaluation`, node
  `lem-weil-pbc-torsor-section-evaluation`, in
  `Sheaf.ConstructibleSheaf.TorsorSectionEvaluation`.
- `AlgebraicGeometry.Scheme.GaloisCover.sectionEvaluation_bijective`, node
  `lem-weil-pbc-torsor-section-evaluation-bijective`, in
  `Sheaf.ConstructibleSheaf.TorsorSectionEvaluationBijective`.

This is a decomposition, not a sorry-free proof of essential image: one upper
hole is closed, two strictly lower holes are added, and the net hole change
before any pruning is +1. Every added hole is the entire proof of a named public
theorem with a source, full proof in words, and a matching node.
`sectionRepresentation` and every auxiliary definition have genuine data.

## No longer needed

No original import or original proof dependency was removed. The original
`Sheaf.ConstructibleSheaf.TorsorAssociatedModule` remains necessary for the
statement and the final sheafification identification. The original plan has
only this definition as a dependency, so there are no original planned modules
to prune.

The discarded earlier route through
`Sheaf.ConstructibleSheaf.TorsorModuleDescentEquivalence` is not used or imported.
Its invalid `TorsorAssociatedFunctorComparison` module and
`lem-weil-pbc-associated-functor-comparison` node remain absent. They were
already removed by the earlier reader and are not part of this delivery.
This does not claim any pruning from the repository's existing target closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's five reading points are addressed as follows:

1. The target signature is preserved. The circular descent-equivalence imports
   are absent. The new modules form a downward dependency chain ending at
   `TorsorAssociatedModule`, which does not import this item.
2. There is no assertion about an arbitrary unconstrained functor T. The
   representation is the explicitly constructed `F(Y)` representation, and
   the evaluation map is constrained by naturality and normalization at every
   diagonal point of the cover. Those conditions recover its local formula.
3. The main proof uses the newly stated evaluation and gluing steps, not the
   descent equivalence that already depends on the present essential-image
   theorem.
4. The unit `sk-thm-p1` and its realized steps are unchanged. This is a
   decomposition below the unit level, preserving the essential-image claim.
5. The actual source import graph is acyclic and all delivered modules compile
   in import order. No cached cyclic comparison interface is used.

The node's original single paragraph does not name declarations for its
representation recovery, evaluation, and gluing steps; its only proof dependency
is the associated-module definition. The concrete representation is now made
into Lean and the two remaining steps are exposed as separate statements.

Stacks Tags 0DV5 (3), 0DV6, and 0A3R were read in the local Stacks source mirror,
`/home/ubuntu/c1-stacks-review/etale-cohomology.tex`, at the labels
`lemma-locally-constant-on-connected`,
`remark-functorial-locally-constant-on-connected`, and `lemma-pullback-filtered`.
Tags 04TR and 04TS were read in its `sites.tex`, at `lemma-glue-sheaves` and
`lemma-mapping-property-glue`. The first three discuss finite modules; the
arbitrary-module fixed-torsor version here is an explicit section/descent
adaptation, not a claim that 0DV5 itself states an arbitrary-module equivalence.
The new statement nodes mark their proof origin as agent-written adaptation.

Checked the zero module, trivial group/identity torsor, and an empty etale
object W. The representation construction and normalization impose no rank or
finite-generation hypothesis. For the identity torsor they give ordinary
constant-function evaluation; on an empty W both section modules are zero.
ConnectedSpace supplies the nonempty total space needed to recover the
constant value from global sections. Bijectivity is stated only for normalized
maps: an arbitrary natural morphism, such as the zero map on a nonzero module,
is not asserted to be invertible.

LeanFinder, Loogle, source searches of Mathlib and the project, and blueprint
searches found no existing independent theorem for these section constructions.
LeanSearch returned an internal server error; the unavailable searches are
recorded without treating them as evidence of absence.

## New nodes

`def-weil-pbc-torsor-section-representation`: the canonical section representation
and its coefficient-lifted presheaf and diagonal normalization. Its defining
module has no holes; the action laws are proved directly from restriction and
the cover's left-action laws.

`lem-weil-pbc-torsor-section-evaluation`: construction and naturality of the
normalized map from F into equivariant locally constant functions on fibre
products. This leaves no global isomorphism claim under another name.

`lem-weil-pbc-torsor-section-evaluation-bijective`: injectivity by separatedness
and surjectivity by equivariant gluing for a supplied normalized evaluation map.
It is independent of the existence statement, permitting separate proof work.

No change record is needed: only the item's proof and private proof imports
changed, and the other three modules and nodes are new.

## Second reading by B2

1. **Interfaces: pass.** Diffed every delivered module against the read-only
   repository. Only the item exists there: its sole theorem signature and
   docstring are byte for byte unchanged; the changes are its proof and two
   ordinary proof imports. The other three modules are new. No change record
   or target statement change is required.
2. **Proof and data: pass as a decomposition.** All four modules compiled with
   lcompile.py in import order without warnings. Scratch copies printed axioms
   for all six section-construction declarations, both open lemmas, and the
   original theorem. The constructions use only propext, Classical.choice and
   Quot.sound; the original theorem and the two open lemmas additionally use
   sorryAx. Exactly the two reported named theorem bodies contain sorry; no
   definition does. No forbidden declarations or external implementations occur.
   Restriction along inverse deck transformations gives the required left
   action: contravariance reverses composition, and inversion reverses it again.
3. **Split statements: pass.** Independently checked zero coefficients, the
   trivial group and identity torsor, and the empty etale object. ConnectedSpace
   includes nonemptiness, so diagonal normalization is not vacuous upstairs.
   Naturality on etale objects over Y determines evaluation on their graphs;
   translating the graphs by the torsor action covers the pulled-back torsor.
   Constant sections locally generate all sections of the constant pullback,
   so this determination applies to all local sections. This verifies why the
   bijectivity lemma can quantify over every normalized map. The existence
   lemma supplies no bijection, and the bijectivity lemma assumes a supplied
   map and supplies no representation: neither restates essential image.
   Both have matching nodes and complete proof docstrings. Read the cited
   local Stacks passages; the arbitrary-module extension is a site descent
   argument, not a direct invocation of the finite-type equivalence in 0DV5.
   Repeated LeanFinder, Loogle and source searches with different wording.
   The hits give connected locally constant value equality and generic sheaf
   separatedness, or concern different sites; none closes either entire lemma
   or duplicates it. In particular, the existing associated-module comparisons
   do not construct the F(Y) evaluation morphism. No few-minute closure was found.
4. **Route and pruning: pass.** The main proof constructs the section
   representation, obtains evaluation, establishes componentwise invertibility,
   then applies sheafification and its invertible counit. Each proof import is
   used; the original public associated-module import remains needed by the
   statement. The original proof_deps contains only that associated-module
   definition, which remains used, so No longer needed is complete (none).
   Read sk-thm-p1.json and its realized statement and steps: this reduction is
   below them, changes none, and does not import the circular descent-equivalence
   module. This is one original hole closed and two lower holes added, net -1
   holes closed before pruning, not a sorry-free essential-image proof.
5. **Nodes: pass after metadata repair.** Compared the existing node JSON with
   the repository: only proof, proof_deps and proof_origin change. Those steps
   follow the Lean proof, including inversion before sheafification. New nodes
   have source, creation, blueprint, chapter/unit, search and Lean records.
   Replaced the two new theorem nodes' flattened Lean signature records with
   their exact written signatures, and added independent second-reader searches.
   The definition node retains the canonical signature beginning at def, as
   required by preflight's signature parser (which omits noncomputable).

Second reading changed only the new nodes' signature/search metadata and this
report. The Lean proof and statements needed no repair. No additional holes
were closed or added by the second reading.
