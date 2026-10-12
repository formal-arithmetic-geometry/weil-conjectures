## What changed

Replaced the admitted proof of
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_stalk_data`
by a compiling reduction to three strict parts of its argument. Its signature,
public imports, and public interface are unchanged. The parent docstring and DAG
proof now describe the implemented route.

The three new modules are:

- `Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor`: a finite locally
  constant sheaf becomes constant on a connected finite monodromy torsor. It has
  no Sylow cover and no representation-to-sheaf functor.
- `Sheaf.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient`: a connected finite
  Q-torsor admits a quotient by any subgroup H, with geometric fibre cardinality
  H.index and the original total space as a connected H-torsor. It mentions no
  coefficient field, representation, or input sheaf.
- `Sheaf.ConstructibleSheaf.ConnectedTorsorModuleDescent`: on an already supplied
  connected finite torsor, recover a representation from a specified sheaf and
  its constant trivialization, and construct the associated-sheaf functor with
  stalk and object comparisons. It constructs no Sylow subgroup or cover of U.

The parent proof chooses `H : Sylow ℓ Q` and proves its p-group and prime-index
conditions using `H.isPGroup'` and `H.not_dvd_index`. Its intermediate `htriv` is
an explicit composition of four isomorphisms: inverse pullback composition for
cH.π and v, pullback composition along the commuting square of total spaces,
the image of the original trivialization under pullback along e.hom, and
`Scheme.upperStarConstantSheafIso`. The descent lemma is applied to this
specific trivialization of v*G; then the existential witnesses and all conjuncts
are assembled. There is no remaining hole inside the parent proof.

Read Stacks 0DV5 (3), 0DV6 and 0A3R in the available local Stacks checkout,
0BND (1)-(3) and Section 03SF in pione.tex, and 04TR/04TS in sites.tex.
The new docstrings include complete proof plans. In particular, module descent
is described by equivariant sections on W times_V Y; gluing preserves the
equivariance equations and linear operations, so the construction applies to
infinite representations as well as finite ones. Reconstruction uses the
canonical descent datum of F and connectedness of Y to recover constant linear
transition maps. The universe lifts transport existing group/ring structures;
no replacement definition of a torsor or hollow definition was introduced.

Searches: LeanSearch returned Internal Server Error (recorded as unavailable);
Loogle for `Rep, CategoryTheory.Sheaf` returned no hit; LeanFinder returned
abstract Galois category, invariants, and condensed module functors, without
these scheme-torsor/sheaf interfaces; Mathlib grep found no matching torsor
construction. Also searched the two library roots, all DAG nodes, and the
blueprint index. The existing Galois equivalences supply the finite monodromy
plan, but do not state these interfaces. The existing module gluing node is
for open subsets of a topological space, not descent along an etale torsor.

Validation: all four delivered modules compile through lcompile.py. The static
module comparison finds no changed signature or public import, no changed
interface, one original admission removed, and no admission in the parent.
The final deliver3.py --no-push run performs local compilation, the axiom probe,
server compilation of the new modules, and the stage-3 preflight. Nothing is
pushed; the second reading remains for the next worker.

## Proved and sorry left

Proved from the three stated intermediates:
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_stalk_data`
(node `lem-weil-pbc-sylow-cover-stalk-data`). One of one original sorries removed.

Exactly three named admissions remain in the new modules, each with proof
exactly `:= by sorry`, its source, full proof in words, and matching node:

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_monodromy_trivializing_torsor`
  — `lem-weil-pbc-finite-monodromy-trivializing-torsor`.
- `AlgebraicGeometry.Scheme.GaloisCover.exists_connected_subgroup_quotient`
  — `lem-weil-pbc-connected-torsor-subgroup-quotient`.
- `AlgebraicGeometry.Scheme.GaloisCover.exists_module_descent_stalk_functor`
  — `lem-weil-pbc-connected-torsor-module-descent`.

The result is a reduction, not a proof free of admissions in its dependency
closure. The three new statements are separate mathematical arguments, not
renamings of the parent theorem.

## No longer needed

Removed these six direct proof imports from the parent:

- `Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`.
- `Sheaf.Paper.GaloisLisseRepresentations`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.

The route no longer uses the finite-locally-free rank argument. Nodes
`lem-weil-pbc-fibre-degree-base-change`,
`lem-weil-pbc-finite-locally-free-degree-locally-constant`, and
`def-pc-finite-locally-free` are removed from this argument: subgroup quotient
fibres are coset sets, whose cardinality is directly the index. Thus their first
two modules above are not needed to prove this item by the new route.

The finite monodromy and fundamental-group equivalences remain planned proof
dependencies of the new finite-monodromy and quotient nodes; they are not
claimed mathematically obsolete. The geometric-fibre splitting node
`lem-galois-geometric-fibre` remains in the quotient node for separably closed
fields. Its FiberDegree module is no longer a direct parent import. The complete old-minus-new direct proof dependency list is:

- `cor-galois-lisse-representations` (retained under finite monodromy).
- `thm-galois-fundamental` (retained under finite monodromy and quotient).
- `thm-galois-lc-etale` (retained under finite monodromy and quotient).
- `lem-galois-geometric-fibre` (retained under quotient).
- `def-pc-finite-locally-free` (bypassed by the coset-fibre argument).
- `lem-weil-pbc-fibre-degree-base-change` (bypassed).
- `lem-weil-pbc-finite-locally-free-degree-locally-constant` (bypassed).

There are
no fixed-unit realization nodes pruned: this item is below sk-thm-p1's realized
statement and steps. No claim is made that any module is globally unreachable
from every other target.

## Where the brief, the DAG or earlier work was wrong

The previous split asserted object comparisons for arbitrary M, T and G from
only a stalk comparison. It is false: M = 0, G constant of rank one, P trivial,
and the constant-sheaf functor give the zero-versus-rank-one counterexample.
This delivery does not use either rejected statement. Instead, its first lemma
supplies an actual trivialization of G on a connected torsor. The quotient
retains that same total space via e, the parent transports the trivialization
by actual isomorphisms, and descent recovers M from the canonical descent datum
of v*G. M is existential in that lemma, never an unrelated arbitrary input.

Edge cases checked against the source and statements: G = 0 uses the trivial
monodromy group and zero coefficient module; Q = 1 has index one; H = 1 gives
the original cover; H = Q gives the base; A = 0 descends to the zero sheaf.
The descent statement does not require P to be an l-group and works for
infinite input representations. Its connected nonempty total-space hypothesis
is essential to recover constant transition matrices; it is supplied by both
the finite monodromy and subgroup quotient statements. It does not require
l to be invertible on the scheme, noetherianity, separatedness, or nonzero rank.

Neither new node cites the parent or either other new node in its proof.
Checked the statement/proof dependency closures of the existing tools: none
reaches the parent, so this reduction introduces no cycle. The parent node is
updated with exactly the dependencies of the implemented proof.

The blueprint ancestor utility cannot follow module-valued created.item fields
on this existing stage-3 chain. New nodes therefore inherit the parent's
already recorded blueprint.from.node and extend its via chain, rather than
inventing an ancestor or modifying the fixed unit. This is a bookkeeping issue,
not a reason to bypass the unit route.

## New nodes

`lem-weil-pbc-finite-monodromy-trivializing-torsor` records the pre-Sylow part of
Stacks 0A3R: take the finite monodromy image and its connected torsor and
trivialize the module sheaf there. The finite Galois/lisse equivalences are
used as the same generic tools as in the old parent plan. This node makes the
trivialization, its finite-dimensional coefficient module, and the connected
total space available to independent workers.

`lem-weil-pbc-connected-torsor-subgroup-quotient` records the geometric part for
an arbitrary subgroup. With the existing convention of a left deck action,
the quotient fibre is H\Q; inversion identifies its cardinality with Q/H and
hence H.index. It retains the torsor's total space and commuting square, which
are needed to transport the particular sheaf trivialization in Lean.

`lem-weil-pbc-connected-torsor-module-descent` records the sheaf-theoretic part
on an already provided connected finite torsor. Its proof uses the explicit
module-valued variant of the gluing construction in 04TR and its mapping
property in 04TS, with scalar transport and chosen geometric lifts for the
natural stalk isomorphisms. This is also a generic tool independent of Sylow
subgroups. Its sheaf recovery hypothesis prevents the earlier false split.

No change record is required: no existing statement, definition or public
interface changed. All new nodes inherit sec-proper-base-change and sk-thm-p1.


## Second reading by C1

1. Interface: PASS. Read the full diff against the repository module and checked
   its declaration table with `stage3_delivery.diff_module`: no existing signature
   changed, no declaration disappeared, and all original public imports remain
   byte for byte. Only proof imports, the proof docstring, and the proof body
   changed. The three new modules introduce the three reported theorems and no
   definitions or replacement notions. No change record is required.
2. Proof and axioms: PASS as a reduction with three explicitly admitted parts.
   Independently compiled all four modules in import order through lcompile.py;
   all compiled without warnings. A scratch copy of the parent with explicit
   `#print axioms` for all four declarations reported exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The delivered parent contains
   no sorry; the three new holes are precisely named public theorems with bodies
   `:= by sorry`. Checked for forbidden declarations and attributes, and for
   hollow definitions: none. The pullback-composition orientations and commuting
   square match the actual four-isomorphism composition in htriv. This does not
   certify the parent free of admissions in its dependency closure.
3. Split statements: PASS. Read the definitions of GaloisCover and finite locally
   constant module sheaves, and the local source copies at
   `/home/ubuntu/c1-stacks-review/`: 0DV5 (3), 0DV6, 0A3R, and 04TR/04TS.
   ConnectedSpace includes nonemptiness. Finite stalks over the finite field give
   finite monodromy without a noetherian or invertibility hypothesis. Quotient by
   an arbitrary subgroup is valid even for a nonnormal subgroup: left deck
   H-orbits are H\Q, and inversion compares their cardinality with Q/H.
   Descent uses the actual trivialization of F, so M is recovered from its
   descent datum rather than assumed unrelated to F. Evaluation of maps between
   constant sheaves on the connected total space gives constant linear maps;
   the cocycle yields the action. Equivariant-section descent applies to every
   representation, including infinite-dimensional ones. Checked zero G/A,
   Q = 1, H = 1, H = Q, and P = 1. These are three separate mathematical
   arguments, each strictly a part of the parent construction.
   Independent LeanFinder queries used constant etale trivialization/monodromy,
   intermediate subgroup index/fibres, and module-valued torsor descent/stalks;
   none matched these interfaces. Loogle found constantSheaf additivity, which
   alone supplies neither torsor descent nor recovery of F. Searched both Lean
   roots with quotient/subgroup/trivialization/associated/descent terminology.
   Upstream quotientCocone and fiber_quotientCocone are useful ingredients, but
   do not supply the connected subgroup torsor and commuting square together;
   EtaleTorsorDescent classifies abelian sheaf torsors, not this module functor.
   No split lemma can be closed by a few-minute application of these results.
4. Route and pruning: PASS after report correction. The parent opens its original
   hole, uses Mathlib directly for the Sylow facts, transports the specified
   trivialization explicitly, and assembles all witnesses. Its three helper
   imports are used, and the six removed proof imports are correctly reported.
   All seven old proof_deps absent from the new direct list are now explicitly
   named above, including the four retained transitively. The unit sk-thm-p1
   realized statement/steps do not name this parent or any removed direct node;
   no unit-level route was bypassed. Existing public imports were preserved;
   new public imports provide vocabulary or instances for the signatures.
5. Nodes: PASS. Compared each Lean declaration with its node lean.statement and
   checked proof_deps equals the union of proof-step uses in all four nodes.
   The parent node describes the actual three-helper reduction, Sylow facts,
   and pullback isomorphisms; the new nodes describe their still-open proofs
   honestly, cite their sources, record the searches and origin, and carry the
   required chapter/unit/created/blueprint/Lean fields. No existing statement
   or statement dependency was changed.

Second-reading changes: completed the direct-dependency pruning inventory and
added this independent review. No Lean proof, signature, definition, or node
needed repair. The temporary axiom probe was removed from the delivered files.
