## What changed

Replaced the sole `sorry` in `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegreeTrace`
with a complete Lean proof from two strictly smaller intermediate theorems. The proof
chooses a splitting neighbourhood above every point of each site object, verifies that
their maps form an étale covering using `Scheme.ofArrows_mem_smallEtaleTopology_iff`,
uses the split trace computation, and combines the local identities through naturality
and `Presheaf.IsSheaf.hom_ext_ofArrows`. The final additive calculation is proved by
functor-category scalar arithmetic. The target signature and public imports are unchanged.

Added `Sheaf.AlgebraicGeometry.FiniteEtaleDegreeSplitAt` and
`Sheaf.AlgebraicGeometry.FiniteEtaleTraceSplitComponent`, each with one source-backed
public theorem, a detailed proof docstring, and a matching DAG node. Their imports in
the item's module are proof-only. All three modules compile locally without warnings;
the delivery dry run also compiles the new modules on the server and runs the axiom probe.

## Proved and sorry left

Proved `AlgebraicGeometry.Etale.finiteEtaleTrace_comp_restriction` (node
`lem-weil-pbc-finite-etale-trace-degree-trace`). This is a decomposition, not a completed proof of the transitive closure.
Holes closed: 1 (the declaration above). Holes added: 2 (the declarations below).
The delivery therefore has net -1 holes closed; no axiom-free target was completed.

Exactly two `sorry` declarations are included, both whole public theorem proofs:

- `AlgebraicGeometry.Etale.exists_finiteEtale_degree_split_at`, node
  `lem-weil-pbc-finite-etale-degree-split-at`. This is purely geometric: it supplies a
  local degree-counted splitting and has no sheaf or trace conclusion.
- `AlgebraicGeometry.Etale.finiteEtaleTrace_comp_restriction_app_of_split`, node
  `lem-weil-pbc-finite-etale-trace-split-component`. This computes one component under
  an explicit supplied splitting; it has no degree hypothesis and proves no global
  identity for a general finite étale morphism.

Edge cases checked in the statements and the combination: `d = 0` uses an empty index
set; the component theorem permits any finite index type, including empty; an empty
site object gives an empty covering, accepted directly by sheaf separatedness. No
connectedness, nonemptiness, positivity, or coefficient invertibility was added.

## No longer needed

Removed the direct proof imports `Sheaf.Paper.FiniteEtaleEtaleLocalSplit`,
`Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists`, and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` from the item's module.
Their mathematical roles remain below the two new intermediate nodes: local splitting,
trace characterization, and restriction comparison are still required there. They are
not declared globally unnecessary.

`lem-weil-pbc-etale-covering-base-change` is unnecessary on this route: splitting is
performed separately above each point of each site object, and the covering is verified
directly using Mathlib's jointly-surjective criterion. No covering-base-change module
is imported. All other geometric counting, coproduct, field-closure, fibre-product, and
localization dependencies from the old proof remain in the two new nodes as needed.

The item's direct proof dependencies are now only the two intermediate nodes,
`def-weil-pbc-abelian-etale-sheaves`, and `def-weil-pbc-etale-site`. The latter two supply
Mathlib's sheaf separatedness and covering criterion. Both statement imports stay.

The complete list removed from the item’s old direct `proof_deps` is:

- `def-pc-fibre-product`
- `def-pc-finite-locally-free`
- `def-weil-algebraic-closure`
- `def-weil-geometric-point`
- `def-weil-pbc-finite-etale-trace`
- `lem-galois-geometric-fibre`
- `lem-weil-pbc-etale-covering-base-change`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-finite-etale-etale-local-split`
- `lem-weil-pbc-finite-etale-trace-exists`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-scheme-coproduct-copies`

Except for covering base change, these remain statement dependencies or obligations
of the two intermediate nodes; removal from this direct list does not establish
that their modules leave the targets’ import closure. No whole module is claimed
pruned from that closure.

## Where the brief, the DAG or earlier work was wrong

The original plan contains the correct mathematical argument but does not provide
Lean declarations for the prescribed-count splitting or localized split-component
computation. Those are the two remaining obligations, rather than a renamed copy of
the global degree identity. Several original dependency records have no module or
individual declaration (`def-weil-algebraic-closure`,
`lem-weil-pbc-etale-covering-base-change`, `lem-weil-pbc-open-fibre-product`, and
`lem-weil-pbc-scheme-coproduct-copies`); the final proof avoids the covering-base-change
record, while the other geometric work is explicitly described in the new splitting
node for a future worker.

The nearest-blueprint-ancestor script returns `None` because the original node's
`created.item` is a module name. The new nodes retain the actual blueprint ancestor
recorded on the existing item: `lemma-weil-pbc-curve-locally-constant-reduction`, its
trace-splitting step. No unit statement or realized unit proof step is bypassed.

Read the source at Tag 03SH, `section-trace-method`, including the characterization
following Definition 03SE, and Tag 04HN, `lemma-finite-etale-etale-local`, from the
locally available Stacks source. Searches via `msearch.py` used LeanSearch, LeanFinder,
Loogle, and grep. LeanSearch returned HTTP 500 and is recorded as unavailable;
LeanFinder returned ring-theoretic étale decomposition/descent results; grep returned
ring and matrix trace formulas, with no exact sheaf trace component or prescribed-count
scheme splitting. Blueprint searches for finite étale splitting and trace found no
exact duplicate of either strict intermediate statement.

## New nodes

`lem-weil-pbc-finite-etale-degree-split-at` realizes steps 1–2 of the original plan at
an arbitrary site-object point. Its source is Stacks Tag 04HN plus the fixed-degree
geometric-fibre count implicit in Tag 03SH. Its Lean index type is `ULift (Fin d)`
to match the universe of the schemes. The proof plan counts the summands at the chosen
geometric point and transports the cofan by pullback pasting.

`lem-weil-pbc-finite-etale-trace-split-component` realizes the localized split computation
of steps 3–4. Its source is Tag 03SH's two trace-characterizing properties. It uses
restriction-comparison unit compatibility, localization of the trace, the section
sum formula, and the elementary diagonal/sum calculation. The actual sheaf-descent
combination is proved in the original module, rather than moved into either new node.

## Second reading by U1

1. **Interfaces — pass.** Compared all three delivered modules with the repository:
   only the original module existed. Its full theorem signature and existing docstring
   are byte-for-byte unchanged, as are both public imports. The only Lean differences
   are proof-only imports and the proof body. There are no definition or statement
   changes requiring a change record. Open change records name none of these declarations.
2. **Proof and trust — pass as a decomposition.** All three files compiled through
   `lcompile.py --all`, without errors or warnings. Scratch copies with explicit
   `#print axioms` for each delivered theorem report exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. Exactly the two reported public
   theorem bodies have `sorry`; there are no new definitions, forbidden declarations,
   or hidden holes. The global proof constructs an actual jointly surjective covering,
   uses component equality and naturality, and applies sheaf separatedness.
3. **Intermediate statements — pass.** Read both signatures, proof docstrings, and
   nodes against [Stacks 04HN](https://stacks.math.columbia.edu/tag/04HN) and
   [Stacks 03SH](https://stacks.math.columbia.edu/tag/03SH). The geometric lemma uses
   the distinguished point to count the summands, without assuming the base connected;
   the trace lemma assumes a supplied splitting and is independent of a fixed degree.
   Neither restates the general global identity. For `d=0`/empty `J`, the pullback
   is empty and the trace sum is zero; for empty `W`, sheaf sections are zero and
   any finite number of empty pieces is harmless. For degree one the sum is identity.
   Independent LeanFinder search for “sections of a finite etale covering trace
   diagonal sum” returned field/ring trace lemmas, not these sheaf results; grep
   for degree/coproduct and trace/restriction also found no match. Loogle’s first
   query could not resolve unqualified `IsColimit`; a qualified follow-up returned
   only general colimit machinery. `rg` through both Lean roots found the existing
   local splitting and trace uniqueness proofs, neither an exact duplicate. Closing
   either remaining theorem needs substantial geometric counting or localization/unit
   compatibility work, not an available one-line lemma.
4. **Route and pruning — pass after reporting repair.** Read the existing local
   splitting theorem, the chosen trace definition, its three-characterization
   existence theorem, and the localization argument in trace uniqueness. The two
   obligations are genuine parts of that route. Both new imports are used by the
   global proof; each public import supplies types or definitions in a signature.
   The unit `sk-thm-p1` and its `realized` statement and steps stay unchanged:
   trace splitting still serves the curve locally constant reduction. Expanded
   the report to enumerate every old direct proof dependency removed and distinguish
   direct import removal from whole-closure pruning.
5. **DAG — pass after citation repair.** The original node changes only `proof`,
   `proof_deps`, and `proof_origin`; its steps agree with the compiled proof. In
   all three nodes, `proof_deps` is the union of step `uses`. Both new nodes have
   source, complete proof steps, logged searches, blueprint ancestor, chapter/unit,
   creation metadata, and verbatim Lean signatures. Corrected the geometric node’s
   source location to distinguish 04HN in `etale.tex` from 03SH in
   `etale-cohomology.tex`.

Second reading changed reporting and the geometric node’s source citation only.
The Lean proof and both intermediate statements were retained. The report now
explicitly counts one hole closed, two added, net -1: a decomposition.
