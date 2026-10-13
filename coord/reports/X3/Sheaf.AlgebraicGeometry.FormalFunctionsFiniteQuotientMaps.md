## What changed

Proved `AlgebraicGeometry.formalFunctions_finite_quotient_maps`, with its original
signature, from the smaller finite-open compatibility statement
`AlgebraicGeometry.formalFunctions_finite_open_factorization` in the new module
`Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenFactorization`.

For each prescribed finite choice D, the proof chooses a local resolution K and local
open data E₀, then uses `{ E₀ with source := D.source }` as E. The source field is
independent of psi, unit_square and target. Thus the germ in ha is definitionally the
germ required by Theta. Applying the helper's additive map to ha, and using its two
compatibility equations and hr, proves the Theta equality. This is real composition
of three equations, not a renamed statement of the original theorem.

The new helper states a map between open cohomology groups, its compatibility with
restriction of a global class, and its compatibility with restricted h-maps. It
mentions no a, r, stalk, germ, local comparison predicate or Theta predicate. It needs
no properness, coherence or Noetherianity, and even permits V not containing y. The
existential map is eliminated only in a proof of a proposition; no definition chooses
an arbitrary witness from an unproved existence statement.

Added a local irreducibility annotation for moduleCohomologyFMap. Without it, equality
matching unfolded its chosen injective resolutions and repeatedly exceeded 60 seconds;
keeping this construction abstract makes the same proof compile within the limit.
The annotation is local; no definition or signature was changed. The scoped heartbeat
setting supports elaboration of the nested cohomology types. The unused-variable linter
is disabled only for this theorem: its unchanged interface retains hF, while this
formal compatibility argument does not need coherence. All imports added for
proofs are ordinary, non-public imports. Updated the original DAG node's proof,
proof_deps and proof_origin to this route.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.formalFunctions_finite_quotient_maps`
(node `lem-weil-pbc-formal-functions-finite-quotient-maps`). No sorry remains in the item.

Added one hole:
`AlgebraicGeometry.formalFunctions_finite_open_factorization`
(node `lem-weil-pbc-formal-functions-finite-open-factorization`). Its proof is exactly
`by sorry` in its own public theorem/module, with a source and a full proof plan in its
docstring and node. This delivery is a decomposition (one hole closed, one added), not
an unconditional proof or a net decrease in holes. The still-unproved part is precisely
restriction and composition of the finite h-map; the germ/resolution-choice argument
and its combination with ha and hr are complete.

The new statement was checked on V=empty, zero coefficients, empty fibres, p=0 and n=0.
These are compositions of zero maps or ordinary section maps, with no surjectivity or
invertibility assumption. The construction works for arbitrary open V because the
projection identity gives W=j inverse U′ without requiring either open to be top.

## No longer needed

Removed these eight redundant direct imports from the item:

- Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
- Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
- Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
- Sheaf.AlgebraicGeometry.FormalFibreCohomology
- Sheaf.AlgebraicGeometry.FormalFunctionsLocalStalkComparison
- Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
- Sheaf.AlgebraicGeometry.TensorPullback
- Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

The required definitions remain visible through the unchanged public import of
FormalFunctionsFinitePullback. Functoriality and adjunction are dependencies of the
new lower helper's mathematical proof, not direct proof tools of the item. Basic
properties are not used explicitly by the written proof or the new helper's plan.
The original parent proof_deps no longer directly cite the functoriality, basic
properties, tensor pullback or tensor adjunction nodes. The h-map
definition is still used for the restriction maps in the written proof and recorded
in the updated dependency list.

Exact original proof_deps removed from the parent: `def-pc-module-pullback`,
`lem-pc-module-pullback-adjunction`,
`lem-weil-pbc-module-cohomology-fmap-basic-properties`, and
`lem-weil-pbc-module-cohomology-fmap-functorial`.

No whole-library module is claimed pruned from the targets' transitive import closure:
these modules can still occur through other imports. The resolution-independence
argument in original step 1 is unnecessary. A proved experimental independence lemma
was therefore removed from the delivery; the shared source-record construction is
shorter. No blueprint unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan's comparison of arbitrary source resolution identifications is
unnecessary. Local open choices are quantified universally in ha, so their source can
be set to D.source directly. The open-choice structure has no condition tying that
source field to psi. The resulting record keeps its valid unit_square unchanged.

Existing composition and restriction declarations do not directly state the finite
factorization, including the transported open and restricted adjunction-unit triangle;
that strictly smaller step is the one new item. Mathlib/source/Sheaf searches found no
ready-made statement. LeanSearch was unavailable (Internal Server Error); LeanFinder
returned only germ identities, and grep found the separate cohomology tools.

Read Stacks Tags 02OD, 01E4 and 01FB online. In 02OD the omitted verification identifies
the infinitesimal neighbourhoods because c_n factors through c. Tags 01F7/01FB provide
the restriction/composition argument recorded for the helper. No source error or
statement dispute was found, and no existing statement/definition was changed.

## New nodes

`lem-weil-pbc-formal-functions-finite-open-factorization` records the two cohomology
compatibility equations for a finite pullback restricted to inverse-image opens.
Its source is the factorization in Stacks 02OD and the cohomology functoriality in
01F7/01FB. Its two proof steps identify the inverse-image opens, restrict the finite
h-map, and compare the restricted composite units by adjunction before applying
cohomology composition. Its module contains the only added sorry. It inherits the
parent's chapter, unit and blueprint ancestry. Searches (LeanSearch unavailable,
LeanFinder and grep) and the zero/empty/degree-zero cases are recorded above and in
the node. The preflight requires the change record
`coord/changes/formalFunctions_finite_quotient_maps_elaboration.md` for the local
irreducibility command. It documents the original/new section context and the
unchanged exported interface; there are no forced adaptations.

## Second reading by X3

1. Compared both delivered modules with the repository. The factorization module is
   new; the existing theorem signature is byte for byte unchanged (also checked by
   extracting the text before `:= by`). No existing definition, public import,
   visibility or target statement changes. The local irreducibility annotation is
   confined to the section and has its change record. Verdict: pass.
2. Compiled both modules in import order with lcompile.py: clean, 19.4 and 25.0 seconds.
   The only delivered sorry is the named public factorization theorem. No forbidden
   declaration or hollow definition occurs. The resolutions and open choices are
   eliminated within a proposition; no definition selects arbitrary data from an
   unproved existence theorem. Axiom checks are recorded below. Verdict: pass.
3. Read the new factorization statement, its full proof docstring and its node against
   formalFunctionsFiniteFMap, the projection identity, E/D.unit_square and the existing
   restriction/composition theorems. Restriction adjunction injectivity pins each psi;
   the fields source and target do not enter its unit square. The statement isolates
   two open-cohomology compatibilities and has no germ, a, r or Theta: it is a strict
   subargument, not a renamed parent. Empty V, zero F, empty fibre, p=0 and n=0 introduce
   no surjectivity or invertibility requirement. Reviewed Stacks 02OD and 01FB directly.
   Independent Loogle search (`"moduleCohomology", "restriction"`) returned no hits;
   LeanFinder on composition over inverse-image opens returned only scheme section
   identities. Ripgrep on Sheaf, upstream cohomology and Mathlib found the separate
   composition/restriction tools, not this combined finite-unit compatibility.
   Closing the remaining helper requires the transported open and adjunction diagram,
   rather than a few-minute application of an existing theorem. Verdict: valid split.
4. The written upper proof uses the shortest source-choice route: replace E.source by
   D.source, then compose the helper equations with ha and hr. All new proof imports
   are non-public. The eight removed direct imports are redundant through the existing
   public definitions or unused. The exact old proof_deps no longer cited directly are
   `def-pc-module-pullback`, `lem-pc-module-pullback-adjunction`,
   `lem-weil-pbc-module-cohomology-fmap-basic-properties` and
   `lem-weil-pbc-module-cohomology-fmap-functorial`; the latter adjunction/functoriality
   tools remain needed by the lower helper's plan. Checked dag/units/sk-thm-p1.json:
   neither the parent nor any removed dependency realizes a unit statement or step;
   the realized route is preserved. No whole-library module is claimed pruned.
   Verdict: pass; one original hole closed and one lower hole added, net zero.
5. Checked the parent node's two steps against the actual record replacement and
   equation composition, and checked proof_deps is the union of uses. The new node
   has its source, statement dependencies, complete proof steps, searches, created,
   blueprint, chapter/unit and verbatim Lean signature. The proof origins describe
   the reduction and the remaining diagram. Verdict: pass.

Changes by the second reader: corrected the main theorem's stale docstring, which
still described resolution independence, to describe the actual shared-source proof;
added independent Loogle and LeanFinder results to the new node; made the exact four
removed original node dependencies explicit here. No proof or signature changed.

Scratch-copy `#print axioms` checks of both declarations compiled successfully:
each lists exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
The last is expected from the named open helper and still-open imported statements;
there is no additional axiom. Scratch copies were removed before delivery.
