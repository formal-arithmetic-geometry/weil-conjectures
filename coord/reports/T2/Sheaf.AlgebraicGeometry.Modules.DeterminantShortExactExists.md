## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.determinant_shortExact_exists` by a complete compiling
combination of the existing splitting cover and two strictly smaller new statements.
The theorem's signature and visibility are unchanged.

The first new module, `Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism`, states
existence of the concatenated-wedge **morphism**, without invertibility. It requires
finite local freeness only for the first term. The second,
`Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit`, proves bijectivity of
any morphism with this formula on every subopen of an explicitly supplied splitting
open. It assumes finite local freeness only for the outside terms and does not assume
global exactness. Both are public named theorems with `sorry`, source citations, full
proofs in words, and matching nodes.

The actual item proof obtains the morphism and its formula, obtains the existing
splitting cover, and for each point extracts a cover member from its supremum equality.
The local statement supplies bijectivity on every subopen. The already proved
`Hom.isIso_of_forall_bijective_app` gives global `IsIso`. Finally `(asIso φ).symm`
has inverse definitionally equal to `φ`, so the desired formula is precisely the
previous formula, with no transport or inverse calculation left unfinished.

All new proof imports of the item are non-public. Its direct import of
`Sheaf.LinearAlgebra.ExteriorTopDirectSum` moves to the split-local comparison module.
That module also imports the existing lifted-wedge extensionality statement. The
construction module imports Mathlib's exterior-power basis theorem for its planned
rank-vanishing argument. No existing interface or definition was changed and no
adaptations are included.

Validation: all three Lean modules compile together in import order using the required
`lcompile.py --all` command, without warnings. The completed combining proof needs no
new definitions, arbitrary chosen data, or axioms. The source-library local-bijectivity
criterion was read in full and receives an existing-declaration DAG node, with no
additional Lean module or hole.

## Proved and sorry left

Closed the original hole:

- `AlgebraicGeometry.Scheme.Modules.determinant_shortExact_exists`
  (`lem-sc-determinant-short-exact-exists`). Its module now contains no `sorry`.

Added two holes, each the whole proof of one public theorem in a separate new module:

- `AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_exists`
  (`lem-sc-determinant-wedge-morphism`), in `DeterminantWedgeMorphism.lean`.
- `AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_bijective_of_split`
  (`lem-sc-determinant-wedge-morphism-split`), in `DeterminantWedgeMorphismSplit.lean`.

This is a decomposition, not a sorry-free proof of determinant multiplicativity:
one original hole is closed and two strictly smaller holes are added. There are no
other added holes. The existing local splitting and lifted-wedge extensionality
statements remain dependencies; their proofs are outside this delivery.

The parts are not renamed versions of the item. The construction lemma does not
assert an isomorphism and even applies when the prescribed exterior degree of the
quotient differs from its rank. For example, for the split sequence
`O → O ⊕ O → O` with degrees `r₁ = r₂ = 1`, `r₃ = 0`, it gives the first inclusion,
which is not an isomorphism. The second lemma constructs no morphism or isomorphism:
it takes a morphism, its formula, and a compatible splitting on one open, and asserts
bijectivity there. The actual proof uses the separate covering statement and the
existing local-to-global theorem to combine these parts.

Edge cases checked before settling the statements: when `r₁ = 0`, the first term is
zero and lifts are unique locally; when `r₃ = 0`, the construction is the exterior
map of the injection and requires no quotient lifts. For the split comparison with
`r₃ = 0`, the quotient has rank zero and the splitting identifies the middle with the
first term. The empty wedge generates degree zero in either position. The empty open,
empty scheme, and zero rings cause no exception: sheaf sections on the empty open are
unique, and the relevant algebraic constructions allow zero rings. A non-affine
splitting open is allowed; the proof refines it to trivializing charts and uses the
sheaf property, rather than assuming its outside terms have global bases.

## No longer needed

Removed the item's direct proof import of `Sheaf.LinearAlgebra.ExteriorTopDirectSum`.
It is still needed, and imported, in the new split-local comparison module: this is
relocation, not pruning from the target closure. No existing node or module is claimed
pruned. In particular `lem-sc-local-splitting-finite-free` and
`lem-sc-exterior-top-direct-sum` remain needed. The top-direct-sum naturality theorem is
not separately invoked by the plan; compatibility with restriction is checked on the
standard wedge bases. No additional module is imported to use that naturality theorem.

## Where the brief, the DAG or earlier work was wrong

The item's DAG listed no proof dependencies although its proof text described local
splitting, a top exterior-power comparison, and gluing. Its original two proof imports
alone do not provide the sheaf morphism or the sheafified split comparison. These are
now the two precise remaining steps; the updated node records the dependencies actually
used by the completed proof. No mathematical error in the statement or the unit route
was found. The unit `sk-thm-picard-rr` has no realized node binding that this change
bypasses; determinant multiplicativity still follows the local splitting and wedge
route in its rank-induction argument.

The referenced literature file is not present in this clone. Its determinant
paragraph is preserved verbatim in `lem-sc-riemann-roch.json`, field
`blueprint_proof_text`, which was read along with the unit record and the local splitting
and direct-sum nodes. The new proof details are marked as agent-written elaborations
of that preserved source. The external raw-source fetch was unavailable; no replacement
source or mathematical claim was invented.

Searches: LeanFinder returned ordinary-module exterior-power `desc`, `map`, and
`hom_ext`, plus free-module and degree-one naturality infrastructure, but no determinant
sheaf construction or split-local comparison. LeanSearch returned Internal Server Error;
this is recorded as unavailable, without a mathematical verdict. Loogle did not
recognize `exteriorPower`. Mathlib and both library roots were searched by `rg`, and
blueprint searches for determinant, wedge, exterior power, and locally bijective were
checked. The existing source theorem `Hom.isIso_of_forall_bijective_app` is an exact
match for the local-to-global step and was used directly. New-node search records give
the queries and findings.

## New nodes

`lem-sc-determinant-wedge-morphism`: existence of the lift-independent wedge morphism,
without invertibility, requiring a finite locally free rank only for the first term.
The proof explains local lifts, rank-vanishing of changes of lifts, separate
alternation, restriction compatibility, and descent through exterior and tensor
sheafification.

`lem-sc-determinant-wedge-morphism-split`: bijectivity on every subopen of a given
splitting open for a morphism satisfying the wedge formula. The proof compares with
`existsUnique_topDirectSum` on trivializing charts, uses lifted-wedge extensionality,
and proves injectivity and surjectivity on arbitrary subopens by separatedness and
gluing. It does not require exactness away from the given open.

`lem-sc-module-hom-local-bijective-iso`: attaches the already proved source-library
`AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_bijective_app` to its exact DAG
statement. It adds no declaration and no hole. Its source is the existing Lean proof,
which reduces to Mathlib's local-bijectivity criterion and reflection of isomorphisms.

No change records are required: all existing statements, definitions, and public
imports are unchanged. The existing item node changes only `proof`, `proof_deps`, and
`proof_origin`.

## Second reading by T2

1. **Interfaces unchanged.** I diffed the delivered item against the repository version. The
statement of `determinant_shortExact_exists` is byte-for-byte unchanged; the two added
modules contain new declarations only. No definition or public interface was altered.

2. **Compilation and trust.** All three delivered modules compile together with
`lcompile.py --all` without warnings. The item has no `sorry`; the only remaining
`sorry`s are the complete proofs of the two named split-off theorems, each documented
and represented by a node. The axiom probe reports only the expected `sorryAx` inherited
from those open statements, together with `propext`, `Classical.choice`, and
`Quot.sound`; no forbidden declaration or hollow definition occurs.

3. **New statements.** I checked both split-off signatures and their edge cases. The
construction theorem asserts only existence of the wedge morphism and does not claim
invertibility. The split theorem assumes an explicit splitting on one open and concludes
bijectivity on its subopens, with no unnecessary global exactness or middle-term rank
hypothesis. Rank-zero, empty-open, and zero-ring cases are covered by the same empty
wedge and sheaf arguments. Searches found no existing declaration with either
statement.

4. **Pruning and route.** The item's proof imports are minimal for the written route:
the direct-sum comparison import moved to the split-local module, while the local
splitting and existing local-to-global isomorphism criterion remain used. The unit route
still passes through local splitting and the exterior direct-sum comparison; no realized
unit step is bypassed. No old proof dependency is unused.

5. **DAG agreement.** The item's `proof`, `proof_deps`, and `proof_origin` match the
combining proof. Each new theorem has a matching node, source, natural-language proof,
search record, and Lean declaration record. The existing local-bijectivity declaration
is recorded as an existing dependency node.

I changed only this second-reading section of the report after review; no Lean statement,
proof, node, or import required repair.
