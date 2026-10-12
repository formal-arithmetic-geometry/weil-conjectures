## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.exists_fpqc_singleton_affine_refinement` with a complete
proof using Mathlib. The declaration, docstrings, module header, and two public
imports are unchanged. No new declarations or modules were added.

The proof implements the existing four-step DAG plan:

1. Extract `Flat f` from singleton membership in the flat precoverage and
   `QuasiCompactCover (PreZeroHypercover.singleton.{0} f)` from membership in the
   quasi-compact precoverage. Apply
   `QuasiCompactCover.exists_isAffineOpen_of_isCompact` to the whole affine base,
   which is compact, obtaining `U : Fin n → X.Opens`, affine opens, and their
   images covering the base.
2. Define `h` by `Sigma.desc` of the inclusions and `g` by `Sigma.desc` of their
   composites with `f`. `Sigma.hom_ext` and the coprojection identities prove
   `g = h ≫ f`; the finite affine coproduct instance proves the source affine.
3. Mathlib's flatness instance for `Sigma.desc` applies to the flat composites
   of the open inclusions with `f`. Identify each composite's range with the
   image of its open by explicit subtype witnesses and apply
   `Surjective.sigmaDesc_of_union_range_eq_univ`.
4. Both source and target are affine, so `g` is affine and quasi-compact by
   Mathlib instances. Apply `g.singleton_mem_fpqcPrecoverage`.

The singleton index universe is explicitly `0`; this resolves an otherwise
unconstrained universe in the quasi-compact-cover instance. The proof never
requires `n > 0`. In particular the empty-base case and `Fin 0` are admitted.
The node belongs to `sk-prop-h2`, whose `realized` lists are empty; no unit
statement or proof step is bypassed. The existing node's proof and dependencies
already describe this argument, so no node update is necessary.

Validation: the prescribed `lcompile.py` single-file compile succeeded without
warnings. The required `deliver3.py --no-push` additionally checks local and
server compilation, declaration axioms, and preflight. No delivery is pushed
by this worker. Searches through `msearch.py` (leanfinder, loogle, grep) and
local Mathlib/source-library inspection located the Mathlib facts used above.
The local literature files are absent on this machine; the source statements
were checked at https://stacks.math.columbia.edu/tag/022B and
https://stacks.math.columbia.edu/tag/022E.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.exists_fpqc_singleton_affine_refinement`
(blueprint: `lem-galois-fpqc-singleton-affine-refinement`). One of one original
sorries closed. No `sorry` remains in the delivered module, and none is added
elsewhere. The proof imports only the existing Mathlib modules and uses no
project declarations resting on `sorry`.

## No longer needed

None. Both original public imports remain necessary for the statement's fpqc
precoverage and scheme coproduct infrastructure. No proof-only imports were
added. All existing proof-dependency nodes continue to supply the definitions,
coproduct, flatness, surjectivity, and affine/quasi-compact facts of the original
plan. No node or module is pruned, and no new nodes are introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's local-ring flatness check and affine-open
singleton check are already encapsulated in proved Mathlib instances and
`Hom.singleton_mem_fpqcPrecoverage`. Thus this item admits a direct complete
proof and requires no intermediate theorems left for future workers.

## Second reading by P2

1. **Visible declarations unchanged — pass.** Compared the complete delivered module
   with the repository using `diff -u`. The only difference is the body replacing
   the original theorem's `sorry`; the signature is byte-for-byte unchanged, as
   are the docstrings, module header, public imports, and all other source text.
   No definition, statement, change record, or additional module is delivered.
2. **Kernel proof — pass.** Independently compiled the delivered file with the
   prescribed `lcompile.py`, without errors or warnings. Compiled a scratch copy
   containing `#print axioms` for
   `AlgebraicGeometry.Scheme.exists_fpqc_singleton_affine_refinement`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. Inspected the
   complete source: no remaining `sorry` or prohibited declaration mechanisms.
3. **Split statements — pass, none.** No new declaration, new node, or split-off
   statement exists. Checked the construction for an empty affine base (allowing
   `Fin 0`), the identity covering, and a flat surjection of affine schemes.
   The proof never assumes that the finite index set is inhabited.
4. **Shortest route and pruning — pass.** Inspected Mathlib's finite affine-open
   extraction theorem, flatness of open immersions/composites and `Sigma.desc`,
   surjectivity from the union of ranges, and singleton fpqc membership. Searched
   `lean/Sheaf` and the upstream library for affine refinement declarations;
   the upstream finite-affine fpqc-topology theorem supplies sieve members, not
   the required opens of the original source with coproduct and inclusion map.
   The direct Mathlib construction is appropriate. Both public imports support
   the statement (fpqc precoverage and scheme coproducts). The old dependencies
   are definitions and Mathlib leaves still used by this route, so `No longer
   needed` is complete. Read `dag/units/sk-prop-h2.json`: its realized statement
   and step lists are empty; this below-unit refinement bypasses no unit route.
5. **DAG agreement — pass.** Read the complete existing node
   `lem-galois-fpqc-singleton-affine-refinement`. Its four proof steps, dependency
   union, and documented proof origin agree with the finite-open extraction,
   coproduct construction, flatness/surjectivity, and affine singleton fpqc check
   in Lean. Mathlib instances encapsulate the planned local-ring argument. No
   node modification is needed.

Changes made by the second reader: appended this review record only; the proof
and metadata required no repair.
