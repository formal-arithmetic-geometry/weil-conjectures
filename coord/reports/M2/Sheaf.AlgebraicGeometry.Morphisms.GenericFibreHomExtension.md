## What changed

The original declaration `AlgebraicGeometry.Scheme.finiteEtale_genericFibre_hom_extension`
is reduced to extension existence and reducedness/density of the source generic restriction.
Its signature and docstring are unchanged. Two new modules are proof-only imports.
Mathlib's separated-morphism extensionality proves uniqueness in the original module.
All three sandbox modules compile without warnings using lcompile.py.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finiteEtale_genericFibre_hom_extension` by decomposition.
Added exactly two holes:

- `AlgebraicGeometry.Scheme.finiteEtale_genericFibre_hom_extension_exists`, node
  `lem-sbc-finite-etale-generic-fibre-hom-extension-existence`.
- `AlgebraicGeometry.Scheme.genericFibre_cover_reduced_and_dominant`, node
  `lem-sbc-finite-etale-generic-fibre-cover-density`.

The original module has zero holes. This is a decomposition, not a sorry-free proof
of the full mathematical theorem: one upper hole closed and two lower holes added.
The geometric lemma has no normality, connectedness, or finite-cover hypotheses.
The existence lemma does not assert uniqueness. No data definitions or arbitrary
witness choices were added.

## No longer needed

No existing imports were removed: all five public imports serve the original signature.
The original node had no proof dependencies to prune. No original modules or nodes
are declared unnecessary. For uniqueness, normality and integrality of C or Cη and
full faithfulness on Cη are unnecessary; reducedness of X, dominance of ψX, and
separatedness of πY suffice. The existence argument still needs generic-point fullness.

## Where the brief, the DAG or earlier work was wrong

The original node's two non-elementary steps had empty uses and proof_deps;
there were no stated dependencies from which to implement that plan directly.
The new nodes make the remaining geometric and existence inputs explicit.

Edge cases checked mathematically: C and X may be empty; the empty comparison has
dense image in the empty scheme and the empty scheme is reduced. Disconnected finite
etale covers are allowed throughout. A base that is not Noetherian is allowed:
033B proves smooth reducedness without Noetherianity, and 0BQM applies to normal
integral schemes without it. No statement correction or change record is needed.

The unit's spreading route is unchanged. The reduction does not replace any step of
that unit; it formalizes the generic-fibre morphism assembly below the unit level.
Search services and direct source searches found no matching extension theorem.
LeanSearch returned an Internal Server Error; LeanFinder and source grep were used.

## New nodes

`lem-sbc-finite-etale-generic-fibre-hom-extension-existence` states only existence,
with the original compatibility equations, in GenericFibreHomExtensionExistence.
Its proof in words explains normality, the integral generic fibre, fullness at the
generic point, and compatibility by faithfulness after restricting back.

`lem-sbc-finite-etale-generic-fibre-cover-density` states reducedness and dominance
for an etale cover of any smooth scheme over an integral base, in GenericFibreCoverDensity.
Its proof uses smooth reducedness (033B) and openness (01UA), followed by point lifting
in the pasted pullback. This is strictly geometric and contains no hom-extension claim.

## Second reading by M2

1. **Visible declarations and statements.** Compared the delivered modules with the repository versions. The
   existing theorem signature and docstring are byte-for-byte unchanged; the two added theorem signatures are
   exactly the node records. The added imports in the original module are proof-only imports.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; compilation succeeds without warnings.
   The original theorem has no `sorry`; the only remaining holes are the two named public theorems, each with its
   own blueprint docstring and DAG node. No forbidden declarations or hollow definitions occur.

3. **Split statements.** The existence theorem is strictly weaker than the original `ExistsUnique` target and
   asserts only extension existence. The density theorem is independent geometric input and asserts only reducedness
   of X and dominance of its generic restriction. Both retain the original hypotheses needed by their uses and do
   not add arbitrary witness data. The edge cases (empty schemes and disconnected finite etale covers) are covered.

4. **Pruning and route.** The uniqueness proof uses Mathlib's separated-morphism extensionality, with reducedness and
   dominance supplied by the density node. The unit's spreading route remains unchanged. No existing proof
   dependency or import is unused; no node can be pruned from the original route.

5. **DAG agreement.** The proof and proof dependencies of the original node match the declarations used in the
   Lean proof. Each split theorem has a matching node, source, proof description, blueprint, and Lean record.

I changed only the proof-only imports and proof of the original theorem, and added the two documented split theorem
modules and their DAG nodes. No statements, definitions, target declarations, or change records were altered.
