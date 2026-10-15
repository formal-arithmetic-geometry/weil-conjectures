## What changed

Filled all three proofs in `lean/Sheaf/CategoryTheory/SimplicialMatchingObject.lean`.
All theorem signatures, definitions, visibility, and existing docstrings are unchanged.
The second reader removed three redundant direct public imports (listed below).

- `CategoryTheory.SimplicialObject.matching_object_zero` uses terminality to construct the
  unique morphism and the unique isomorphism between terminal objects.
- `CategoryTheory.SimplicialObject.matching_object_one` chooses the limit of the discrete
  two-object diagram. The fan lift and projection identities give mutually inverse maps
  between morphisms into the product and arbitrary pairs. Associativity gives naturality.
  Limit uniqueness gives the projection-preserving isomorphism, and lifting the face maps
  gives the unique matching map.
- `CategoryTheory.SimplicialObject.matching_object_succ_succ` supplies the finite-index
  instances and takes the canonical multiequalizer cone. The multifork lift, projection,
  compatibility, and extensionality APIs give the compatible-tuple equivalence, its inverse
  laws, and uniqueness. Associativity gives naturality. Reindexing Mathlib's
  `SimplicialObject.δ_comp_δ` with the second index minus one proves face compatibility,
  and lifting that tuple gives the unique matching map. The reindexing follows the existing
  proof in `WeilConjectures.AlgebraicGeometry.SemiRepresentableObject`.

The existing DAG's three steps are realized directly; no route or dependency changed, so no
node update is needed. The unit `sk-prop-h2` has no realization assigned to this node and its
route is preserved.

A declaration-local `linter.unusedVariables` setting on `matching_object_zero` suppresses
warnings about the original existential witness names `μ` and `α`, whose predicates are
`True`. Their signatures remain textually identical.

Validation: the whole item compiles cleanly through `lcompile.py`. All three declarations'
`#print axioms` outputs contain only `propext`, `Classical.choice`, and `Quot.sound`.
A textual check confirms that all three existing theorem signatures are unchanged, there
are no `sorry`s, and every Lean source line is at most 100 characters.

## Proved and sorry left

Closed all three original holes, all attached to
`lem-weil-pbc-simplicial-matching-object`:

- `CategoryTheory.SimplicialObject.matching_object_zero`.
- `CategoryTheory.SimplicialObject.matching_object_one`.
- `CategoryTheory.SimplicialObject.matching_object_succ_succ`.

Sorry left: none. Holes added: none. No split-offs, new modules, or adapted modules.

## No longer needed

Removed the redundant direct public imports
`Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
`Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer`, and
`Mathlib.CategoryTheory.Limits.Shapes.Terminal`.
The retained source module publicly imports all three, so the public transitive import
closure is unchanged; no DAG node or module is pruned. All old `proof_deps` are still used:
finite-limit existence, simplicial objects, and the face identity. Change record:
`coord/changes/SimplicialMatchingObject-redundant-imports.md`.

## Where the brief, the DAG or earlier work was wrong

No mathematical, statement, or interface error found. No statement or definition changed.
The cited local Stacks TeX file is absent from this checkout, so the cited sources were read
at [Stacks 0186](https://stacks.math.columbia.edu/tag/0186) and
[Stacks 0167](https://stacks.math.columbia.edu/tag/0167). Their tuple compatibility relation
and face identity agree with the existing signatures and the proof.

## Second reading by D2

1. **Repository comparison.** I compared the delivered module with the repository version. The
three existing theorem signatures and all definitions are byte-for-byte unchanged; only proofs,
a declaration-local linter option, and imports differ. Verdict: pass.

2. **Proof and axioms.** The module compiles through `lcompile.py`; it contains no `sorry`,
`axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `sorryAx`. Scratch `#print axioms`
checks for all three theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
Verdict: pass.

3. **Split-off statements.** No statements were split off and no new theorem or definition was
added. The existing node remains the sole DAG node for the three declarations, and no duplicate
Mathlib or upstream declaration was introduced. Verdict: pass.

4. **Route and pruning.** The proofs use finite-limit and multiequalizer universal properties,
the simplicial face identity, and the existing boundary-index definitions. The unit route and
DAG proof dependencies remain intact. The three direct Mathlib imports were redundant because
`WeilConjectures.CategoryTheory.SimplicialMatchingObject` already publicly imports them, so they
were removed. Verdict: pass.

5. **DAG agreement.** The node's three proof steps and dependencies match the implemented route:
finite-limit existence, compatible-tuple universal properties, and face compatibility followed by
the matching map. No node or unit record requires an update. Verdict: pass.

Small cases checked against the definitions: degree zero is terminality and degree one has
two unconstrained projections; for degree two (`n = 0`), the three pairs `(0, 1)`, `(0, 2)`,
and `(1, 2)` give respectively `d₀ ≫ d₀ = d₁ ≫ d₀`, `d₀ ≫ d₁ = d₂ ≫ d₀`, and
`d₁ ≫ d₁ = d₂ ≫ d₁`, the three expected face relations (composition in Lean order).
For general `a < b`, `a ≤ b - 1` is exactly the inequality required by `δ_comp_δ`.
Limit hom-ext proves both inverse laws and uniqueness; associativity proves naturality.
The Mathlib Multifork and Fan API source was checked for an existing full tuple-equivalence
statement; the implemented lift/fac/hom-ext proof already uses the generic available results.
No simpler full theorem or new split-off was found in the source library.

Changed in this second reading: removed the redundant public imports
`Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
`Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer`, and
`Mathlib.CategoryTheory.Limits.Shapes.Terminal`; retained the local linter option because the
unchanged `True`-witness signature necessarily leaves the names `μ` and `α` unused.
