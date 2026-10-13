## What changed

Proved `AlgebraicGeometry.affine_principal_sheaf_complex_transport` in
`Sheaf.AlgebraicGeometry.AffinePrincipalSheafComplexTransport` without changing its
signature, universes, visibility, or existing docstring. Constructed the output complex
by the actual over-site equivalence followed by restriction along
`Spec(A_f) → D(f) → U`. Proved preservation of zero terms and finite-free ranks, then
assembled the derived comparison from Mathlib factorization isomorphisms.

Two proved private helpers establish compatibility of global sections with
pushforward/scalar restriction and the natural tilde/localization comparison.
Limit preservation uses the already proved upstream instance
`Scheme.Modules.preservesLimitsOfSize_restrictFunctor`. The latter follows from uniqueness of left adjoints, avoiding a separate
principal-open section calculation. The derived functor supports independent `wX` and
`wY`; no extra derived-category instance or hypothesis was introduced.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` for its proved
restriction-limit instance. The initially added explicit Mathlib zero-preservation
and adjoint-uniqueness imports were redundant and removed during second reading. Updated the existing node's proof,
proof dependencies and proof origin to the completely proved categorical argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.affine_principal_sheaf_complex_transport`
(node `lem-pc-affine-principal-sheaf-complex-transport`).
Both retained private helpers are fully proved; the duplicate limit helper was
removed in favor of the proved upstream instance. No holes remain in this module, and no
holes or new statement modules were added. This is a proof, not a decomposition.
The complete module compiled locally without errors or warnings.

## No longer needed

Removed proof import `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact` and its
planned dependency `lem-sc-derived-open-restriction-adjunction-exact`. This proof
requires neither extension by zero nor its exactness or adjunction: restriction's
limit preservation is proved directly and colimit preservation comes from Mathlib.

The planned black-box use of `lem-weil-pbc-spec-module-tilde-sections` is also no longer
needed: the natural comparison follows from adjunction uniqueness. Its Mathlib module
`Mathlib.AlgebraicGeometry.Modules.Tilde` remains a public import required by the
unchanged statement. No other existing imports were removed. No other DAG nodes
are added as proof dependencies; the added upstream proof import supplies a
previously proved instance. These are local pruning claims; other target paths
may still need the removed module and nodes. The unit record
`sk-thm-picard-duality.realized` has no statement/step nodes bypassed by this change.

## Where the brief, the DAG or earlier work was wrong

The DAG's exactness and sections facts are valid, but their stated interfaces do not
themselves supply the complex transport or its natural tilde comparison. Mathlib's
adjunctions provide a complete shorter route. No statement correction or forced
adaptation was needed. Empty principal opens, the zero ring, and rank zero require no
case exclusion: all constructions are functorial, and free sheaves are transported
using the coproduct comparison for the same `ULift (Fin r)`.

The literature TeX sources listed in the repository were not present on this machine.
Read the official source pages instead:
[Tag 08E7](https://stacks.math.columbia.edu/tag/08E7),
[Tag 01HV](https://stacks.math.columbia.edu/tag/01HV), and
[Tag 08BS](https://stacks.math.columbia.edu/tag/08BS).
Tag 08BS itself concerns K-injective restriction and cites exact extension by zero;
that stronger apparatus is unnecessary for this proof. Read the Mathlib declaration
sources for the adjunctions, over-site equivalence, restriction composition, free-sheaf
comparison, and derived exact-functor factorization. Searches via the project leanfinder,
loogle and grep wrappers found these components and no exact transport theorem.


## Second reading by X2

1. **Existing interface unchanged — pass.** Compared the complete module with the
   repository version using `diff` and compared the theorem signature as literal
   text: byte-identical, including `u`, independent `wX`/`wY`, all three derived
   category binders, arbitrary `M`, `f`, `U`, `hf`, `P`, `hb`, `hfree`, and `hiso`,
   and all three existential output clauses. Existing visibility, public imports,
   and docstrings are unchanged. No definition or target interface changes and
   no change record or forced adaptation is needed.

2. **Proof and actual constructions — pass.** Compiled the submitted module cleanly
   with `lcompile.py`. Appended `#print axioms` to a scratch copy: the main theorem
   and all original helpers use exactly `propext`, `Classical.choice`, `Quot.sound`;
   there is no `sorryAx`. Inspected all bodies: no `sorry`, axiom, unsafe/opaque
   declaration, foreign implementation, or arbitrary witness chosen from an open
   existence assertion. `C` is the actual termwise image of `P` under `E ⋙ T`.
   The retained isomorphism definitions use proved, constructed natural
   isomorphisms and adjunctions. The final delivery's declaration probe also checks
   their axioms after the import/helper simplification.

3. **Split statements and edge cases — pass.** No statement is split off and no
   new public statement, node, or hole is added. Checked `f = 1` (the whole affine),
   `f = 0` (empty principal open and zero localization), the zero ring, `U = D(f)`,
   rank zero, and arbitrary upper bound: the same restriction and finite-coproduct
   constructions apply without extra assumptions. `mapFreeIso` uses the identical
   `ULift (Fin r)`, so no rank or universe is changed. Consulted the cited Stacks
   pages [08E7](https://stacks.math.columbia.edu/tag/08E7),
   [01HV](https://stacks.math.columbia.edu/tag/01HV), and
   [08BS](https://stacks.math.columbia.edu/tag/08BS): the proof implements the local
   comparison and needs only exact restriction, not the K-injective assertion of
   08BS. The adjunction argument proves the natural comparison directly.

4. **Short route, imports, and pruning — repaired, then pass.** Searched with the
   independent phrases “natural isomorphism sheafification extension of scalars
   pullback affine scheme” (LeanFinder), the Loogle query pairing `restrictFunctor`
   with `PreservesLimitsOfSize`, and local `rg` searches for restriction exactness
   and preservation of limits in Mathlib, upstream, and `lean/Sheaf`. Found the
   already proved upstream `Scheme.Modules.preservesLimitsOfSize_restrictFunctor`
   in `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` (lines 91–109),
   which duplicates the original private helper. Replaced that helper by the
   instance and added its module as a plain proof import. Removed both redundant
   newly added Mathlib proof imports; a scratch copy without them compiles cleanly.
   The other two helpers give the short natural-adjunction comparison and were
   retained. Checked the complete old `proof_deps`: both removed nodes are named
   under `## No longer needed`. Opened `dag/units/sk-thm-picard-duality.json`:
   `realized.statement = []`, `realized.steps = [[]]`; none is bypassed by this
   local categorical argument. The upstream instance is a proved library tool.

5. **Node/code agreement — repaired, then pass.** The only changed node fields are
   `proof`, `proof_deps`, and `proof_origin`. The three proof steps match the actual
   construction of `C`, finite-rank comparison, adjoint-uniqueness comparison, and
   the ordered derived-factorization composite. Updated the first and third steps
   to name the upstream limit-preservation instance and the two remaining helpers.
   `proof_deps = []` correctly removes the two unneeded planned project nodes;
   the remaining categorical ingredients are proved Mathlib/upstream tools.
   The node's statement, `stmt_deps`, Lean signature record, unit and chapter stay
   unchanged. There are no new nodes whose required fields need checking.

Second-reading changes: removed the duplicated private restriction-limit proof;
used its proved upstream instance through a proof-only import; removed the two
redundant newly added Mathlib imports; updated the proof steps and this report.
No mathematical statement or construction was changed. Closed one original hole
(`AlgebraicGeometry.affine_principal_sheaf_complex_transport`); added zero holes.
