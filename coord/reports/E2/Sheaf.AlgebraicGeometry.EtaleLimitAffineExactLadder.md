## What changed

Replaced `AlgebraicGeometry.Etale.etale_limit_affine_exact_ladder`'s hole by an explicit
construction of its maps and a proof of all seven requested clauses, from compatible
short exact systems and a generic cohomology cocone. Its existing signature is unchanged.
Added `EtaleLimitCompatibleExactSystems` and its node. Reused the proved
`EtaleLimitCanonicalCohomologyDiagram` for both coefficient systems.
No existing dependency module or public import was changed.

The boundaries are the actual `Sheaf.H.δSucc` maps, the stage maps are `H.map bi`, and the
limit map is `H.map b`, transported through the specified cohomology isomorphisms. Stage
injectivity gives surjectivity. Exactness supplies both the zero composite and the limit
preimage. Ext functoriality of extension classes and morphisms of short complexes give the boundary
squares; coefficient naturality and the middle square give the remaining square.
The construction module and the item compile with `lcompile.py`; the final item check
took 43 seconds and emitted no warnings. The original declaration's parsed signature
was compared verbatim with the baseline and is unchanged. The delivery dry run performs
the remaining preflight and axiom checks.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.etale_limit_affine_exact_ladder`
(node `lem-weil-pbc-etale-limit-affine-exact-ladder`). This is a decomposition, not a
sorry-free proof of the target closure.

Added the construction hole
`AlgebraicGeometry.Etale.etale_limit_compatible_exact_systems`
(node `lem-weil-pbc-etale-limit-compatible-exact-systems`). It asserts no cohomology
conclusion and is strictly the compatible-short-exact-system part of the argument.
The zero system, empty schemes, a singleton index and degree zero were checked against
the constructions: no positive-degree vanishing of the limit middle sheaf is required.
This is the only new hole and none remain in the item's module. The generic diagram
and cocone are supplied by the existing proved
`AlgebraicGeometry.Etale.etale_limit_canonical_cohomology_diagram`; quotient comparison-leg
invariance is proved here from its cocone naturality and the displayed map formulas.
Thus one upper hole is closed and one strictly smaller construction hole is added: net
holes zero for this decomposition.

## No longer needed

No existing imports were removed: the item's only original import supplies its public
signature. The direct sheaf-system construction eliminates the affine-site presentation
and strictification detour, hence the following original proof dependencies are unnecessary
for this argument (this is local pruning, not a claim that other targets stop using them):

- `lem-weil-pbc-limit-affine-transition`, `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
- `lem-weil-pbc-affine-etale-site-colimit`, `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`.
- `lem-weil-pbc-affine-etale-site-topos`, `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`.
- `lem-weil-pbc-site-cohomology-pullback`, `Sheaf.CategoryTheory.SiteCohomologyPullback`:
  the boundary square is proved directly using Ext.mapExactFunctor_extClass.
- `lem-weil-pbc-derived-functor-long-exact`,
  `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`: the already proved
  Ext-encoded sheaf-cohomology sequence supplies the exactness used here.
- `lem-weil-pbc-derived-functor-injective-vanishing`: Ext injective vanishing is used directly.

The compatible injective-system construction, exact inverse image and exact filtered
colimits remain in the new construction node's proof plan. Pullback functoriality remains
in the cocone proof. The unit's realized statement and proof-step nodes are not bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated unavailable construction glue as a reason to abandon. That glue
can be isolated as a strictly smaller theorem, and the complete cohomological argument can
be formalized from it. Existing `etale_limit_replacement_exact_systems` does not state the
transition morphisms of short complexes or the middle component of its limit comparisons;
these are necessary for the transition-boundary and middle-map squares. The new construction
interface includes precisely these missing compatibility data. It is in continuation
form to keep the dependent system data explicit during proof assembly. No statement is disputed.

## New nodes

`lem-weil-pbc-etale-limit-compatible-exact-systems` in
`lean/Sheaf/AlgebraicGeometry/EtaleLimitCompatibleExactSystems.lean` isolates the product
injective-system and cokernel construction with its stage and limit compatibility. Its proof
in words follows Stacks 0EXZ and exact filtered colimits; it works for arbitrary schemes,
so no geometric affine-limit or affine-site-colimit theorem is needed.

No cocone node is added: `lem-weil-pbc-etale-limit-canonical-cohomology-diagram`
already supplies the required diagram and cocone.
No change record or forced adaptation is needed because all existing interfaces are preserved.

## Second reading by E2

1. **Signatures and visibility.** Compared the delivered item with the repository baseline;
   the existing theorem signature is byte-for-byte unchanged. The added construction module
   has the signature recorded by its new node, and its public import is required by the item.
   Verdict: pass.
2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both
   compile without warnings. The item contains no `sorry`, while the sole remaining `sorry`
   is the named construction theorem. No forbidden declarations were found. Verdict: pass.
3. **Statements and new node.** Checked the continuation theorem and the construction node
   against the source descriptions and edge cases (singleton index, zero systems, empty
   schemes, and degree zero). The construction statement is strictly smaller than the item
   and introduces no cohomology conclusion. Verdict: pass.
4. **Route and pruning.** The proof uses the compatible-system construction and canonical
   cohomology diagram, then proves the seven ladder clauses by boundary and middle-map
   naturality and exactness. The unit route is retained; old affine-site dependencies are
   pruned from the item and recorded above. Verdict: pass.
5. **DAG agreement.** Updated the item proof and proof dependencies to match the actual
   imports and proof, and added the construction node with source, proof plan, Lean record,
   and search record. Verdict: pass.

The second reading changed only this report section; no Lean declarations or statements were
changed during review.
