## What changed

Closed the sole hole of `Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange` by
combining two strictly smaller intermediate theorems, in their own modules.
`GeometricFibreExchangeGerms` constructs the pointed iterated-pullback lift, the
canonical unit/restriction map, and the canonical source stalk isomorphism without
holes in their data. `IntegralGeometricFibreSections` states the invertibility and
germ formula of this restriction for integral morphisms.

The final proof obtains the invertible restriction map, uses the exchange germ
identity to identify the actual identity stalk up to source and target isomorphisms,
cancels the target isomorphism, and applies conservativity of the singleton family
of the identity geometric point. The universe-lift comparison is explicit.
No existing signature or definition changed. Local compilation of all three
modules succeeds without warnings. The dry run passes, pending the second reading.
The item's DAG proof and dependencies now describe this decomposition.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_isIntegralHom_geometricPoint`
(node `lem-sbc-integral-geometric-point-exchange`), one of one original holes.

Added holes:
- `AlgebraicGeometry.Etale.integralGeometricFibreSections`
  (`lem-sbc-integral-geometric-fibre-sections`). This is the integral section
  comparison, independently of exchange.
- `AlgebraicGeometry.Etale.geometricFibreExchange_germs`
  (`lem-sbc-geometric-fibre-exchange-germs`). This is the general compatibility
  of exchange and restriction on germs, with no integral hypothesis and no
  claim that exchange or the supplied comparison is invertible.

This is a decomposition, not an axiom-free proof of integral base change. The
hole count is one closed and two added. Both remaining proofs are exactly named
public `by sorry` declarations with source, proof in words, and matching nodes.
The item's module has no remaining sorry.

## No longer needed

Removed direct imports from the item:
`Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension`,
`Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization`,
`Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`,
`Sheaf.RingTheory.IntegralOverHenselianPair`,
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`.
These obligations remain needed through the intermediate nodes; no transitive
module is claimed pruned. The upper-star stalk module is publicly imported by
`GeometricFibreExchangeGerms`. The strict-henselian section-stalk lemma is part
of that intermediate's stated proof. All original proof-dependency nodes remain
needed below the new interfaces, rather than directly in the target proof.

## Where the brief, the DAG or earlier work was wrong

The original plan's geometric restriction and exchange compatibility had no
single callable interfaces. The existing stalk-continuity theorem is for sets,
the terminal stalk comparison is for abelian groups, while this item uses module
coefficients. The new nodes explicitly include the module compatibility rather
than treating those coefficient identifications as already available.
The henselian degree-zero theorem is applied to the identity of Spec B, as the
original plan requires; no properness of the integral morphism is asserted.

Checked the new statements on the identity square, the zero sheaf, the empty
fibre, and transcendental extensions of separably closed residue fields. The
compatibility statement assumes a specified germ formula, not invertibility;
the integral section statement explicitly preserves that formula. Neither is
just the original exchange-isomorphism assertion with its hypotheses repackaged.
The unit record has no realized nodes; its normalization route is preserved.

## Earlier second reading (a previous round; superseded)

Pending second reader; the target and intermediate modules compile, and the dry run validates the decomposition and node metadata.

## New nodes

`lem-sbc-integral-geometric-fibre-sections` packages steps 1 and 2 of the original
node as a direct-image germ/section comparison, with its formula. Its proof
retains stalk continuity, henselian integral restriction, and separably closed
field-extension invariance. It does not mention exchange in its conclusion.

`lem-sbc-geometric-fibre-exchange-germs` packages the compatibility part of step 3.
Its conclusion is a commuting identity for an arbitrary supplied restriction map;
it proves no isomorphism of exchange. The target combines the two assertions
using categorical cancellation and conservativity in actual Lean.

## Second reading by S1

1. **Visible changes and statements.** Compared the delivered target module with the repository version. The target declaration's signature is byte-for-byte unchanged; only its proof and proof-only imports changed. The two added declarations are new interfaces, and their signatures match their DAG nodes. Verdict: pass.

2. **Compilation and proof hygiene.** Compiled all three delivered modules with `lcompile.py --all`; all compile without warnings. The target has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The only remaining sorries are the two named split-off theorems, each with a docstring proof and matching node. Verdict: pass.

3. **Truth and strength of split statements.** `integralGeometricFibreSections` asserts only the integral section comparison and its germ formula, without asserting exchange. `geometricFibreExchange_germs` assumes an arbitrary map with that formula and concludes only the comparison identity, without integrality or invertibility. These are strictly smaller than the target and cover identity, zero-sheaf, empty-fibre, and transcendental residue-field cases as documented. Verdict: pass.

4. **Route and pruning.** The target follows the unit route: integral fibre sections, exchange-germ compatibility, cancellation, and identity-point conservativity. Removed imports are proof-only imports no longer referenced directly; required declarations remain available transitively through the two intermediate modules. Verdict: pass.

5. **DAG agreement.** The target node proof and `proof_deps` name exactly the two intermediate nodes and the conservative-family lemma used by the Lean proof. Both new node records contain matching statements, proof steps, sources, and Lean records. Verdict: pass.

Changed in this second reading: no Lean statements or proofs; added this review section only.
