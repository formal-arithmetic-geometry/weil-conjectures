## What changed

Proved CategoryTheory.fpqc_descent_underlying_morphism with its unchanged signature.
Pull back the fpqc singleton using the supplied IsPullback square. Mathlib fpqc
subcanonicality makes q A an effective epimorphism. Use the transport identity,
IsBaseChange and beta.commutes to establish the descent equation on arbitrary test
schemes; EffectiveEpi.desc then gives existence, reconstruction and uniqueness.
A proved private helper transport_left_of_eq specializes transport_self to equal
base points. No proof imports were added. Updated the existing node to this route.

## Proved and sorry left

Closed: CategoryTheory.fpqc_descent_underlying_morphism
(node lem-galois-fpqc-descent-underlying-morphism), one original hole.
Added holes: none. Remaining holes in the delivery: none.
Local compilation and axiom probes pass. The server compilation and delivery
preflight pass in the dry run (the second reading remains for the assigned reader).
The theorem introduces no dependence on sorry.

## No longer needed

The proof does not need lem-galois-fpqc-morphisms-descend or its module
Sheaf.AlgebraicGeometry.FpqcMorphismsDescend. It avoids canonicalDescentIso,
baseChangeMap and the comparison of chosen squares with canonical fibre products.
No existing imports were removed: SchemeDescentDataCategory remains the only
public import, required by the unchanged statement. The diagonal-identity and
fibre-product nodes remain used. The existing Mathlib leaves
lem-galois-fpqc-covering-base-change and lem-weil-pbc-fpqc-representable-descent
supply cover stability and representable descent. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The canonical-fibre-product route in the node is unnecessary in the transport
encoding. Direct effective-epimorphism descent proves the same conclusion.
The local build mirror lacks SchemeDescentDataCategory.olean although its source
is present. An unchanged copy of that existing module is included in the sandbox
for dependency-order compilation; deliver3.py confirms that it has no source diff.
This copy also compiles on the server. No declaration is restated or changed.
A preliminary scratch test used the earlier identical category interface; the final
dry run checks the actual import and theorem name with the current source.

## Second reading by E1

1. **Visible interfaces: pass.** Diffed both sandbox modules against the repository.
   The full signature of `CategoryTheory.fpqc_descent_underlying_morphism` is byte
   for byte unchanged; only its proof, a private proved helper, and its proof
   explanation differ. `SchemeDescentDataCategory` is an identical compilation
   dependency, not an adaptation. No definitions, public imports, or existing
   statements changed; no change record is needed.
2. **Proof and trust: pass.** Read the entire proof and the transport/category
   definitions. Compiled both modules locally in import order without warnings.
   A scratch-copy `#print axioms CategoryTheory.fpqc_descent_underlying_morphism`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   There are no holes or prohibited declarations in either delivered module.
   In `hz`, equality after q A follows from bcA and transport_self, and equality
   of base maps is Over.w; IsPullback.hom_ext then identifies transport with g₂.
   The equations bcB and β.commutes yield precisely the EffectiveEpi.desc condition.
   Epi cancellation proves both the over-X equation and uniqueness, without
   assuming that the descended map already respects descent data.
3. **Split statements: pass, none.** No new public statement, new node, or new
   sorry is introduced. The private helper is only transport_self specialized
   by substitution of equal base points; proof irrelevance handles the equality
   witness. Identity r and empty schemes introduce no excluded cases: the same
   covering/sheaf and pullback arguments apply. Independent rg searches in
   lean/Sheaf and the upstream WeilConjectures checkout found transport_self,
   the related finite-etale proof, and the canonical fpqc descent theorem, but
   no existing theorem with this interface. A fresh msearch grep query
   `transport_self|effectiveEpi_of_fpqc|IsBaseChange` returned unrelated ring
   base-change hits. There is no split statement needing further search.
4. **Route and pruning: pass.** Read Stacks Tags
   [0241](https://stacks.math.columbia.edu/tag/0241) (the equal-composite overlap
   argument and descent of the underlying map) and
   [023Q](https://stacks.math.columbia.edu/tag/023Q) (universal effective epimorphism).
   The proof implements this argument on arbitrary test schemes. It uses the
   existing Mathlib sheaf/effective-epimorphism API directly. The similarly named
   helper in FpqcMorphismsDescend is private, and importing that module would
   reintroduce the avoided canonical-fibre-product route. The sole public import
   is required by the statement. `## No longer needed` names the only removed
   old proof dependency, lem-galois-fpqc-morphisms-descend. The sk-prop-h2 unit
   has no realized entry naming this auxiliary node or the pruned dependency;
   its Kummer/Brauer route is unchanged.
5. **Nodes: pass.** Diffed the item node; only proof, proof_deps and proof_origin
   differ. Read the cited covering-base-change, representable-descent and
   diagonal-identity nodes. Their declarations give exactly cover stability,
   fpqc subcanonicality and transport_self. The fibre-product node supplies the
   pullback universal property. The recorded steps match hcover, the effective
   epi instance, he, and the final desc/fac/cancellation argument. No new nodes.

Second-reading repair: replaced the stale theorem proof docstring (which still
claimed canonical fibre-product identification and Tag 02W0) with the actual
transport/effective-epimorphism argument. The compiled proof itself needed no repair.
