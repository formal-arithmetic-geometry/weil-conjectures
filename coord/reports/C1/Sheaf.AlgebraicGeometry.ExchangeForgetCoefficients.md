## What changed

Proved `AlgebraicGeometry.Etale.exchange_forget_coefficients` in
`Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`, with its signature unchanged.
The proof assembles the existing exactness and canonical edge-comparison instances,
the homology comparison, and `moduleAbelianDerivedExchange_compatibility`.
It then proves the final equivalence using cancellation of the endpoint isomorphisms,
reflection of isomorphisms by the underlying sheaf functor, and
`DerivedCategory.Plus.isIso_iff`.

Updated the existing node's proof, proof dependencies and proof origin to match the Lean.
No definitions, statements, public imports or other modules changed.
Local compilation after import pruning passes without warnings in 2.0 seconds.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.exchange_forget_coefficients`
(node `lem-weil-pbc-exchange-forget-coefficients`).
One of one original sorries proved; zero split off; zero added; none left in the delivery.
The proof uses existing library theorems and instances; it does not assert that their
entire transitive import closure is free of sorry.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison`.
- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`.

The last two remain required transitively through the public compatibility module,
and their nodes remain proof dependencies. The separate
`lem-weil-pbc-etale-constant-ring-module-equivalence` node and its module are no longer
needed on this item's proof branch: both the item and the canonical comparisons
already use the same ModuleCat-valued encoding. This removes the explicit encoding
transport in old DAG step 2. No global unreachability claim is made for that module.
All remaining stated proof dependencies are retained. No unit realization is bypassed:
this auxiliary node is not a statement or step in the unit's `realized` field.

## Where the brief, the DAG or earlier work was wrong

The old DAG step 2 required a separate transport between encodings even though the
Lean statement and comparison tools already use precisely the same encoding. It is
unnecessary here. The remaining planned argument is implemented directly, including
conservativity; no statement defect was found. Mathlib already supplies the reflection
instance for sheafCompose of the module-to-abelian forgetful functor, so no new
module-linear inverse construction or conservativity lemma was necessary.

## Second reading by C1

1. I compared the delivered module with the repository version. The theorem signature and all
   existing declarations are unchanged byte for byte; only the proof and three proof-only imports
   differ. The removed imports are accounted for below.
2. I compiled the delivered module with `lcompile.py` successfully and checked a scratch copy with
   `#print axioms`: the theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
   There is no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition in the delivery.
3. No statement was split off and no new node was added. The proof uses the existing homology
   comparison, exactness instances, canonical comparison instances, exchange compatibility, and
   the derived homology isomorphism criterion; the final reflection argument is a direct
   application of those declarations and is strictly about the unchanged target statement.
4. I checked the shortened route against the unit record. The unit's realized statement and steps
   are untouched, and the proof does not bypass a realized unit step. The constant-ring transport
   is unnecessary because the theorem and all canonical comparisons already use the same
   `ModuleCat` encoding. The three removed imports are proof-only and no longer needed.
5. I checked the node's Lean record, `proof`, `proof_deps`, and `proof_origin` against the proof.
   The retained dependencies account for the typeclass instances and compatibility theorem, and
   the removed constant-ring-equivalence dependency is absent from the delivered route. No
   definition or public interface changed.

I changed only the proof imports, the theorem proof, the corresponding existing node's proof
metadata, and this second-reading report. No new nodes, statements, or change records were needed.
