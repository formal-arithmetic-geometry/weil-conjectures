## What changed

Proved `integralClosure.semilocal_normalization_dim_one` with its original signature and
visibility. Added a proved private helper `integralClosure.normalization_same_universe`.
The helper applies `AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`
and injects the maximal spectrum into a finite sigma type of spectral fibres over the
maximal spectrum of the base. The public proof applies the helper to `FractionRing B`
and transports the conclusions along `AlgEquiv.mapIntegralClosure`. Mathlib proves the
fraction-field conclusion directly. Updated the existing node's proof to describe this
implementation. No public imports, definitions, or statements changed.

## Proved and sorry left

Closed one original hole: `integralClosure.semilocal_normalization_dim_one`
(node `lem-sc-semilocal-dim-one-normalization`). Added zero holes. No `sorry` remains
in the delivered module. The private helper is proved. The proof uses the existing
stated dependency `AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`,
whose own proof is still `sorry`; this delivery closes the upper hole from that dependency,
not the entire normalization theory. Local compilation succeeds without warnings.

## No longer needed

None: no original imports, dependency nodes, or modules were pruned. Both recorded proof
dependencies are used, with maximal contraction supplied by its Mathlib match. The bundled
dependency's spectral surjectivity and finite residue-field extension conclusions are not
used; its Dedekindness, dimension-one and finite-fibre conclusions are used. Trial explicit
imports of `Mathlib.RingTheory.Ideal.GoingUp` and
`Mathlib.RingTheory.Spectrum.Maximal.Basic` were unnecessary through the existing public
imports of the dependency and are absent from the delivery.

## Where the brief, the DAG or earlier work was wrong

The existing dependency takes its base ring and extension field in the same universe,
whereas this module allows `B : Type u` and `K : Type v`. Direct specialization to `B K K`
fails with an application type mismatch (`Type v` where `Type u` is required).
The proof uses the canonical `FractionRing B` and transports the result to `K`, preserving
both existing signatures and the unit route. No statement is disputed. No new nodes or
forced adaptations were needed.

## Second reading by Q1

1. **Interface: pass.** Read the entire delivered module and compared it with the
   repository using `diff -u`. The sole existing declaration,
   `integralClosure.semilocal_normalization_dim_one`, retains its signature byte for
   byte, including universes, all hypotheses, the four conclusions, and visibility.
   The imports are identical. The added helper is private and proved; no definition
   or existing statement changed. The existing theorem's explanatory proof docstring
   was expanded to describe the universe bridge, without changing its meaning.
2. **Proof and trust: pass, conditional on the existing dependency.** Independently
   compiled the module through `lcompile.py` without errors or warnings. Compiled a
   scratch copy with `#print axioms` for both the private helper and the public theorem:
   each uses exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The last comes from the already-open
   `AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`; neither
   delivered declaration contains a hole. No forbidden declaration or hollow
   definition is present. `FractionRing B`, the integral closure, and the algebra
   equivalence are actual Mathlib constructions, not arbitrary witnesses chosen
   from an unproved existence statement.
3. **Split statements: pass (none).** No split-off statements, new public theorems,
   new nodes, or added holes. The private helper is a proved same-universe reduction.
   Its finite sigma argument maps each maximal ideal to its contracted maximal ideal
   and underlying prime; equality of underlying primes proves injectivity. The
   hypotheses needed for maximal contraction are supplied by the integral-closure
   instance. A field base is excluded by `hdim`; the one-maximal-ideal case requires
   only the same finite-fibre argument. Transport is valid for arbitrary universes.
4. **Route and pruning: pass.** Read the bundled dependency and the maximal-contraction
   node's Mathlib match, and checked `dag/units/sk-thm-curveestimate.json` (`realized`
   statement `thm-sc-proper-cohomology`, no prescribed steps). The normalization route
   is preserved. Read Stacks [09IG](https://stacks.math.columbia.edu/tag/09IG) and the
   opening normalization clause of [09N2](https://stacks.math.columbia.edu/tag/09N2)
   online because the local literature files are absent. The base need not be normal:
   Loogle's three Dedekind integral-closure matches require `IsDedekindDomain B`, so
   they cannot replace the dependency. An independent LeanFinder search for finite
   maximal spectrum of normalization found only field and Dedekind characterization
   results, not this theorem. Also searched local Sheaf/upstream ring-theory sources
   and Mathlib integral-closure sources. All existing imports serve the statement or
   the used dependency; the dependency is already a plain proof-only import.
   Both old proof dependencies remain used, so `## No longer needed` is complete.
5. **DAG agreement: pass.** Compared the node JSON with the repository: only `proof`
   and `proof_origin` changed, with the original `proof_deps` retained. Step 1 describes
   the application at `FractionRing B`; step 2 describes the finite sigma injection
   and ring-equivalence transport; step 3 names the Mathlib fraction-ring theorem
   actually applied. The node agrees with the Lean proof. No new-node checks apply.

Second reading changed only this report, adding the independent review and its
verification evidence. No repair of the Lean proof or DAG was needed. One original
hole is closed and zero holes are added; the upstream normalization theorem remains
open, so this is not a claim that the public theorem is independent of `sorryAx`.
