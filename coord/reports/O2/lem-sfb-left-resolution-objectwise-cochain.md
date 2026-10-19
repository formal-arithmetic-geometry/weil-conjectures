Files written:

- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-objectwise-cochain.json` — item, split with six proof steps.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-chain-complex-functor.json` — statement, Mathlib leaf (`CategoryTheory.Abelian.LeftResolution.chainComplexFunctor`).
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-chain-exactness.json` — statement, Mathlib leaf (`CategoryTheory.Abelian.LeftResolution.exactAt_map_chainComplex_succ`).
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-complex-extension.json` — statement, Mathlib leaf (`CochainComplex.instIsStrictlyLEExtendNatIntEmbeddingDownNatOfNat`).
- `citations.json` — verbatim statement quotes for every cited node at every proof step.

Attachments: none. The previously suggested project declarations are backed by the slopmaster2 sorry map, so they are not attachments.

WANTED: none.

The imported item had no proof split. I retained its mathematical statement and made the underlying chain-resolution construction, positive-degree exactness, and extension-by-zero support explicit as Mathlib leaves. The item’s `lem-sfb-left-resolution-reduced-api` dependency is used for the definition of a left-resolution pair and its epimorphic components; no claim that the reduced construction is needed for this already-given datum is made.

## Not duplicates

`lem-sfb-left-resolution-chain-complex-functor` vs `lem-sfb-left-resolution-reduced-api`: the former constructs the chain-complex functor and differential formulas, while the latter states the reduced left-resolution existence and zero-preservation result.

`lem-sfb-left-resolution-chain-exactness` vs `lem-sfb-left-resolution-bicomplex-total-exists`: the former is exactness of one termwise image chain complex at positive degrees; the latter concerns support and existence of diagonal totals for a bicomplex.

`lem-sfb-left-resolution-complex-extension` vs `lem-sfb-left-resolution-bounded-minus`: the former is the generic Mathlib extension-by-zero and strict-support API; the latter assembles a functorial bounded-above resolution and its augmentation.

## Review by N2

I read the item source `WeilConjectures/FromJoel/Algebra/Homology/LeftResolution/Basic.lean`, lines 30–170, and the corresponding Mathlib sources `Algebra/Homology/LeftResolution/Basic.lean` (the `LeftResolution` structure, `chainComplex`, `chainComplexMap`, `chainComplexFunctor`, differential formulas, and `exactAt_map_chainComplex_succ`) and `Algebra/Homology/Embedding/Extend.lean` together with `Embedding/CochainComplex.lean` (extension by zero and strict support). I also read the existing reduced-api node before using it.

Step 1 uses only the reduced-api statement that a left resolution is a pair `(F, π)` with epimorphic components; I checked that the item’s full-faithfulness and abelian hypotheses match Mathlib’s typeclass assumptions. Step 2 uses the chain-complex leaf for the objectwise terms and functorial kernel maps. Step 3 uses that same statement plus the extension leaf; the index conversion `n ↦ -n` gives exactly the displayed negative-degree terms and zero positive degrees. Step 4 uses the chain differential formula and the kernel condition to check that `π_X` defines the augmentation and that naturality is inherited from `π.naturality` and kernel maps. Step 5 uses the positive-degree exactness leaf for all negative cochain degrees, the degree-zero kernel/epimorphism argument from the source, and the extension support leaf for positive degrees. Step 6 uses strict support and the fact that a functor preserves zero objects.

I tested the edge cases conceptually at `X=0` (all displayed terms and the augmentation are zero), at a complex concentrated in degree zero (the degree-zero short complex is the only nontrivial one), and at the first negative degree (the `ker π_X` term and the kernel factorization agree). No statement was changed, no SGA source was used, and no long proof step hides a separate unrecorded lemma.

What remains unfinished: none in the split; the required dry run is the remaining delivery check.
