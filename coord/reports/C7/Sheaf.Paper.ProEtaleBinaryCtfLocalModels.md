## What changed

Completed `AlgebraicGeometry.Scheme.proEtale_binary_ctf_of_local_models` in
`Sheaf.Paper.ProEtaleBinaryCtfLocalModels`, with its statement unchanged. Only this
existing Lean module and its own DAG node are changed. No public definition,
instance, attribute or import is changed; all added imports are private proof imports.

The proof applies the existing proved `finiteCoverCTFLocality` to the two opens.
Proved private helpers connect the two constructibility encodings: finite models
are equivalent to local constancy with finite geometric stalks, including the
positive-stratum convention on an empty scheme. The module-sheafification unit
and the canonical realization counit identify the inverse realization with
restriction to constant scalars; exactness then identifies homology.

Other proved private helpers use `RingedDerivedNative.tensorIso` to compare any
allowed K-flat representative with the native derived tensor. This identifies the
original all-representatives Tor predicate with the chosen-tensor test required
by finite-cover locality, in both directions. The supplied model isomorphisms
transport all local properties. A separate open-cover zero-detection argument
retains the cohomological interval `[a,b]`, independently of `[s,t]`.

The local finite-support argument works even for `a > b`. The ordered Tor
interval is obtained from a local hypothesis, including on an empty open. The
constructibility conversion explicitly handles the empty scheme with its identity
stratum and empty trivializing cover. No nonzero-ring hypothesis is used.

Validation: the private comparisons compiled in 6.4 seconds. The first assembly
check found the need to import `ProEtaleConstantModulePullbackEncoding` directly;
that proof import was added. The completed module then compiled without errors
or warnings in 10.2 seconds using `lcompile.py`. The delivery tool also runs its
per-declaration axiom probe.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.proEtale_binary_ctf_of_local_models`
(node `lem-sp-proetale-binary-ctf-local-models`).

Added 0 holes; 0 `sorry` statements remain in the item or are added elsewhere.
Every new private helper is proved. This is a proof from existing declarations,
not a decomposition into new obligations. The existing library dependencies are
used with their current proofs and axiom dependencies.

## No longer needed

No existing import was removed. The existing public imports are retained as the
module's interface; in particular `SmoothPurityNormalizedTowers` supplies the
small-site sheafification instances used by the fixed-module presentation.
Every added proof import is used.

The following old planned dependencies are no longer direct proof dependencies:

- `lem-weil-proetale-weakly-etale-localization`
  (`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`), and
  `lem-pur-site-restriction-module-adjunction-exact`
  (`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`): existing exact
  pullback/homology and open-cover detection supply the needed consequences.
- `def-weil-proetale-inverse-image`
  (`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`) and
  `lem-sfb-geometric-inverse-image-constant-module`
  (`Sheaf.SixFunctors.GeometricInverseImageConstantModule`): the proved
  finite-cover locality and fixed-module finite-model comparisons supply the
  constructibility step without reconstructing inverse images of constants.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
  (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`):
  `finiteCoverCTFLocality` already proves the tensor locality step; the item only
  needs the native tensor comparison to translate the Tor predicates.
- `def-weil-proetale-constructible-sheaf` is retained as a statement dependency;
  the proof now records the specific encoding and finite-model results it uses.

These removals are from this node's direct proof plan. Several remain transitive
dependencies of the reused theorems. No whole module is withdrawn or claimed to
have left the target closure. The smooth-purity unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The old proof plan described
reconstructing zero detection, finite stratifications and tensor pullback at this
node. Those arguments now exist in proved library declarations, so this delivery
reuses them and supplies the missing encoding and Tor-predicate glue. The
independent cohomological and Tor intervals are preserved explicitly.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
