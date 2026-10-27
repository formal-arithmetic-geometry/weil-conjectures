## What changed

Filled `WeilConjectures.PurityConventions.rootTorsor_represented` using the existing
Kummer-cover point equivalence and units-to-ring-roots equivalence, including naturality
under every etale restriction. Added private, proved helpers for the Gamma-Spec
precomposition calculation and the lifting-torsor sections.

Filled `WeilConjectures.PurityConventions.finiteLineTransition_existsUnique` using the
finite clause of `Scheme.tateTwist_finite_locallyFree`. Unique quotient scalar maps
identify the coefficient actions. A private, proved additive-sheaf extensionality lemma
uses the sheafification adjunction and tensor induction, proving uniqueness among all
abelian-sheaf isomorphisms with the specified formula.

Added only the private proof import
`WeilConjectures.EtaleCohomology.TateTwist.KummerClassTorsor`. Updated the item's DAG
proof and dependency union. Every public declaration signature, definition body,
public import, and existing proof is retained. No other module is changed.

## Proved and sorry left

Closed 2 of the 7 original holes, with no holes added and no split-off statements:
`WeilConjectures.PurityConventions.rootTorsor_represented` and
`WeilConjectures.PurityConventions.finiteLineTransition_existsUnique`.

Five existing holes remain, all attached to `sk-def-purity-conv`:

- `WeilConjectures.PurityConventions.coefficientComparison_existsUnique`
- `WeilConjectures.PurityConventions.finiteLinePullback_existsUnique`
- `WeilConjectures.PurityConventions.kummer_baseChange`
- `WeilConjectures.PurityConventions.kummer_exponent_independent`
- `WeilConjectures.PurityConventions.regularNormalBundle`

Server single-file compilation accepted both completed proofs in 54.4 seconds.
Profiling options and the reported style warning were removed before delivery; the
delivery runs the final compile and declaration-axiom probe.

The positivity argument includes every r, including r=0; the transition also includes
r=n. Tensor induction requires neither nontrivial A nor freeness over the residue ring.
The root equivalences apply to every scheme, including the empty scheme.

## No longer needed

None. No import, module, declaration, node, or unit step is withdrawn. The transition
uses the already imported finite local-freeness clause directly; it does not import
the larger `ProEtaleTateTwistConstructions` module merely to obtain `spFiniteKummer`.
All existing dependencies remain needed by the retained constructions or open properties.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The previous DAG recorded only the four proofs
already completed by E7 and explicitly retained the other holes. This delivery records
the two additional arguments. The regular normal-bundle theorem in `PurityNormalBundle`
requires finite-type field data, so it cannot directly discharge the unrestricted
`regularNormalBundle` statement here; that existing hole is retained unchanged.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
