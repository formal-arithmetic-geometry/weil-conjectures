## What changed

Marked the two unconditional tensor-completeness theorems in
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral`
`STATEMENT-DISPUTED`, with the graph/zero-section counterexample explained
at each declaration and in detail below. No declaration signature, proof body, attribute, definition, or import
changed. This is a mathematical dispute delivery, not a proof or decomposition.

The coefficient category is sheaves of discrete modules on the small etale site. Its derived
completeness predicate is not the completed pro-etale tensor product used in the current DAG.
Replacing one by the other would change the statements. The source-library boundary prevents
silently making that replacement or adding the missing completeness hypotheses.

Validation uses `lcompile.py` through `deliver3.py`, which also probes the module and its
existing axiom dependencies. The first single-file attempt stopped while rebuilding imported
`ProjectionFormula.Torsion` at 60 seconds. A temporary profiling copy of that dependency then
compiled in 33.8 seconds; it was removed and is not part of this delivery. No timeout limit
was changed and no profiling option is retained.

## Proved and sorry left

Closed: zero of four holes. Added: zero holes. Split off: zero.

The existing holes retained on the current post-sync source are:

- `AlgebraicGeometry.Etale.derivedCompleteIntegral_derivedTensor_rightDerivedLowerShriek`:
  STATEMENT-DISPUTED: false even with its properness hypothesis.
- `AlgebraicGeometry.Etale.derivedCompleteIntegral_derivedTensor_leftDerivedUpperStar`:
  STATEMENT-DISPUTED: false for the same example, with a proper closed immersion.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMap_of_derivedCompleteIntegral`:
  unchanged and unproved on the current post-sync source.
- `AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral`:
  unchanged and unproved. The module's complete-source/complete-target conditional reconstruction
  is already proved; the remaining general formula cannot be obtained by applying it to the
  two false completeness assertions. No claim is made here that this third statement is false.

None of these declarations currently has a `lean` attachment in `dag/nodes`. Searching all
node records for the module and the two tensor-completeness declaration names found none.
Their existing blueprint mentions refer to `thm-sf-pf-adic` and `sk-thm-sf-pf-adic`; the current
nodes now concern different completed pro-etale objects. No incorrect attachment was added.

## No longer needed

No imports, nodes, modules, or declarations removed. No pruning claimed. The source-library
module and all of its existing declarations remain present.

The short-route searches were LeanFinder for projection formulas with bounded constructible
finite-Tor inputs, Loogle for `HasProjectionFormula`, and grep/ripgrep for projection and
completeness APIs. Mathlib search supplied no matching result. The library's dualizable
projection formula has an extra hypothesis that constructible finite-Tor complexes do not
satisfy in general. The rational-stage formula imports this item and is not an independent
route. The pre-sync finite-reduction proof was in this item, but its imported torsion-reduction
modules were removed by the concurrent upstream sync. Reduction is conservative only on
complete objects, which is precisely the failed step of the completeness argument here.

## Where the brief, the DAG or earlier work was wrong

The brief asks for proofs of two false completeness statements. The initial source module
already documented the counterexample in its implementation notes; the concurrent upstream
sync replaced that module by an older version without those notes.
The first theorem's docstring suggests properness repairs the issue; the module's own
counterexample has proper f, so it does not. The source-versus-pro-etale mismatch is also
recorded in the earlier stage-1 reports for `thm-sf-pf-adic` and
`det-thm-sf-pf-adic-projection`.

Here is the counterexample in full. Let k be algebraically closed of characteristic zero,
Omega an algebraic closure of k(t), and R the integral closure of k[t]_(t) in Omega. Set
X = Spec R. The local rings of R are strictly henselian, and every open subset of X is
irreducible. Thus the small etale topos agrees with its Zariski topos, and the constant
O_E-sheaf K has derived sections O_E on every nonempty open: it is derived complete.
It is bounded constructible and flat. The fiber C = V(t) is an infinite profinite space
(the extensions of the t-adic valuation to Omega).

Put Y = A1_X, let f: X -> Y be the graph of t, and let i: X -> Y be the zero section.
Both are closed immersions. Let L = i_* O_E,X. Closed direct image is exact and preserves
derived completeness. The stratification by the zero section and its principal open
complement shows L is constructible; its geometric stalks are O_E or zero, so it is flat.
Both inputs therefore have all the stated hypotheses, including finite Tor amplitude [0,0].

The tensor K tensor Lf^* L is the closed direct image of O_E,C to X. The source
Rf_! K tensor L is its closed direct image to Y. Their global sections are the locally
constant functions C -> O_E. This module is torsion free but not adically complete: its
adic completion contains continuous O_E-valued functions with infinite image, whereas a
locally constant function from a compact space to the discrete O_E has finite image.
Derived global sections preserve derived completeness. Hence neither tensor object in the
two disputed conclusions is derived complete. This uses no failure of properness: f is
already a closed immersion.

I preserved the false source signatures and did not replace their holes by new false lemmas,
weakened claims, or proofs using an unrelated inconsistency. A subsequent authorized interface
repair must distinguish discrete etale operations from completed pro-etale operations, or
require the tensor completeness used by the already-proved conditional formula. Existing
proper and rational-stage consumers also rely on the two disputed assertions.

The first delivery attempt pushed nothing: source-presence checking detected that the
concurrent sync had removed `ProjectionFormula.TorsionReduction`. The sandbox was rebased
onto the current source, keeping only the two dispute annotations. No removed dependency
or pre-sync proof was restored. The updated source has four holes rather than three.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
