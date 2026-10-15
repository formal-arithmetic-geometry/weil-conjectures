## What changed

Proved `AlgebraicGeometry.ProEtale.profinite_test_object_functor` in
`lean/Sheaf/Paper/ProfiniteTestObjectFunctor.lean`, with its original public signature,
visibility, public imports, and docstring unchanged. Every new helper is private and proved.
Updated the corresponding DAG node's `proof`, `proof_deps`, and `proof_origin` to describe
this proof rather than the original affine-chart construction.

The shorter route uses the already defined base-change functor. Its existing source-library
finite-limit instance handles the first clause. Evaluation at a prime of the coefficient
ring proves joint surjectivity of the spectrum maps. Their weak etaleness gives flatness,
and their affineness gives quasi-compactness, yielding finite fpqc covers, then relative
covers by base change. This also proves covering preservation over `Spec Z` locally rather
than invoking the source's unproved covering-preservation lemma. Continuity and the
subcanonical/extensive-sheaf characterization give finite coproduct preservation. Explicit
point coproducts give the natural comparison on finite sets. Finally, factorization of
locally constant functions and injectivity of pullback along a surjection give the filtered
ring colimit; `Spec` and base change give the required cofiltered limit.

The new proof uses the profinite effective-epimorphism, filtered-ring-colimit, Yoneda,
connected-slice-limit, coherent/extensive-site, and pro-etale base-change APIs already
exported by the existing public imports. Trial compilation confirmed that no new import is
needed; only the two original proof imports for cofiltered profinite limits and the locally
constant spectrum theorem remain. No public API or target statement changed. No other module was adapted.
Compilation through `lcompile.py` succeeds without diagnostics in approximately 2.8 seconds.
The empty coproduct/family cases are included by the general finite-shape and cover proofs;
no inhabitedness, nonemptiness, or qcqs assumption on `X` was added.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.profinite_test_object_functor`
(blueprint: `lem-weil-pbc-profinite-test-object-functor`). All six conjuncts are proved.
There are no remaining `sorry`s in the item and no new holes or split-off statements.
This is a proof from existing library declarations, not a decomposition adding new holes.

The proof still inherits the existing source-library obligations
`AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme` and
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_profiniteToProEt` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`. They were already in the item's
public import closure; this delivery does not prove them or claim that the resulting theorem
has no transitive `sorryAx`. The proof of covering preservation in this delivery avoids using
`AlgebraicGeometry.ProEtale.coverPreserving_profiniteToProEt` and its continuity instance.
All helper constructions are explicit, or use uniqueness of limits/colimits/terminal objects.
No arbitrary object is chosen from an unproved existence theorem.

## No longer needed

Removed these original proof-only imports:

- `Mathlib.Topology.Separation.Profinite`.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `Mathlib.AlgebraicGeometry.Gluing`.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` (its API is available transitively).
- `Mathlib.AlgebraicGeometry.Morphisms.Affine` (its API is available transitively).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat` (the API remains available transitively).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc` (the API remains available transitively).

Removed these direct proof dependencies from this item's node:

- `lem-weil-pbc-profinite-clopen-basis`.
- `lem-weil-pbc-finite-affine-coproduct-spectrum`.
- `lem-weil-pbc-limit-affine-transition-core`.
- `pqf-lem-affine-local-target`.
- `lem-weil-pbc-limit-cone-affine-projections-opens`.
- `lem-weil-pbc-scheme-morphism-gluing`.
- `lem-weil-pbc-tychonoff-product-quasi-compact`.
- `lem-weil-pbc-affine-open-stalk-localization`.

Their mapped modules are respectively `Mathlib.Topology.Separation.Profinite`,
`Mathlib.AlgebraicGeometry.Limits` (the finite coproduct construction),
`Sheaf.AlgebraicGeometry.LimitAffineTransition`,
`Mathlib.AlgebraicGeometry.Morphisms.Affine`,
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`, `Mathlib.AlgebraicGeometry.Gluing`,
`Mathlib.Topology.Compactness.Compact`, and
`Mathlib.AlgebraicGeometry.AffineScheme` (with `OpenImmersion` and `Scheme`).
These are no longer direct mathematical dependencies of this proof, rather than claims
that the entire library or the inherited finite-limit/weak-etaleness proofs can omit them.
`GammaSpecAdjunction` and `Morphisms.Affine` supply other facts actually used, through the
existing public imports; their explicit imports were redundant.
The sole removed Sheaf statement-module import is `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
No blueprint unit statement or realized unit proof step was removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original DAG route was longer than necessary for the
existing Lean interface: `profiniteToProEtOf` already is base change of the concrete spectrum
functor, and the source already states its finite-limit and weak-etaleness inputs. Rebuilding
an arbitrary affine-transition limit or gluing scheme maps is unnecessary for this item.
The updated DAG proof explicitly records the two inherited source obligations; their exact
Lean names occur in source-audit metadata elsewhere in the DAG, but neither has an individual
node attachment under that name. This delivery does not conceal those obligations with a
new statement or attempt to cite this item's parent (which would introduce a dependency cycle).

The original theorem docstring's ten-step plan is preserved as requested by the proof-editing
contract; the node's updated six-step proof is the route implemented here. The binding unit
`sk-thm-properbasechange` and its `realized` fields are unchanged.

## Second reading by F1

1. **Interface preservation.** Compared the delivered module with the repository version. The
   theorem signature, visibility, declaration name, docstring, and all public imports needed by
   its interface are unchanged; only proof-only imports and the proof body changed. Verdict: pass.
2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds without diagnostics.
   The item contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or
   `debug.skipKernelTC`. Every helper is private and fully proved. Verdict: pass.
3. **Statements and nodes.** Checked the theorem and each private helper against the implemented
   argument, and checked the updated node's `proof`, `proof_deps`, and `proof_origin`. No new
   public statement or split-off node was added, and no statement was weakened. Verdict: pass.
4. **Shortest route and pruning.** The proof directly uses the existing concrete base-change
   functor and its finite-limit input, proves the covering and coproduct clauses through the
   available coherent/extensive-site APIs, and removes the obsolete affine-chart and gluing
   imports and dependencies listed above. The unit statement and its realized route remain
   unchanged. Verdict: pass.
5. **Axioms and inherited obligations.** The new theorem introduces no local axioms or hollow
   definitions. Its transitive `sorryAx` sources are the pre-existing source-library declarations
   `weaklyEtale_toSpecZ_profiniteToScheme` and
   `preservesFiniteLimits_profiniteToProEt`, explicitly recorded above; this delivery neither
   hides nor adds such obligations. Verdict: pass.

I changed only this report section after the initial delivery attempt; the module and DAG proof
metadata remain as described above.
