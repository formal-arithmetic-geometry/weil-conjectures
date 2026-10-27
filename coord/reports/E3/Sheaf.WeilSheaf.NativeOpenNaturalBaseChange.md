## What changed

Proved `AlgebraicGeometry.nativeWeilOpenNaturalBaseChange` in the assigned module,
with its original statement, universes, assumptions, visibility, and docstring unchanged.
No other existing Lean module was changed. Updated the item's DAG proof, proof dependencies,
and proof origin to describe the implementation.

The proof follows the adjoint-uniqueness argument of Stacks Tag 03S6
(`etale-cohomology.tex`, `lemma-shriek-base-change`, lines 11508–11516).
The existing native open adjunction is assembled with
`IsoAlgebra.mapOfNatIsoLeftAdjunction` and the actual adic Frobenius mate and comparison.
Taking the inverse mate of the native direct-image square produces the restriction/direct-image
comparison inside the native hearts. The private carrier calculations identify it with
`ProEtale.adicBaseChangeMap`; weakly etale base change on the geometric fibres and the conservative
forgetful functor make it invertible. Transporting the composite adjunction across this comparison
and applying `Adjunction.leftAdjointUniq` proves the heart-level extension/pullback isomorphism.
`Functor.mapDerivedCategoryNatIso` and `Functor.mapDerivedCategoryCompIso` then give the requested
isomorphism on all unbounded ordinary derived objects.

The proved private native adjunction, mate-component formula, and carrier calculations follow
those in `Sheaf.WeilSheaf.NativeOpenProperInterchange`. Those helpers are private and cannot be
imported; its proper/open theorem is neither used nor imported. The actual public composition,
congruence, and carrier APIs are used from `WeilConjectures.WeilSheaf.IsotypicPullback`.
The three proof imports are `IsoAlgebraLeftAdjunction`, `DirectImageRestriction`, and
`IsotypicPullback` under their existing source-library paths. The latter two provide the
geometric-fibre pullback-square lemma, adic base change, and native square/carrier API.
The derived comparisons are already exposed through these imports; their redundant explicit
`ExactFunctor` import was removed.

The first complete proof compiled through `lcompile.py` in 20.9 seconds, exit 0, without compiler
messages. The first delivery's probe compile took 73.4 seconds and correctly refused to push.
Profiling found the carrier-comparison simplification took about eight seconds, while a profiled
standalone compile completed in 17.5 seconds. The derived construction is now packaged in the
proved private `nativeOpenDerivedBaseChangeIso`; the public theorem applies that comparison.
The refactored module together with the exact delivery axiom probe compiled in a scratch
profiling copy in 19.0 seconds, with `SHEAF-PROBED 3`, no forbidden-axiom messages, and no
remaining-hole messages. The profiler and probe's own long-line warnings belong only to that
scratch copy. No profiler, trace, or altered transparency option is present in the delivered file.
The final version is checked again by `deliver3.py`, including its declaration/axiom probe. This is a change to proofs and private helpers only, so no consumer interface adaptation
or change record is required. No quasi-compactness of the upper open, boundedness,
constructibility, properness, or absolute separatedness assumption was added.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.nativeWeilOpenNaturalBaseChange`
(node `lem-sf-native-weil-open-natural-base-change`).

Added 0 holes. The assigned module has 0 remaining `sorry`s. Every new private helper is proved;
no split-off statements, axioms, definitions with holes, or additional modules were introduced.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.Adic.Constructible`.
- `WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion`.
- `Sheaf.CategoryTheory.ExactDerivedComposition`.

The following declared proof dependencies are unnecessary for this proof and were removed from
the item's `proof_deps` and proof steps:

- `lem-weil-proetale-weakly-etale-localization`: the native adic base-change theorem already
  implements the needed restriction comparison; no separate equivalence of sliced sites is used.
- `lem-weil-pbc-localize-ringed-site-morphism`: no general ringed-site comparison is instantiated.
- `lem-pur-site-restriction-module-adjunction-exact`: the actual native extension adjunction is
  obtained from the existing adic adjoint triple, with its specified Frobenius actions.
- `lem-weil-pbc-ringed-topoi-module-adjunction`: the existing native pullback/direct-image
  adjunction supplies exactly the needed functors.
- `lem-weil-pbc-mate-pasting`: the mate is constructed inside the native categories; its
  Frobenius compatibility is part of its type, and the carrier formula is proved directly.

The exactness and derived-comparison nodes are retained: their existing source-library
instances and comparison definitions are used directly. The public statement imports are
unchanged. These are removals from this item's direct imports and planned dependency route;
no source-library declaration or other parent's dependencies were withdrawn, and no claim is
made that a removed module leaves the targets' entire import closure.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned general ringed-site localization instantiation and
separate Frobenius compatibility proof can be replaced by already proved native adjunctions,
the native direct-image square, and the existing adic weakly etale base-change theorem.
The node now records this shorter route. The unit record `sk-thm-sf-package` has empty
`realized.statement` and `realized.steps` entries; no unit-level statement or route was removed.

Local searches read the source APIs and their signatures before assembling the proof.
The required `msearch.py` calls returned eight generic restriction/pullback hits for the
LeanFinder query and zero hits for both the Loogle `"mapOfNatIso"` query and the grep query
`openImmersionLowerShriek.*[Bb]ase|[Bb]ase.*openImmersionLowerShriek`.
The usable native APIs were found with `rg` in the source library and the existing
`NativeOpenProperInterchange` implementation. No unavailable search was treated as a result.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
