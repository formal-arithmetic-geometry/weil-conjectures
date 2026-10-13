## What changed

Preserved the signature and docstring of
`RingTensorCohomology.affineTensorCohomology_localization`. Replaced its hole by a
three-part reduction. The new localization-square module supplies D-linear component
isomorphisms, two naturality equations, and a componentwise comparison equation.
The main proof constructs `alphaIso` and `betaIso` with `NatIso.ofComponents` and
uses extensionality to prove the natural-transformation square. Independently it
obtains flatness of the specified coefficient map and applies the general ordinary
target flat-extension theorem to the local lift `Tl`. All three parts are needed.

New modules:
- `Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationSquare`;
- `Sheaf.Algebra.Homology.AffineTensorLocalizationFlat`;
- `Sheaf.Algebra.Homology.AffineTensorTargetFlatExtension`.

The algebra-only flatness module imports Mathlib ring-hom flatness directly and
does not import the project cohomology definitions. The ordinary target module
does not import prime-localization infrastructure.

Only proof-dependency imports change in the existing module. No existing signature,
visibility, definition, unit step, or target statement changes. The existing node's
proof route now records the actual assembly.

## Proved and sorry left

Closed the one original hole in
`RingTensorCohomology.affineTensorCohomology_localization`, conditional on the three
new named statements below. This is a decomposition, not a completed mathematical
proof: one hole closed, three added, net minus two holes in this delivery.

The delivery adds exactly these holes, each in its own module:
- `RingTensorCohomology.affineTensorCohomology_localization_square`, node
  `lem-pc-affine-tensor-cohomology-localization-square`;
- `RingTensorCohomology.affineTensorLocalization_flat`, node
  `lem-pc-affine-tensor-localization-flat`;
- `RingTensorCohomology.affineTensorTarget_flat_extension`, node
  `lem-pc-affine-tensor-target-flat-extension`.

Every remaining proof is exactly `by sorry`, in a public theorem with a source and
complete proof in words. There is no new definition or arbitrary chosen witness.
The component square omits the final local target identification. The flatness
statement involves only rings and coefficient maps. The flat target-extension
statement involves only one target lift, an arbitrary flat coefficient map, and
its A-generator equation; it has no primes, source lift, or comparison square.
These are strictly separate parts of the argument, not copies of the full target.

Edge checks: primes are not assumed to exist; zero rings therefore impose no
localization instance. Localization maps need not be injective. Identity
localizations give flat identity maps. Zero complexes have zero homology, and the
ordinary target assertion does not require flatness of B over R, boundedness, or
Tor independence. Compatibility with the A-algebra map is retained explicitly in
the ordinary target statement; otherwise its conclusion could use the wrong
scalar action.

## No longer needed

Removed the following direct imports from the original module:
- `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology`;
- `Mathlib.RingTheory.Localization.BaseChange`;
- `Mathlib.Algebra.Module.LocalizedModule.Exact`.

They remain dependencies of the new component-square and coefficient arguments.
No original dependency node or module is globally pruned: the new route still
needs `lem-pc-derived-tensor-localization-cohomology`,
`lem-weil-pbc-localization-tensor-product`, and
`lem-weil-pbc-localization-module-exact`. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was established. The planned localization theorem has a
pointwise balanced derived-model interface, not an interface for the prescribed
functor lifts in this item. Transport, identification of the localized resolution
with the chosen local functorial resolution, and the coefficient-map flatness
argument are substantial glue. The reduction states these missing interfaces
explicitly rather than assuming them silently.

The local checkout lacks the cited Stacks TeX files. The corresponding official
pages were read at https://stacks.math.columbia.edu/tag/0DJ8,
https://stacks.math.columbia.edu/tag/00DL, and
https://stacks.math.columbia.edu/tag/00CS. No repository literature list was changed
because this worker is restricted to its sandbox.

## New nodes

`lem-pc-affine-tensor-cohomology-localization-square` supplies componentwise
localization isomorphisms with naturality and compatibility with comparison,
using the existing balanced derived localization result and exact tensor
localization. Its new module is `AffineTensorCohomologyLocalizationSquare`.

`lem-pc-affine-tensor-localization-flat` isolates the algebraic fact that the
specified local coefficient map is a further localization, hence flat. Its
new module is `AffineTensorLocalizationFlat`.

`lem-pc-affine-tensor-target-flat-extension` isolates the ordinary target
identification after any flat coefficient extension. Its new module is
`AffineTensorTargetFlatExtension`. It follows from the ordinary balanced tensor
identification, uniqueness of the tensor-factor action, exact homology
comparison, and tensor associativity.

All three nodes retain the original chapter and unit and carry verbatim Lean
signatures, source references, proof steps, and three kinds of Mathlib search.
No change record is needed because no existing statement or definition changed.

## Second reading by E1

1. Compared the delivered localization-isomorphism module with the repository version. Existing declarations retain byte-for-byte signatures and visibility; only proof-dependency imports and the target proof body changed. Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all`. Compilation succeeds with no errors or warnings. The only remaining `sorry`s are the three named split theorems, each public and documented; no definition contains `sorry`, and no forbidden declaration form was introduced. Verdict: pass.
3. Checked the three split statements against their signatures, edge-case discussion, and repository search records. They are strictly smaller than the original target and do not duplicate it; their DAG nodes include source, proof, dependencies, and Lean records. Verdict: pass.
4. Checked the proof route from the target downward. The assembled `NatIso.ofComponents` and `NatTrans.ext` proof uses the localization square, coefficient flatness, and flat target-extension nodes. The removed imports are no longer directly needed, while the corresponding dependencies remain through the split modules. Verdict: pass.
5. Checked the node JSON files against the Lean declarations and proof dependencies. The original unit and chapter are retained, and the target node records the actual three-step assembly. Verdict: pass.

Changed only this report section during second reading; no Lean or DAG repairs were required.
