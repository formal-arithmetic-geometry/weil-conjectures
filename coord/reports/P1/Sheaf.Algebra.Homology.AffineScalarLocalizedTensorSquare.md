## What changed

Repaired C5/G1 in `FlatIteratedScalarExtensionHomologySquare.lean` by replacing the
entire three-helper block, rather than renaming its declarations. The new private theorem
`iteratedHomologyData_comparison` compares the canonical cycles and homology maps for
`(h.map F).map G` and `h.map (F ⋙ G)`, for arbitrary left homology data `h`.
It cancels the common monic inclusion for cycles and the epic homology projection for homology.
The new `mapCyclesIso_hom_comp` and `mapHomologyIso_hom_comp` express the composition laws
for arbitrary categories with zero morphisms and zero-preserving functors `F`, `G`, and their
homology-preserving composite. Expanding the comparison isomorphisms using the same original
homology data cancels the intermediate isomorphism after applying `G`.

In `forgetAdjunct`, the homology lemma is specialized to `F = restrictScalars f` and
`G = forget₂ (ModuleCat E) AddCommGrpCat`. The composite has the same underlying objects
and maps as forgetting from `ModuleCat D`, so the required comparison is definitionally the
one in the existing goal. No existing library module was adapted to expose private helpers.
All public signatures and public imports from the returned delivery are preserved.
The iterated-square node now describes this argument.

The existing reduction of `exists_affineScalarLocalizedTensorSquare` is retained: first change
only final coefficients by the proved flat coefficient-model comparison, then apply the direct
localization obligation. The proof composes the source isomorphisms and the homology equations.
F/G1 is repaired by replacing the incorrect claims and checklist with the reading below.

## Proved and sorry left

The item's sole original hole, `AlgebraicGeometry.exists_affineScalarLocalizedTensorSquare`,
is closed by a compiling reduction. The delivery's sole remaining hole is
`AlgebraicGeometry.exists_affineDirectLocalizedTensorSquare`, node
`lem-pc-affine-direct-localized-tensor-square`. One hole is closed and one added: this is a
one-hole decomposition, not a net reduction of the sorry count.

`ModuleCat.exists_flatFinalCoefficientModelComparison`, node
`lem-pc-flat-final-coefficient-model-comparison`, and
`ModuleCat.flatIteratedScalarExtension_homology_square`, node
`lem-pc-flat-iterated-scalar-extension-homology-square`, have complete proofs.
Every private helper is proved. The repair adds no holes, definitions, or public declarations.
The direct-localization theorem, including model/universe transport, remains an obligation;
compilation of its statement is not a proof of that transport.

## No longer needed

The item's direct public import of
`Sheaf.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates` was replaced by
`Sheaf.Algebra.Homology.AffineBaseChangeTildeCoordinates` in the retained delivery.
This does not establish that the ordinary-stalk module leaves the targets' import closure:
`AffineDirectLocalizedTensorSquare` still imports `AffineStalkScalarExtensionCoordinates`,
which publicly imports the ordinary-stalk module. No global module pruning is claimed here.

The copied `map_homology_pi_comp`, `forget_restrict_cyclesIso_comp`, and
`forget_restrict_homologyIso_comp` helpers are removed in full. The repair uses no additional
imports. The remaining DAG dependencies are kept; no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous repair merely renamed helpers already present in `ScalarExtensionHomologySquare`.
Its report incorrectly called that a generalization and incorrectly claimed compliance with C5.
The reviewer was correct. This repair changes both the statements and proofs of the entire block:
its comparison laws contain arbitrary categories and functors, no rings or restriction functors,
and the specialization occurs only inside `forgetAdjunct`.

The previous second-reading checklist did not explain how the direct-localization statement
matches the localization lemmas or how its two derived-category universes are related.
The reading below supplies that explanation and explicitly leaves its Lean implementation
inside the named direct-localization obligation.

## Earlier second reading (a previous round; superseded)

Repair reading in this session; the independent second reader still reviews the delivery.
I read the affine part of the proof of [Stacks Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8),
from the identification of the cartesian affine square through the final displayed localization
identity. It identifies the global derived tensor cohomology localized at the fourth prime with
the cohomology obtained after localizing the input, base, and second factor. I also read
[Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6), including its K-flat computation and
change-of-rings argument; [Tag 01I9](https://stacks.math.columbia.edu/tag/01I9), both affine
pullback/restriction assertions; [Tag 00HD](https://stacks.math.columbia.edu/tag/00HD), its
flat tensor criterion and exactness argument; and
[Tag 05G3](https://stacks.math.columbia.edu/tag/05G3), Lemma 10.14.3 and its explicit
extension/restriction adjunction formulas.
These passages supply the mathematical route, not a pre-existing Lean proof of the new square.

I read the signatures and proofs of `derivedTensor_first_localization_models` and
`derivedTensor_base_second_localization_models`, the fields of
`BaseDerivedTensorCohomologyModel`, `exists_affineStalkScalarExtensionCoordinates`, and
`SingleComplexBaseChange`'s stalk algebras, tensor map, `cohomologyModel`, and `tensorComplex`.
For the direct obligation, write `Aq = O_{Spec A,g' p}`, `Rp = O_{Spec R,f(g' p)}`,
`Bp = O_{Spec R',f' p}`, and `D = O_{Spec A',p}`. The rings localize at the contracted
primes. `hφg'` and `hφf'` identify the two inclusions into the fourth ring;
`sq` and stalk-map naturality give their common base map and the required scalar towers.
The composite algebra on `D` is exactly the supplied algebra on `A ⊗[R] R'` followed by
`κ`. These compatibilities must be furnished to the localization declarations, not assumed
from type inference.

Apply the first-factor declaration with `B = R'`, `Q = M`, and the localization
`A → Aq`. Its source is `D ⊗_{A ⊗[R] R'} n.cohomology i`, precisely `U` in the direct
obligation. Its target uses a model of `Aq ⊗_A M` over the unchanged base and second factor.
Apply the base/second-factor declaration with its first algebra now `Aq`, base `R`, second
factor `R'`, and localizations `R → Rp`, `R' → Bp`. Localization gives the needed
`Rp`-action on `Aq`; the compatible contracted primes give the scalar towers.
Choose a common intermediate universal model for the two applications.
Both declarations conclude a D-linear source isomorphism and a square for
`localizedComparison`, with a chain isomorphism fixed on pure tensors. Composing these
squares gives `a ≫ H(tau) = e.hom ≫ l` after the termwise stalk identification.
The stalk-coordinate theorem sends `1 ⊗ x` to its germ, matching the direct obligation's
formula. D-linearity extends that formula from coefficient 1 to every coefficient, so
`ExtendScalars.hom_ext` identifies any supplied `tau` with the canonical map. Neither
localization declaration assumes that `M` is K-flat over `R`. All ordinary homology targets
in this obligation are already computed over `D`; extension of ordinary A'-cohomology is
handled only by the separate flat final-coefficient theorem.

There is a genuine universe transport to do: the two localization declarations use a common
`HasDerivedCategory.{w}` universe, the supplied model uses `wM`, and the fixed stalk model
uses `HasDerivedCategory.standard` at universe `u`. I read Mathlib's
`DerivedCategory/Basic.lean` definitions of `HasDerivedCategory.standard`, `Q`, and `Qh`,
and `CategoryTheory/Localization/Predicate.lean`'s `equivalenceFromModel`,
`qCompEquivalenceFromModelFunctorIso`, and `compEquivalenceFromModelInverseIso`.
For each original ring, its supplied and standard derived categories localize the same
complex category at quasi-isomorphisms. Compose their equivalences with the constructed
localization to obtain an equivalence intertwining `Q`, and hence `Qh` via
`quotientCompQhIso`. Transport `n.derived` by the inverse equivalence at `R` and the forward
equivalence at `R'`, and conjugate its counit by these intertwining isomorphisms. The
universal counit property is preserved by equivalence. Homology descends from the same
complex homology functor, so its localization factorization transports `cohomologyIso`.
Naturality at multiplication by `a`, together with `cohomologyIso_smul`, preserves the
full tensor-algebra action; `comparison_eq` and `localized_eq` preserve the comparison.
The coefficient cohomology modules and final D-module square do not require identifying
the derived categories by equality. One can then use the localization lemmas with standard
instances for every ring, and transport the localized input by the termwise stalk iso to
compare with the fixed `cohomologyModel` through counit-compatible model uniqueness.
These steps explain the remaining obligation; this delivery does not claim to formalize them.

I checked edge cases in the statements and proofs: zero complexes give zero comparison
maps; identity localizations leave only model-identification and tensor-associativity maps;
a zero fourth ring has no prime, making the affine assertion vacuous. In the generic
coefficient lemmas a zero final ring still gives zero tensor modules and the unit equations
remain valid. With `k` the identity, the iterated square reduces to naturality. Only `k`
is required to be flat; no flatness of `c`, `d`, or the original input over the base is added.

For the duplicate-helper repair I compared the old block with
`ScalarExtensionHomologySquare.lean:26–73`, then read each new helper's complete proof.
The data comparison works with arbitrary `h`: cancellation of the mapped kernel inclusion
proves the cycles equality; the homology-projection identity and its epimorphism prove the
homology equality. The two functor-composition lemmas cancel the intermediate canonical
isomorphisms after applying `G`. The specialized call in `forgetAdjunct` supplies restriction
and forgetting and uses their composite's definitional equality with forgetting from `D`.
This is a mathematical generalization, rather than a rename or an attempt to expose another
module's private declarations. All four delivered modules are checked in import order.

## New nodes

No new nodes are introduced by this repair. The retained delivery adds
`lem-pc-affine-direct-localized-tensor-square` for its one remaining obligation,
`lem-pc-flat-final-coefficient-model-comparison` for the proved coefficient-model transport,
and `lem-pc-flat-iterated-scalar-extension-homology-square` for the proved iterated square.
The last node's proof and proof origin are updated to describe the general composition repair.
The retained import change record is
`coord/changes/AffineScalarLocalizedTensorSquare-imports.md`.

## Second reading by P1

1. **Statements and accidental changes.** I diffed the delivered item against the repository
   version. The target theorem signature and all existing declarations are unchanged; the
   import change is recorded in `coord/changes/AffineScalarLocalizedTensorSquare-imports.md`.
   The added helper modules contain the new declarations listed above, with their matching
   DAG nodes.
2. **Compilation and axioms.** I compiled all four delivered modules in import order with
   `lcompile.py`; they compile cleanly. A source scan found no forbidden commands and the
   only remaining `sorry` is the named direct-localization obligation. The completed
   declarations use only the permitted foundational axioms (the delivery preflight checks
   this with its axiom probe).
3. **New statements.** The flat final-coefficient comparison and iterated homology square
   are true, strictly intermediate statements: they express model uniqueness and exact
   scalar-extension naturality, and are stronger only in the explicit generality needed by
   the target proof. The direct-localization theorem remains a named, sourced split node;
   it is not hidden in a definition or used to restate the target.
4. **Pruning and route.** The proof uses the retained coefficient-model and direct-localization
   dependencies, and keeps the unit route. The ordinary-stalk public import is replaced by
   the base-change coordinates import; the removed duplicate private helpers and their
   dependencies are no longer used. No target-closure pruning is claimed for the ordinary
   stalk module because the direct-localization dependency still reaches it.
5. **DAG agreement.** I checked the target and three auxiliary node records against the
   declarations and proof calls. Their `proof`, `proof_deps`, and `proof_origin` fields match
   the implemented route, and the direct-localization node documents the unresolved
   universe/model transport obligation.

I changed only the report in this second reading: I added this explicit five-point review
section required by the stage-3 delivery contract. No Lean proof or statement was altered.
