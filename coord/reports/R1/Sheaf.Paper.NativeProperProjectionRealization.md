## What changed

Replaced the body of AlgebraicGeometry.ProEtaleWeilSheaf.native_proper_projection_realization
by a complete assembly proof. Its theorem signature is unchanged. The original record's
resolution fields are factored into NativeProperProjectionModels; the original record
extends it and keeps the four projection fields verbatim. All mathematical data and
normalization equations are retained. The constructor now accepts the resolution
record as one parent field, and the new model module is a public import.
The resolution fields remain available by dot notation through the parent; the original
flat qualified projection constants are replaced by the model record projections.
The private projection_square helper proves the two actual projection-map
compatibility equations by transposition and cancellation of the specified isomorphisms.
The private inverse_tensor_square helper reverses the realization tensor square.
The private projection_naturality helper proves simultaneous naturality from the tensor
comparison and counit. The final proof transfers ordinary invertibility through the
conservative section-forgetful functor and uses NatIso.ofComponents.

Added NativeProperProjectionModels and OrdinaryProperProjectionInvertible as separate
modules. These isolate the original proof's resolution construction (Steps 1--4) and
ordinary projection-formula invertibility (Steps 6--7). They do not include a native
projection isomorphism or repackage the original conclusion. All model data are eliminated
inside the final theorem proof; no definition chooses data from an unproved existence theorem.
No adopted WeilConjectures source file or other existing module is changed. No existing
consumer imports the item in the current snapshot, so no consumer adaptation is needed.
The resolution-record factorization is documented in the change record. Local
irreducibility attributes keep the large cochain and localization comparison maps
behind their stated types during the proof, without changing their exported reducibility.

The proof cites native_closed_forgetful and the actual derived adjunction, tensor functors,
properCommonProjection and properOrdinaryProjection already in the library. It adds no copy
of a landed theorem. The generic private square helper allows arbitrary pullback/tensor
components and a specified normalized direct-image comparison, unlike the existing
projectionMate_square_of_tensor_coherence interface requiring a natural transformation
and its canonical mate. Its argument is the same formal adjunction calculation.

Validation: lcompile compiled NativeProperProjectionModels in 33.3 s and the final
NativeProperProjectionRealization in 33.1 s without warnings. The ordinary split module
compiled separately in 7.3 s. Every resolution field and every projection field was
checked textually against the original: their types and equations are retained verbatim.
No existing consumer imports the item, so no consumer changes are needed.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProEtaleWeilSheaf.native_proper_projection_realization
(lem-sf-native-proper-projection-realization). The item module has zero sorry.

Added two holes:

- AlgebraicGeometry.ProEtaleWeilSheaf.native_proper_projection_models
  (lem-sf-native-proper-projection-models), in NativeProperProjectionModels.
- AlgebraicGeometry.ProEtaleWeilSheaf.properOrdinaryProjection_isIso
  (lem-sf-ordinary-proper-projection-invertible), in OrdinaryProperProjectionInvertible.

This is a decomposition: one upper hole closed and two strictly smaller holes added,
net minus one when counting these three declarations. It is not a complete axiom-free proof of the proper projection formula.
The two projection equations, detection of native invertibility from the ordinary one,
and assembly and naturality are proved without additional holes.

## No longer needed

Removed these direct proof imports from the item:

- Sheaf.Paper.ExchangeProjectionSuppliedDomains
- Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
- Sheaf.Paper.FiniteTorAmplitudeSites
- Sheaf.Paper.NativeDerivedWeilTensorConstructible
- WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
- Sheaf.CategoryTheory.FixedPairDerivedForgetComparison
- Sheaf.Paper.LocallyFiniteCoefficientRingRealization
- WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate
- Sheaf.WeilSheaf.NativePullbackStarPreservation
- Sheaf.Algebra.Homology.RingedForgetTensorTransposition
- Sheaf.Paper.WeilFrobeniusActionResolutions
- Sheaf.Paper.ProjectionMateExact
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
- WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational
- Mathlib.Algebra.Homology.DerivedCategory.KInjective

The original resolution and field-stage dependencies are retained in the two new nodes
where they are still needed. They are not claimed as globally pruned modules.
The final assembly itself no longer needs
lem-sf-native-weil-pullback-star-preservation or
lem-sf-derived-weil-tensor-hom-adjunction: its source and target functors already have
ambient native derived endpoints, and the output structure asks for their isomorphism.
The existing constructible-preservation results and modules remain in the library.
No existing module is withdrawn; no whole-module pruning is claimed.

Removed obsolete direct tool_uses approvals from the item node (the corresponding
utilities still occur in the resolution/ordinary subarguments where relevant):

- def-exchange-projection
- def-sf-native-weil-derived-framework
- def-weil-algebraically-closed-coefficients
- def-weil-finite-tor-amplitude
- lem-sf-fixed-pair-adjunction-lift
- lem-sf-fixed-pair-derived-forget-comparison
- lem-weil-pbc-ringed-projection-mate-exact
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- lem-weil-pbc-termwise-adjunction-homotopy
- thm-sf-pf-field

## Where the brief, the DAG or earlier work was wrong

No statement defect or repair assignment was found. The queue lists one proof hole;
there is no current rework row or item build-error file in the shared snapshot.
The original DAG's generic lemmas do not directly produce the normalized native data
or the ordinary projection formula in section coordinates. The split statements retain
those precise missing constructions instead of moving the original theorem to a new name.
The existing rational localizing projection theorem concerns internal modules with its
own tensor and adjunction; it does not directly state the normalized section-module mate.

Edge cases were checked against the arguments: zero complexes, empty schemes and p = id
need no nonzero object or nonempty space hypothesis; arbitrary multi-degree bounded
constructible T is retained. The ordinary lemma assumes bounded constructibility only,
using finite Tor amplitude at finite coefficient field stages. No target is changed.

## New nodes

lem-sf-native-proper-projection-models packages exactly the resolution, sheaf, tensor,
representative and counit data before forming the projection mate. It contains no
projection-formula assertion. Its theorem remains open with the original construction
plan, precise sources and declarations available to the next worker.

lem-sf-ordinary-proper-projection-invertible asserts invertibility of the actual ordinary
mate for bounded constructible ordinary module inputs, with the specified proper
realization comparison. It contains no Weil structure, native comparison square,
naturality assertion or native isomorphism. Its source is the finite-field projection
argument in original Steps 6--7, including the identity-open normalization.


## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeProperProjectionModels": "fb3ed4366e698ff8e2cfc1b8db1874b4fa12aa69", "Sheaf.Paper.NativeProperProjectionRealization": "a5224fc4ecf3b95c4c95e42ff8df633243877b25", "Sheaf.Paper.OrdinaryProperProjectionInvertible": "7648d3f7f10ecbe67144abd290840840f28c2abe"}, "results": {}, "time": "2026-10-28T08:23:10+0800", "transitive": 0, "version": 1}
```

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
