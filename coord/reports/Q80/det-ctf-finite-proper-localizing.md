## Worker report

This repair replaces the earlier ordinary `ModuleCat A` presentation with the recorded condensed finite-coefficient presentation required by the immutable-head review. `finiteDiscreteCondensedCoefficient A` is the canonical continuous-map condensed ring for the finite discrete commutative ring A, using `continuousMapRingObjOfUniverse`; its monoid and commutative monoid structures are the published canonical structures. No coefficient ring, module category, or closure is chosen arbitrarily.

`finiteCoefficientLocalizingProperties` is the four-clause helper. For a functor F between the module-object derived categories over `condensedRingObj Λ X` and `condensedRingObj Λ Y`, its clauses are:

* `constantModelBoundedConstructible Λ X K ∧ DerivedCategory.finiteTorAmplitude _ K` implies the same conjunction for `F.obj K`. This is the recorded `sk-def-sfb-constructible` Dctf predicate, clause by clause: boundedness and constant-model constructibility are rendered by `constantModelBoundedConstructible`, and finite Tor amplitude is rendered by `DerivedCategory.finiteTorAmplitude`.
* `localizingClosureProEtale Λ X K` implies `localizingClosureProEtale Λ Y (F.obj K)`. This is the recorded smallest replete triangulated ambient coproduct closure.
* Every ambient distinguished triangle `T ∈ distTriang _` whose three vertices satisfy the source closure is sent to `F.mapTriangle.obj T ∈ distTriang _`.
* Every discrete diagram indexed by `I : Type (u + 2)` whose objects are in the source closure satisfies `PreservesColimit D F`; this includes the empty diagram and the canonical ambient coproduct comparison.

The proper theorem uses the published module-object total right derived pushforward `(f)_*⟦Λ⟧.rightDerivedFunctor`. The open theorem uses the published exact derived extension by zero `(j)_!open⟦Λ⟧.mapDerivedCategory` and separately states `PreservesColimitsOfShape` for every discrete shape. The compactification theorem uses their composite. All standing hypotheses from the node are retained: prime `ℓ`, characteristic `p > 0` with `p ≠ ℓ`, finite commutative A killed by a positive power of `ℓ`, separated locally finite type quasi-compact k-schemes, and k-morphisms; no flatness or cohomological-dimension assumption is added.

`derivedPullbackSquareComparison` is the canonical comparison obtained from the recorded condensed derived pullback composition isomorphisms and the equality in `ChosenCartesianSquare`. `derivedBaseChangeMate` is the actual ambient unit/square/counit mate: it inserts the unit of `Lf'^* ⊣ Rf'_*`, transports through that pullback comparison with `Functor.squareTransport`, and contracts with the counit of `Lf^* ⊣ Rf_*`. The base-change theorem asserts `IsIso` of this exact component on every K in `localizingClosureProEtale`, with arbitrary g.

Dependencies used:

* `Sheaf.Paper.CondensedConstantConstructibility`: `constantModelBoundedConstructible` and the finite constant-model constructibility definitions.
* `Sheaf.Paper.LocalizingClosure`: `localizingClosureProEtale`.
* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare` and its commutative-square equality.
* `Sheaf.Topology.ContinuousMapCondensedRing`: `continuousMapRingObjOfUniverse`, `continuousMapRingObjOfUniverseMonObj`, and `isCommMonObj_continuousMapRingObjOfUniverse`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`: condensed module-object derived pullbacks, pushforwards, their adjunction, and composition isomorphisms.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek`: condensed extension by zero and its derived functor.
* `WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport`: canonical transport used in the mate.
* `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`: the published `CommShift` structure for total right derivation.
* Mathlib scheme, finite-type, proper, and open-immersion declarations.

Edge cases checked in the statement are empty schemes and fibres, the zero ring and zero complex, empty coproduct diagrams, identity arrows and identity base changes, and non-flat base-change maps. No `Nonempty` or `Nontrivial` assumption is introduced. The finite discrete topology is installed only inside the canonical coefficient construction, so the public theorem has no extra topology hypotheses on A.

Searches made before and during repair included `msearch.py` leanfinder/loogle/grep for proper direct image, localizing closure, constructible finite-Tor, and base-change declarations; `rg` over the shared `lean/Sheaf` and upstream `WeilConjectures` trees for `constructibleFiniteTor`, `localizingClosureProEtale`, `derivedBaseChangeMap`, and module-object operations; and `scompile.py --source` for `CondensedConstantConstructibility`, `LocalizingClosure`, `ModuleObject.Derived.BoundedConstructible`, `ModuleObject.Derived.UpperLowerStar`, and `ModuleObject.BaseChangeTheorems.MorphismDefs`. The searches found the recorded constant-model and localizing declarations and the canonical condensed six-functor interfaces; no existing declaration stated this item.

The immutable-head return identified H3/H4: the previous packet used upstream `DerivedCategory.constructibleFiniteTor` and a generic closure, whose equivalence to the recorded objects was only the item's proof step. This repair uses the recorded objects directly and keeps the four-theorem split, helper bundle, chosen square, and actual mate. H9 is addressed by removing unused statement imports. No source statement correction is made: the paper statement remains unchanged and is represented through its canonical finite discrete condensed coefficient identification.

Validation: `scompile.py Q80 det-ctf-finite-proper-localizing lean/Sheaf/Paper/FiniteProperLocalizing.lean` compiles both sandbox and library copies cleanly with the expected `sorry` declarations only. The delivery dry run is the next required check.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (maintainer review of 2ebc27823ac4)

* H4: `derivedPullbackSquareComparison` and `derivedBaseChangeMate` were a second definition of the
  recorded ambient exchange of def-weil-pbc-ambient-ringed-exchange
  (`AlgebraicGeometry.ProEtale.CondensedRing.condensedAmbientExchange` in
  `Sheaf.Paper.CondensedAmbientExchange`, on the base of this delivery): the same mate (`mateEquiv`) of the
  same comparison `leftDerivedUpperStarComp (f', g)⁻¹ ≫ eqToIso(square) ≫ leftDerivedUpperStarComp (g', f)`
  under the same derived adjunctions. Both private definitions are removed and
  `finiteProperLocalizing_baseChange` states `IsIso ((condensedAmbientExchange _ sq).app K)`.
* H9: the unused import `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek` and the now
  unused `SquareTransport` import are removed.
* H8: every declaration carries `(blueprint: det-ctf-finite-proper-localizing)` with its source place, and the
  four theorem docstrings carry the node's proof steps (1--13; 1--10, 14, 15; 1, 16; 17).
* The lean record lists the coefficient helper and its two instances in `declarations`.
* Compile: `nt_compile.py --json` on the fixed file, clean, 23.0 s (no error, no warning besides `sorry`).

