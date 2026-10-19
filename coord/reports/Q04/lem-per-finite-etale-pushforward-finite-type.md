## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtalePushforwardFiniteType` states
`AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_lowerStar_of_isFinite_etale`.
Its sole proof is `sorry`. The six steps of the DAG proof are reproduced in the
theorem docstring. The source was read in
`literature/stacks-project/etale-cohomology.tex`,
`lemma-pushforward-locally-constant` (Tag 095B), lines 9972–9991.
No statement correction, new node, or dependency repair is needed.

Clause-by-clause correspondence:

- The two arbitrary schemes are `{X Y : Scheme.{u}}` and the named morphism
  `f : Y ⟶ X` has exactly the hypotheses `[IsFinite f] [Etale f]`.
- An arbitrary commutative ring is `{R : Type (u + 1)} [CommRing R]`.
  There is no `[Finite R]`, `[IsNoetherianRing R]`, or nontriviality hypothesis.
- A sheaf of constant-coefficient modules on the small etale site of `Y` is
  `F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)`. This is the
  fixed-coefficient presentation of modules over the constant ring sheaf,
  explicitly exposed for this use by the dependency's recorded declaration list.
  Module-valued sheafification and localization respect the scalar operations;
  no new ring or module category is defined here.
- Local constancy of finite type is `[IsFiniteLocallyConstantSheaf F]`, using
  the etale-specific interface in the recorded dependency
  `def-weil-pbc-locally-constant-finite-type-modules`. It combines an etale
  trivializing cover with finite generation of all geometric stalks. In this
  coefficient category `ModuleCat.isFinitelyGenerated_iff` identifies the
  latter with `Module.Finite R`. This agrees with the node's finitely generated
  constant-value formulation: a constant trivialization at any nonempty cover
  member has value isomorphic to a geometric stalk, hence finitely generated;
  discard empty members and choose a separably closed geometric point on each
  remaining member. Conversely, geometric points lift through the trivializing
  cover and their stalks are the indicated finitely generated constant values.
  For empty `Y`, the empty cover is allowed. Restricting a cover of `Y` to any
  site object gives the covering-sieve formulation for every object. Neither a
  single constant value nor a finite trivializing cover is required.
- The direct image is exactly
  `(Etale.lowerStar (ModuleCat.{u + 1} R) f).obj F`.
  Its defining functor precomposes with etale base change, so evaluation at
  `W → X` is `F(W ×_X Y)`. The maps are `R`-linear, providing the constant
  coefficient module structure specified by the node.
- The conclusion is the same `IsFiniteLocallyConstantSheaf` predicate applied
  to this direct image. No constructibility or weaker stalk-only conclusion
  substitutes for local constancy.
- Both scheme and coefficient finiteness exclusions in the final sentence of
  the node are respected: no Noetherian, quasi-compactness, separatedness,
  finite-ring, or finite-underlying-module assumptions occur.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  morphisms; `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
  The finite-etale-category Mathlib match is `MorphismProperty.Over` with
  property `@IsFinite ⊓ @Etale`, together with `Over.pullback`. Here only
  the unbundled condition on the named morphism is needed.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`;
  `Scheme.Etale` has objects in universe `u+1` and arrows in universe `u`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, a transparent
  abbreviation of the existing `SheafOfModules` (no copy is introduced).
  This dependency is imported; the recorded module-valued presentation is used
  as described above.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf` is the
  sheafification of `Functor.const`. It underlies local trivializations.
- `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`:
  `SheafOfModules.IsLocallyConstantFiniteTypeModules` and the publicly exposed
  etale predicates from `WeilConjectures.ConstructibleSheaf.Defs`:
  `Scheme.IsFiniteLocallyConstantSheaf`, `Scheme.IsLocallyConstantSheaf`,
  `Scheme.IsFiniteSheaf`. The generic equal-universe ringed-site definition
  is not instantiated on the unequal-universe etale site; its recorded
  etale-specific interface is used. The compiler required an explicit public
  import of `WeilConjectures.ConstructibleSheaf.Defs`, which was added.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`;
  `WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated`:
  `ModuleCat.isFinitelyGenerated_iff`, read to verify the arbitrary-ring meaning.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, read with its section parameters and
  definition. The derived part of the dependency is not needed by this statement.

Proof dependency imports include the published modules
`WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit` and
`WeilConjectures.AlgebraicGeometry.DirectImageSplitCoverProduct` (their current
sources were read with `scompile.py --source`), and the Mathlib modules for
localization, base-change finite limits, and sheafification. Constant pullback
is already exposed by `WeilConjectures.ConstructibleSheaf.Defs`.

Edge cases checked mathematically before writing:

- Empty source and an empty finite fibre: direct image is the zero module sheaf
  on that neighbourhood; the empty product and empty generating set are valid.
- Empty target (hence empty source): local constancy and the stalk condition
  are satisfied by empty covering data; no `Nonempty` hypothesis is present.
- The zero coefficient ring and zero module are allowed.
- `R = ℤ` and constant value `ℤ²` are allowed, despite infinite underlying sets;
  finite generation, rather than set finiteness, is the predicate used.
- Non-Noetherian coefficient rings and schemes are allowed.
- On a disconnected non-quasi-compact target the finite degree and constant
  module values may vary from neighbourhood to neighbourhood without a bound.
- The usual etale coefficient universe `u+1` leaves scheme objects in `u+1`
  and arrows in `u`; no equality between these universes is imposed. Every
  ring/sheaf can be accommodated by taking an adequate common universe.

Searches for an existing statement:

- `msearch.py` LeanFinder: “Finite etale direct image preserves locally
  constant sheaves of finitely generated modules” — eight condensed/light
  condensed local-constant functor results; no scheme pushforward theorem.
- `msearch.py` Loogle: `CategoryTheory.Sheaf, ModuleCat` — twelve general
  evaluation/forgetful declarations; no preservation theorem.
- `msearch.py` grep:
  `finite.*etale.*(pushforward|lowerStar)|locallyConstant.*(pushforward|lowerStar)`
  in `AlgebraicGeometry` — zero hits.
- `msearch.py` LeanSearch: “Direct image along a finite etale morphism preserves
  locally constant module sheaves of finite type” — eight results concerning
  condensed modules, sheaf pullback finite limits, and scheme morphism
  properties; no match. Raw outputs are in the sandbox's `searches.jsonl`.
- `rg` over upstream `WeilConjectures/ConstructibleSheaf` for
  `finite.*[eE]tale|[lL]owerStar|[pP]ushforward|IsFiniteLocallyConstantSheaf`
  found existing definitions and other pullback/constructibility statements.
  Search for the item id in upstream sources found no declaration.
- `rg` over `lean/Sheaf` found
  `Scheme.finiteLocallyConstant_lowerStar_of_finite_etale` in
  `Sheaf.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant`.
  Its full signature and proof were opened: it requires `[Finite Λ]`, so is
  only a special case. It cannot be used as an exact existing match.
- The side upstream module
  `WeilConjectures.ConstructibleSheaf.FiniteEtalePushforward` was opened:
  its arbitrary-ring theorem concerns constant input sheaves only, not all
  locally constant finite-type inputs. It is also only a special case.
- The chosen full declaration name was searched in `lean`, upstream
  `WeilConjectures`, and pinned Mathlib; there were no matches.

Validation: `scompile.py Q04 lem-per-finite-etale-pushforward-finite-type`
compiled the delivered module separately in sandbox and library mode, cleanly
(3.6 s and 2.9 s). An initial compile found the etale predicate was not visible
through the side dependency's installed interface; adding its defining
upstream module explicitly fixed that. All universes and variables are bound
explicitly and `autoImplicit` is disabled. Only `lean` changes in the node copy.

## Second reading by Q04

This is a separate second reading by the dispatched worker, not a claim that
another agent reviewed it: the launcher's explicit instructions forbid starting
other agents and specify a maintainer's independent review after delivery.
I reopened the node and final module and compared every binder and conclusion.
The two schemes, direction of `f`, finite and etale hypotheses, arbitrary
commutative coefficient ring, module-valued sheaf, input local finite-type
predicate, fixed-coefficient direct image, and identical output predicate all
match. I rechecked the docstrings defining `IsFiniteSheaf`: “finite” here is
finite generation and does not assume a finite ring. The earlier finite-ring
preservation theorem therefore is not an exact existing statement. Empty
schemes, zero modules, and infinite coefficient sets are not excluded.
The only implementation mismatch found during validation was import visibility;
the defining upstream module is now imported explicitly. No mathematical
statement mismatch or disputed claim remains.
