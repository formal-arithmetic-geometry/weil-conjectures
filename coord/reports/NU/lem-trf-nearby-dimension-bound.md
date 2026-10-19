## Worker report

The module `Sheaf.Paper.NearbyCyclesDimensionBound` states `nearbyCycles_uniformCohomologicalBound` for a Noetherian base scheme, finite type morphism, bounded geometric fibre dimension, finite torsion coefficient ring, and every scheme base change.  It uses the existing oriented nearby-cycle functor and derived t-structure bounds.

The binders render the node hypotheses as follows: `S` and `X` are schemes, `[IsLocallyNoetherian S]` is the Noetherian hypothesis, `f` with `[LocallyOfFiniteType f] [QuasiCompact f]` is finite type, `d : ℕ` is the nonnegative fibre bound, and `hgeom` quantifies every point and algebraically closed residue-field extension and bounds the topological Krull dimension of the geometric fibre.  `Λ`, `[CommRing Λ]`, `[Finite Λ]`, `m`, `hm`, and `hΛ` render the finite commutative ring and `m Λ = 0` with `m ≥ 1`; `a b : ℤ` are the cohomological interval endpoints.

The first conjunct states the upper bound `IsLE (2*d)` for each sheaf in degree zero.  The second repeats it for `f_T` after every scheme map `g : T ⟶ S`, with arbitrary coefficient sheaf on the base-changed source.  The third states that an input complex with `IsGE a` and `IsLE b` is sent to one with `IsGE a` and `IsLE (b+2*d)`.  The fourth repeats this bounded-complex conclusion after every base change.  `sorry` is the postponed proof.

Dependencies used are `AlgebraicGeometry.OrientedNearbyCycles.nearbyCycles` from `Sheaf.Paper.OrientedNearbyCycles` and Mathlib's `IsLocallyNoetherian`, `LocallyOfFiniteType`, `QuasiCompact`, scheme pullback, `topologicalKrullDim`, `Spec.map`, and residue fields.  The source declaration's `isBounded_iff` records the equivalence between bounded t-structure membership and degreewise homology vanishing.

Edge cases checked: `d = 0`, empty geometric fibres (dimension bottom), `a = b`, `a > b`, zero coefficient ring and zero sheaf, identity base change `T = S`, arbitrary non-Noetherian `T`, and algebraically closed residue-field extensions.  Searches were made in Mathlib, `WeilConjectures/`, and project `lean/Sheaf` with `rg`; LeanFinder, Loogle, grep, and LeanSearch records already attached to the stage-1 node all returned no matching nearby-cycle bound.  No statement correction or disputed flag was needed.

## Second reading by NU

I reread the node statement and the complete module signature.  Every hypothesis and each of the four clauses is represented in order; the geometric-fibre expression is the explicit scheme pullback along an algebraically closed residue-field extension, and all base-change quantifiers are explicit.  The file compiled cleanly with `scompile.py` (sandbox and library checks).

## Maintainer review fix

The maintainer's second reader corrected the statement in three places. Everything else is unchanged.

- H3: the node assumes "an integer $m\geq1$ invertible on $S$". The delivered signature had `hm : 0 < m` and `hΛ : (m : Λ) = 0` but no invertibility hypothesis, and the reports above say every hypothesis is represented. Added `(hmS : IsUnit (m : Γ(S, ⊤)))`, which is the project convention (see `InvertibleExponent`, `EtaleTorsorSpreading`).
- H3: the node says "Noetherian scheme". The Lean now uses `[IsNoetherian S]`, which extends `IsLocallyNoetherian`, the recorded declaration of the cited pqf-def-locnoeth, with `CompactSpace`. Before, quasi-compactness of `S` was dropped.
- H3, universes: the coefficient ring had `Λ : Type u`, the scheme universe, but the dependency's `nearbyCycles` takes `Λ : Type v`. The citers TraitNearbyBaseChange and GoodOrientedNearbyKunneth use `Λ : Type v`, and OrgogozoGoodModification uses `Λ : Type (u+1)`, so they could not have applied the delivered statement. Used directly at site universe `max (u+1) v`, Mathlib's `DerivedCategory.IsLE/IsGE/singleFunctor` get stuck on `?w+1 =?= max (u+1) v`. The module therefore adds three abbreviations, `DerivedIsLE`, `DerivedIsGE` and `derivedSingle`, over a site in a generic universe `s`, which is the same pattern as the dependency's `IsBounded`. At `v = u` they are `Iff.rfl`/`rfl` to the Mathlib notions, which I checked by compiling.
- H8: the statement docstring now gives the node's four proof steps with their cited nodes.

Per-file compile (`nt_compile.py`): delivered file rc 0; fixed file rc 0, with no error or warning.
