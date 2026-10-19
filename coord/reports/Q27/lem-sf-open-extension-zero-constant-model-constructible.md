## Worker report

The module `Sheaf.Paper.OpenExtensionConstantModelConstructible` states
`AlgebraicGeometry.ProEtale.constantModelConstructible_openImmersionLowerShriek`.
It has one theorem, whose proof is `sorry`, and no new definitions. The original
node statement and dependency lists are unchanged.

Hypothesis and conclusion correspondence:

- The prime ell is `ℓ` with `[Fact ℓ.Prime]`. Positive characteristic is the prime
  `p` with `[Fact p.Prime]` and `[CharP k p]`; `_hpℓ : p ≠ ℓ` is the inequality.
  `k : Type u` and `[Field k]` give the arbitrary base field.
- `[U.Over (Spec (.of k))]` and the corresponding X instance give the k-schemes.
  On both structure morphisms, `LocallyOfFiniteType` plus `QuasiCompact` is finite
  type and `IsSeparated` is separatedness. `j.IsOver` gives the k-morphism;
  `IsOpenImmersion j` is its open immersion hypothesis.
- The arbitrary commutative condensed ring is
  `Λ : Sheaf (coherentTopology Profinite) Ab` with `MonObj` and `IsCommMonObj`.
  This is the existing internal ring encoding, not a restriction to continuous
  coefficients. `condensedRingObj Λ U` and `condensedRingObj Λ X` are exactly
  the inverse images of this same Λ from the point.
- `M : Mod ... (condensedRingObj Λ U)` is a module object over Λ_U. The finite
  stratification witnessing its constructibility is made explicit as the argument
  `S : Scheme.FiniteLocallyClosedStratification U`. `_hS` requires every stratum
  to be constructible, and `_hM` requires the recorded
  `HasFiniteConstantLocalModel` of the pullback along each `S.immersion a`.
  Supplying the witness of the source's existential hypothesis changes no case
  or mathematical strength; no additional constructibility hypothesis is needed.
- `CondensedRing.openImmersionLowerShriek Λ j` is exactly the recorded extension
  by zero, including its canonical change of scalars along α_j.
- The first conjunct is precisely `IsConstantModelConstructible Λ X (j_! M)`.
- The existential `T` is a finite locally closed scheme stratification of X.
  The equivalence `Fin T.n ≃ Option (Fin S.n)` gives exactly one extra stratum.
  `some a` labels the original a-th stratum, and `none` labels the complement.
  Each stratum is constructible by the first universal conjunct. The second
  universal conjunct identifies its immersion, as an object of `Over X`, with
  `S.immersion a ≫ j` or with `j.closedComplement`, respectively. Thus both the
  subscheme structures and their maps to X are preserved, not just their images.
  In particular T has exactly S.n + 1 strata, including empty strata when present.
- `j.closedComplement` is the existing canonical vanishing-ideal subscheme of
  the complement of `j.opensRange`. Its domain is reduced; no arbitrary choice
  of a closed scheme or of a comparison morphism is assumed.
- The next conjunct gives a module-object isomorphism between pullback of
  `j_! M` along `S.immersion a ≫ j` and pullback of M along `S.immersion a`.
- `IsZero ((CondensedRing.upperStar Λ j.closedComplement).obj (j_! M))` is the
  zero restriction to the reduced closed complement, in its full module category.
- The last two conjuncts record the node's explicit edge cases: `IsEmpty U`
  implies both `IsZero M` and `IsZero (j_! M)`; `IsIso j` implies the canonical
  reduced complement has no points. The latter is the coordinate-independent
  identity-open case, including an arbitrary presentation of U = X.

Dependency interfaces read and used:

- `sk-def-sfb-dc-setting`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `CondensedRing.compactificationOverField` and its field/scheme setting. The
  theorem writes that setting explicitly rather than imposing an additional predicate.
- `sk-def-sfb-condensed-ring`:
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` exports the ring-object
  interpretation and commutativity; the theorem uses its general ambient category
  with `MonObj` and `IsCommMonObj`, without specializing Λ to a continuous ring.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `coefficientRing`,
  `coefficientRing_X`, `condensedRingObj`: the monoidal inverse image from the point.
- `sk-def-sfb-module-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `CondensedRing.openImmersionLowerShriek`, the exact module-object functor.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`, and
  `IsConstantModelConstructible`. The local definition chooses finite
  presentations on the point before pulling them to covering schemes.
- `def-constructible-stratification`:
  `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
  `Scheme.FiniteLocallyClosedStratification`; constructibility is imposed separately.
- `det-def-sfb-constructible-local-model`:
  `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`,
  `finiteConstantLocalModel_iff_exists_cover`, whose scalar models are extension
  of ordinary Λ(*)-modules along `scalarCoefficientHom`. Imported for the proof.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `IsReduced`.
  The canonical complement is the published `Scheme.Hom.closedComplement` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, defined by the
  vanishing ideal, with reducedness supplied by the existing construction.

All already stated proof dependencies are available through the explicit private
proof imports and the public dependency closures. In particular the ringed open-closed
comparison, reduced induced closed subscheme, scalar-change comparison, module-object
pullbacks and composition, and adjunction mates are imported for the five-step proof
written in the theorem docstring. No proof-import cycle is introduced.

Edge cases checked mathematically before writing: U empty, X empty, identity j,
empty original strata (allowed by the recorded finite-family structure), S.n = 0,
zero module, zero coefficient ring, nonreduced X, and arbitrary commutative condensed
coefficients. For U empty and nonempty X, the complement is X reduced, not X with
its original structure. The vanishing-ideal construction is essential here. An
empty complement is retained as the extra stratum, so the indexing equivalence
excludes none of these cases. No nonempty index or nonzero coefficient condition
appears, and all universes and variables are explicitly bound.

Searches for an existing statement:

- msearch LeanFinder, query “Extension by zero preserves finite constant scalar
  models on a finite locally closed stratification of a scheme”: eight unrelated
  basic scheme-section/finite-type results; no match.
- msearch Loogle, query `IsConstantModelConstructible, openImmersionLowerShriek`:
  no hits; the constructibility identifier is unknown to the Mathlib index.
- msearch grep, query `ConstantModelConstructible|openImmersionLowerShriek`:
  no Mathlib hits.
- msearch LeanSearch, query “Extension by zero of a constructible module sheaf
  preserves finite constant local models”: eight unrelated extension-of-functions
  and sheafification results; no match.
- rg in upstream WeilConjectures and the side Sheaf sources for
  `ConstantModelConstructible`, `HasFiniteConstantLocalModel`,
  `openImmersionLowerShriek` and the node id: the definitions above exist and
  weaker locally finitely presented constructibility results exist, but no theorem
  with the required constant-model conclusion and prescribed extended strata.
- Full-name search for `constantModelConstructible_openImmersionLowerShriek`
  in `dag/lean_names_upstream.json`, Mathlib, upstream WeilConjectures, and side
  Sheaf: no hits. Source search for `closedComplement` found and reused the
  existing canonical construction, so no helper or new node is introduced.

The source paragraph Constructibility in the current main-20261015 blueprint was
read directly. No node fault or statement dispute was found. Validation uses only
scompile.py and deliver2.py, under the prescribed per-file limit.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
