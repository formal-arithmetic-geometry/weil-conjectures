# Q141: ordinary-etale pullback and line flat model

## Worker report

The new module `Sheaf.AlgebraicGeometry.EtalePullbackLineFlatModel` states
`AlgebraicGeometry.Etale.etale_pullback_line_flat_model`. It constructs the
termwise model, the actual representative comparison, and the specified
common refinement of trivializing covers. It introduces no alternative
flatness, constructibility, K-flatness, inverse-image or derived-tensor notion.
All helper constructions belong to this node. The one theorem is postponed
with `sorry`; every definition has full data.

Hypotheses, individually:

- `R : Type (u+1)`, `[CommRing R]`, `[Finite R]` are the arbitrary finite
  commutative coefficient ring. The coefficient and sheaf-value universe
  follows the recorded small-etale convention for schemes in `Type u`.
- `X Y : Scheme.{u}`, `f : X ⟶ Y`, `[IsNoetherian X]` and
  `[IsNoetherian Y]` are precisely the given morphism and Noetherian schemes.
  Mathlib's `IsNoetherian` combines local Noetherianness and compactness,
  equivalently a finite affine cover by Noetherian rings.
- `C : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat R)) ℤ` is
  the integer cochain complex in the recorded constant-coefficient category.
- `a b : ℤ`, `_hab : a ≤ b`, and `_hz` express the nonempty interval and
  zero objects in every degree outside it. `_hflat` uses `exactFunctor`
  applied to canonical sheaf `tensorRight`, the definition of tensor-flatness.
  `_hc` uses exactly `Scheme.IsConstructibleEtaleModuleSheaf` on every term.
- `K : DerivedCategoryModule R Y` and `e : DerivedCategory.Q.obj C ≅ K`
  preserve the specified representative and its specified isomorphism.
- `E` is the given module sheaf. The cover `V` and the module-linear
  isomorphisms `_hE` express precisely that E is etale locally R. Giving
  a witness for an existential local-triviality hypothesis does not impose
  extra geometry or a global trivialization. `r : ℤ` is unrestricted.

Conclusions, individually:

- `etalePullbackLineModel` applies exact `Etale.upperStar` degreewise,
  then `tensorRight E` degreewise, and then the cochain shift r. It is
  the literal termwise complex in the statement, with the signed shift.
- In `etalePullbackLineAssertions`, the first two conjuncts express
  termwise exact tensor and finite-value constructibility, respectively.
- The third conjunct says `IsZero` outside `[a-r,b-r]`; the fourth uses
  the recorded `MorphismProperty.kFlat` interface, specialized to
  quasi-isomorphisms of the same ordinary-etale module complexes.
  On this symmetric additive tensor category it is the acyclic-test
  K-flatness of the node, by the cone criterion.
- The comparison is built from the specified e, the localization
  factorization of exact inverse image, Q's lax monoidal tensor comparison,
  the total-tensor/single-complex isomorphism, and the shift comparisons.
  The `etaleLineRepresentativeComparisonIsIsoOnSite` conjunct is exactly
  `IsIso` of this actual arrow, factored through the generic coefficient-site
  interface to avoid expensive specialized instance reduction. It is
  written in the derived-to-model direction; its uniquely determined
  inverse is exactly the asserted model-to-derived comparison. Its source
  is f_R^*K tensor^L E[r], and its target is Q(the termwise model).
- The sixth conjunct says every `Q.homology j` is constructible. The
  next conjunct is the existing `DerivedCategory.hasTorAmplitudeIn`, which
  quantifies over every module sheaf N in degree zero, with no flatness
  or finiteness assumption on N, and every integer outside `[a-r,b-r]`.
- The last clause quantifies over every j and every prescribed
  `Scheme.Stratification Y`, with the actual `LocallyConstantDatum`
  witnesses on its strata, the finite modules `M k i`, and their local
  module isomorphisms. It uses `S.pullback f`, whose domains are the
  actual fibre products and whose strata are the constructible locally
  closed inverse images. It asserts precisely the restriction formula
  H^j(Q)|Z' = f_t^*(H^(j+r)(C)|Z) tensor E|Z'.
- `etalePullbackLineCover` intersects the prescribed cover pulled back
  along `pullback.fst` with V pulled back along the stratum immersion.
  On every member i of this actual refinement the last assertion gives
  a module isomorphism with the constant sheaf of `M k i.1`, retaining
  exactly the finite model of the original cover. Empty strata are allowed
  to remain: their covering conditions are vacuous; deleting them is optional.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`; the full locally-ringed-space affine-chart definition.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public
  coefficient module: `AlgebraicGeometry.Etale.DerivedCategoryModule`,
  `DerivedCategory.Q`, `DerivedCategory.homologyFunctor`, and the actual
  constant ModuleCat-valued etale category.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`; the exact inverse-image
  identification. The ordinary ModuleCat-valued realization is the existing
  `Etale.upperStar` and its `mapHomologicalComplex`, `mapDerivedCategory`
  and `mapDerivedCategoryFactors`, never an arbitrary exact functor.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`,
  the integer-up complex and its homology.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `exactFunctor`,
  the fully explicit tensor-flat predicate used in the recorded sibling
  `finiteFlatConstructible_totalTensor`. The principal ringed-site
  `IsFlatOnSite` has a different domain; the node also records the generic
  exactFunctor interface. No private copy or strengthened flatness is used.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`, `Scheme.Stratification` and
  `Scheme.LocallyConstantDatum`, including the actual finite constant values.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, public import of
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, explicitly recorded by the
  dependency for the ordinary ModuleCat-valued sheaf encoding.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `Etale.derivedTensor`, the existing unbounded K-flat derived tensor.
- `WeilConjectures.ConstructibleSheaf.Pullback`:
  `Scheme.Stratification.pullback`, actual constructible scheme strata.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` supplies the
  existing localization, total-tensor/single and shift comparison interfaces.
  Proof-only recorded modules are imported without `public` for stage 3.

Sources: read the local Stacks `lemma-pullback-ctf` (0963) and its actual
finite-flat-complex argument, together with the recorded eight-step node
proof. That proof is carried step by step in the theorem docstring. The
statement is preserved verbatim: no statement correction or new node.

Edge cases: the zero ring and the empty schemes are admitted; no nonzero
or nonempty typeclass appears. A one-degree interval a=b is allowed. For
r negative as well as positive the degree is n+r, giving a-r and b-r.
Nontrivial locally free lines are admitted: only the chosen local bases
are used. Covers and stratifications may include empty members. The Tor
bound allows a nonflat N (e.g. Z/2 over Z/4). No smoothness, flatness of f,
separation, reducedness, field, or nonnegative-shift hypothesis is added.

Searches performed (actual tool results retained in searches.jsonl):

- LeanFinder via msearch.py: “Pullback of a bounded flat constructible
  complex tensored with an etale locally free line remains K-flat with
  shifted Tor amplitude”. Eight hits, ordinary scheme base-change flatness
  and module-flat tensor exactness; none states the combined etale model
  theorem with the prescribed witnesses and comparison.
- Loogle via msearch.py: `HomologicalComplex, tensorObj`. No results:
  `tensorObj` is not a recognized unqualified identifier in that service.
- Mathlib grep via msearch.py, AlgebraicGeometry:
  `constructible.*pullback|pullback.*constructible`; zero matches.
- rg of live `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  pullback/line/flat patterns: no existing statement of this item. Found
  the generic bounded total-tensor theorem, the finite-flat-model theorem,
  and general constructible pullback, which are properly used as inputs.

No STATEMENT-DISPUTED issue was found. The previous refusal conflated the
Q152 stage-1 split with a stage-2 Lean statement: the current node has
`reviewed` for stage 1 and no `lean` record or `reviewed_lean` record.

Validation: scompile.py compiled the delivered module in both sandbox and
library modes without errors or warnings (8.1 and 8.4 seconds). The generic
site invertibility wrapper preserves the literal canonical comparison and
avoids the original elaboration timeout.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
