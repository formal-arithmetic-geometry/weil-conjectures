## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage` states
`AlgebraicGeometry.Etale.finite_directImage_constructible_and_higher_vanishing`.
It introduces no definitions and leaves precisely that theorem's proof as `sorry`.
The statement and all six proof steps were read against the node and the original
blueprint source `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-morphism.md`, order 1580.
No node correction or additional node is needed.

Hypothesis and conclusion correspondence:

- The field k is `(k : Type u) [Field k]`, and the schemes are `{X S : Scheme.{u}}`.
  No algebraic closedness, perfectness or characteristic restriction is imposed on k.
- “S of finite type over k” is `[S.Over (Spec (.of k))]`, together with
  `[LocallyOfFiniteType (S ↘ Spec (.of k))]` and
  `[QuasiCompact (S ↘ Spec (.of k))]`. These are exactly the two parts of finite type
  specified by the scheme-conventions dependency; no separatedness is added.
- The named finite morphism is `(f : X ⟶ S) [IsFinite f]`. Since the node names f,
  it is explicit; no extra structure map on X or compatibility datum is needed.
- The coefficient convention cited by the node is represented by `(N : ℕ)`,
  `(Λ : Type (u + 1)) [CommRing Λ]` and
  `(hcoeff : IsSmoothBaseChangeCoefficients N Λ S)`. The recorded definition is
  `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`.
  Invertibility on X follows by pulling back the unit along f; it need not be
  separately assumed. This is the ambient convention, not an extra restriction
  invented for this lemma.
- The Lambda-sheaf F is
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  The constructibility hypothesis uses the precise recorded declaration:
  `@Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F`.
  Its finite-ring argument is taken directly from hcoeff, avoiding a duplicate
  finiteness hypothesis. This predicate uses one finite constructible locally
  closed stratification and finite constant module trivializations on each stratum.
- “f_*F is constructible” is the first conjunct, the same predicate at S applied
  to `((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)`.
- “R^q f_*F = 0 for every q > 0” is the second conjunct: `∀ q : ℤ, 0 < q → IsZero`
  of `(DerivedCategory.Plus.homologyFunctor _ q).obj` applied to
  `(rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj` of
  `(DerivedCategory.Plus.singleFunctor _ 0).obj F`. This is exactly the dependency's
  definition of higher direct images as the cohomology of the derived image of
  the sheaf in degree zero. `IsZero` is categorical vanishing of that module sheaf.

Recorded statement dependencies read and used:

- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (base-change precomposition)
  and `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` (the actual
  declaration location; the dependency record's module lists lowerStar).
  The latter is the bounded-below right derived functor of the former.
- `def-weil-pbc-scheme-conventions` is explicitly a convention record, with no
  declaration or module of its own. The exact Mathlib classes used are
  `AlgebraicGeometry.IsFinite` (`Mathlib.AlgebraicGeometry.Morphisms.Finite`),
  `LocallyOfFiniteType` (`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`) and
  `QuasiCompact` (its public import `Morphisms.QuasiCompact`). Their full class
  definitions and docstrings were checked in the installed Mathlib sources.
- `sbc-def-coefficient-conventions`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`,
  `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`.
- `def-weil-pbc-etale-constructible-sheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`,
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.

The proof-only imports preserve the recorded plan: Noetherianity uses
`Mathlib.AlgebraicGeometry.Noetherian`; finite abelian constructible pushforward uses
`Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian`; module compatibility
uses `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`; locally constant
sections use `Sheaf.Paper.ConstantSheafSectionsLocallyConstant`; module category structure
uses `Sheaf.CategoryTheory.RingedSiteModules`; etale composition uses
`Mathlib.AlgebraicGeometry.Morphisms.Etale`; finite exactness uses
`WeilConjectures.SixFunctors.Finite.Exact`. The proof dependency
`def-weil-pbc-constructible-abelian-sheaf` has neither a Lean record nor a Mathlib match,
so it has no module to import. It is not needed to type the present statement.

Edge cases checked: empty X and empty S are allowed; there is no nonempty scheme
hypothesis. The zero sheaf is allowed. q = 0 is deliberately excluded from the
vanishing clause; all positive integer degrees are included. The zero coefficient
ring and N = 1 remain allowed when they satisfy the recorded convention. No dimension
bound, residue-characteristic assumption beyond the coefficient convention, reducedness,
or surjectivity of f is added. The coefficient universe is u+1, as required by the
recorded constructibility predicate and the six-functor implementation. All universe
and term variables are explicitly bound. The dependency's internal let in its existing
definition is reused unchanged; the new theorem signature contains no let or hidden have.

Searches for an existing statement (2026-10-15):

- `msearch.py ... leansearch "finite morphism constructible etale sheaf direct image higher vanishing"`:
  service unavailable (Internal Server Error).
- `msearch.py ... leanfinder "The direct image of a constructible etale module sheaf under a finite morphism is constructible and its positive higher direct images vanish"`:
  eight hits, including constructible-image results for subsets and finite-type module
  sheaves; none states the node's module-sheaf constructibility and higher vanishing.
- `msearch.py ... loogle "AlgebraicGeometry.Etale.lowerStar"`:
  unknown identifier in the search service, no hits. The declaration exists in the
  actual project source and was read there directly.
- `msearch.py ... grep "constructible.*(lowerStar|pushforward)|(lowerStar|pushforward).*constructible"`:
  no Mathlib hits.
- `rg` of the same pattern, case variants and the node id in `WeilConjectures` and
  `lean/Sheaf`: the project has finite pushforward constructibility for underlying
  set/abelian sheaves, generic constancy, finite-pushforward embeddings and finite
  exactness, but no statement with the recorded module predicate and both conclusions.
  In particular `FinitePushforwardConstructibleNoetherian` is a proof dependency,
  not this statement. Searching the node id in upstream sources gave no match.
- `rg` for the chosen declaration name in Mathlib, upstream sources,
  `dag/lean_names_upstream.json` and `lean/Sheaf` gave no collision.

Validation: the delivered module compiled cleanly with `scompile.py` on the server
(nice 19, two threads, 60-second per-file limit). No local Lean invocation or build
was run. The server automatically compiled side-only imported modules in its private
overlay. No warning other than the permitted sorry warning occurred.

## Second reading by NU

Independently read the node, its original blueprint source (order 1580), all four
statement-dependency nodes and their declarations, and the theorem with its six-step
proof docstring. The statement list and correspondence are:

1. A field k: `(k : Type u) [Field k]`. Correct; k is not assumed algebraically
   closed, perfect, or of a prescribed characteristic.
2. Schemes X and S and S of finite type over k: `{X S : Scheme.{u}}`,
   `[S.Over (Spec (.of k))]`, `[LocallyOfFiniteType (S ↘ Spec (.of k))]`, and
   `[QuasiCompact (S ↘ Spec (.of k))]`. Correct: the scheme-convention node explicitly
   defines finite type as locally finite type plus quasi-compact. The Mathlib class
   signatures in Morphisms.FiniteType and Morphisms.Finite were read directly.
3. A finite named morphism f: `(f : X ⟶ S) [IsFinite f]`. Correct: Mathlib IsFinite
   requires affine inverse images and finite ring maps. The composite with S's map
   supplies X's map to k; no independent compatibility or separatedness is imposed.
4. The ambient coefficients: `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]` and
   `(hcoeff : IsSmoothBaseChangeCoefficients N Λ S)`. Correct against the coefficient
   node and its blueprint source: unfolding gives precisely positive N, finite Λ,
   `(N : Λ) = 0`, and invertibility of N on S. Invertibility on X follows by the
   map on global sections induced by f. These are inherited conventions of this
   blueprint, even though Stacks' vanishing theorem holds more generally.
5. A constructible Lambda-module sheaf F on X_et:
   `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` and
   `(hF : @Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F)`.
   Correct. Read IsConstructibleEtaleModuleSheaf itself: it chooses a finite locally
   closed partition with scheme immersions, requires constructible strata, and on
   each stratum chooses an etale covering and finite constant module values with
   module-sheaf isomorphisms. This is the dependency node's exact notion. The finite
   instance is extracted from the coefficient hypothesis rather than assumed twice.
6. Constructibility of f_*F: the first conjunct is the same predicate at S on
   `((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)`. Correct. Opened lowerStar in
   UpperLowerStar.Defs: it is sheaf pushforward by the continuous base-change functor,
   with sections F(V ×_S X), not a different direct-image construction.
7. All positive higher direct images vanish: `∀ q : ℤ, 0 < q → IsZero` of
   `DerivedCategory.Plus.homologyFunctor` at q on `rightDerivedLowerStarPlus` of
   `DerivedCategory.Plus.singleFunctor` at zero applied to F. Correct. Opened
   UpperLowerStarCoherence and Mathlib's DerivedCategory.Plus: the former is the
   right derived functor of this same lowerStar, the single functor places F in
   degree zero, and homologyFunctor computes cohomology in degree q. IsZero concerns
   the resulting module sheaf, not its global sections or an underlying bare type.

Source checks: Stacks etale-cohomology.tex, proposition-finite-higher-direct-image-zero
(Tag 03QP), states vanishing for every positive degree for finite f, without a
surjectivity or nonemptiness assumption. Its finite-pushforward-constructible lemma
assumes finite presentation and a Noetherian coefficient ring; here S is Noetherian
by finite type over k, finite f is finitely presented over that base, and finite Λ
is Noetherian. Thus no extra finite-presentation binder is necessary. The present
source is the blueprint lemma, with its fixed finite coefficient convention.

Edge cases: empty X and empty S, zero module sheaf, and empty stratification on an
empty scheme are allowed. No surjectivity is required. q = 0 is excluded only from
vanishing; every positive integer degree is included. N = 0 is excluded by the
source's positivity convention. N = 1 and the zero coefficient ring are allowed
whenever the stated convention holds. No characteristic restriction is added beyond
invertibility of N. Universe u is arbitrary; coefficient/module universe u+1 is the
recorded dependency convention and permits the finite coefficients. There is no
independent test-object universe that could make a condition vacuous. All variables
and the single universe are explicitly bound.

Independent H4 searches (2026-10-15), using different queries from the worker:

- LeanFinder via msearch: "Finite scheme map sends constructible finite coefficient
  module sheaves to constructible sheaves with acyclic direct image" returned eight
  hits, about constructible subsets, finite ring maps and finite-type module sheaves;
  none states this node's two conclusions for etale module sheaves.
- Loogle via msearch: `AlgebraicGeometry.IsFinite, CategoryTheory.Sheaf` returned no hits.
- LeanSearch via msearch: "Finite map of schemes constructible sheaf of modules direct
  image and higher cohomology vanishing" was unavailable (Internal Server Error).
- rg of `constructible.*(lowerstar|direct.image|pushforward)` and the reverse ordering,
  case insensitive, and of the blueprint id across Mathlib, upstream WeilConjectures
  and this project's lean/Sheaf found no exact existing theorem. Opened upstream
  Finite.Exact: exactness and derived comparison are only part of the conclusion.
  Opened Derived/Stability/DirectImage's
  boundedConstructible_rightDerivedLowerStar_of_finite: "finite" refers there to
  coefficients, and its conclusion is bounded constructibility of a derived image,
  with no positive-degree vanishing. Opened this project's
  FinitePushforwardConstructibleNoetherian: its input/output are underlying set-sheaf
  constructibility for abelian sheaves, not the recorded module-sheaf predicate.
  These declarations are not replacements for this node's statement.

No mismatch was found. No Lean or node change was made; this independent review is
appended to the worker report. There are no new definition nodes or dependency
modules in this delivery, and no statement_change requiring a citer audit. The
single theorem has exactly one sorry and no proved additions or hollow definitions.
Its module/declaration docstrings cite the source and blueprint id; its proof plan
matches all six node steps. The node's lean.statement was checked verbatim against
the file signature, and every line satisfies the 100-character limit.

Validation: scompile.py on the server compiled the delivered file cleanly (nice 19,
two threads, 60 seconds per file), also compiling side-only imports in its private
overlay. No warnings or errors occurred. The first compile command used a relative
path from the read-only checkout and failed before any compiler invocation; rerunning
from this sandbox resolved that path error. No local compiler or lake build was used.
