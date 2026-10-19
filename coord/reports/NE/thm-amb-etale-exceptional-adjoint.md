## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint` states
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
Its sole theorem has proof `by sorry`; no definition or proof is supplied.
The statement is unchanged, with no new nodes or dependency repairs.

Hypothesis and clause correspondence:

- A finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the coefficient universe of the recorded ordinary etale derived categories.
- The schemes and morphism are `{X S : Scheme.{u}} {f : X ⟶ S}`.
- The specified factorization is `(c : Compactification f)`. Its fields are
  `c.Z`, `c.i : X ⟶ c.Z`, `c.g : c.Z ⟶ S`, and `c.comm : f = c.i ≫ c.g`.
  Its instance fields `isOpenImmersion` and `isProper` give precisely the open
  immersion j and proper r; proper implies finite type (locally finite type and
  quasi-compact), so no extra finite-type assumption is necessary.
- Noetherian for each of X, the compactification scheme, and S is rendered by
  `[IsLocallyNoetherian X] [CompactSpace X]`, the corresponding pair for `c.Z`,
  and the corresponding pair for S. These are exactly the two parents of
  Mathlib's `AlgebraicGeometry.IsNoetherian`.
- Ordinary `Rf_! = Rr_* Dj_!` for this compactification is the dependency's
  `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c`.
  Its source and target are the full unbounded `DerivedCategory` of
  `Sheaf X.smallEtaleTopology (ModuleCat A)` and the analogous category for S.
- Having a right adjoint is `.IsLeftAdjoint`, whose sole field is existence of
  a functor and `Nonempty` of its adjunction. The name f-times is conventional
  notation for this adjoint, not additional structure required by the node.
- There is no boundedness, constructibility, finite Tor amplitude, or pro-etale
  condition on the input category or on its objects.

Dependency declarations read and used:

- `def-amb-etale-compact-support`: module
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, declaration
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
  Its body is the degreewise derived extension by zero followed by total right
  derived direct image, exactly as required.
- `def-weil-compactifications-refinements`: module
  `WeilConjectures.Compactification.Refinement`, declaration
  `AlgebraicGeometry.Compactification.Refinement` and its category instance;
  its public dependency `WeilConjectures.Compactification.Defs` supplies
  `AlgebraicGeometry.Compactification` used here.
- `def-weil-pbc-derived-categories`: module
  `Sheaf.AlgebraicGeometry.DerivedCategories`, recorded declaration
  `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` and recorded
  existing `AlgebraicGeometry.Etale.DerivedCategoryModule`. The latter's
  definition is exactly the derived category in the compact-support functor's
  signature; torsion cohomology is not imposed as an extra hypothesis.

The module imports the available recorded proof-dependency modules without
`public`; exact extension by zero and its adjunction share the upstream module
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
The Mathlib exact-functor and K-injective modules supply the recorded Mathlib
proof leaves. `lem-kun-grothendieck-derived-coproducts` has no recorded module,
so its future proof import is deferred. This does not obstruct stating this node.
The theorem docstring carries all four proof steps of the node, including the
K-injective cone argument and Brown representability.

Edge cases checked: the zero coefficient ring is permitted; the empty schemes
and identity compactification are permitted; no Nonempty assumption is added.
All complexes are unbounded and arbitrary. The Noetherian hypotheses apply to
all three schemes. No absolute dimension or common-bound hypothesis is added.
The theorem has no index-universe binder that could restrict the conclusion.
All universes and variables are explicitly bound. No statement dispute found.

Searches performed:

- `msearch.py ... leanfinder "ordinary derived etale compact support functor has a right adjoint"`:
  eight unrelated condensed adjunction hits; no matching theorem.
- `msearch.py ... loogle "CategoryTheory.Functor.IsLeftAdjoint"`:
  twelve hits, including the exact abstract existence predicate, its chosen
  right adjoint and `Adjunction.ofIsLeftAdjoint`; no geometric theorem.
- `msearch.py ... grep "rightDerivedLowerShriek.*[Aa]djoint|[Aa]djoint.*rightDerivedLowerShriek"`:
  zero Mathlib hits.
- Direct `rg` of exceptional/right-adjoint names and the blueprint id in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` in
  `SixFunctors/Etale/Derived/UpperShriek.lean`, lines 86–100. Its full signature
  and docstring were read. It asserts existence for the *chosen*
  `HasCompactification.compactification f`, under only `[HasCompactification f]`.
  It does not assert the fixed arbitrary compactification version of this node;
  using it would require a compactification comparison, explicitly avoided in
  the node's proof. Thus it is not an exact existing match.
- Direct `rg` in `lean/Sheaf` found no matching fixed-compactification adjoint.
  The proposed full name was also checked in Mathlib, the upstream tree,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`, with no collision.

Validation: `scompile.py NE thm-amb-etale-exceptional-adjoint` compiled the
module cleanly, including the required side overlay, with no errors or warnings.


## Second reading by NE

I independently read the item, all three statement-dependency nodes and their
recorded declarations, the blueprint source, and Stacks injectives.tex,
proposition-brown (Tag 0F5Y, lines 2803–2824). That proposition assumes a
Grothendieck abelian source category, a triangulated target, and an exact
coproduct-preserving functor. Its conclusion supplies a right adjoint; it adds
no geometric hypotheses. The node specializes this input by its four proof
steps. I checked the module docstring and theorem docstring against those steps.

Object/hypothesis/conclusion checklist:

- Finite commutative coefficient ring A: `(A : Type (u + 1)) [CommRing A]
  [Finite A]`. Exact match, including the zero ring and every characteristic.
- Schemes X and S and their morphism f: `{X S : Scheme.{u}} {f : X ⟶ S}`.
  Exact match; no base field, separatedness of the schemes, or dimension bound.
- A specified factorization through the compactification scheme: `(c :
  Compactification f)`, whose actual upstream definition has `Z`, `i`, `g`,
  and `comm : f = i ≫ g`. Exact match; c remains universally quantified and
  is not replaced by `HasCompactification.compactification f`.
- j open: `c.isOpenImmersion : IsOpenImmersion c.i`. Exact match. The
  upstream structure does not demand quasi-compact j, but here the Noetherian
  hypotheses imply it; this therefore loses no compactification condition.
- r proper of finite type: `c.isProper : IsProper c.g`. Exact match:
  Mathlib IsProper includes LocallyOfFiniteType and UniversallyClosed, hence
  quasi-compactness, and thus finite type. No extra hypothesis is needed.
- All three schemes Noetherian: each of X, c.Z and S has both
  `[IsLocallyNoetherian ...]` and `[CompactSpace ...]`. Exact match to the
  two parent fields of Mathlib `AlgebraicGeometry.IsNoetherian`, verified in
  Noetherian.lean:280. No merely locally Noetherian case is silently admitted.
- Ordinary compact support for this c: the actual body of
  `rightDerivedLowerShriekOfCompactification` in Derived/LowerShriek.lean:96
  is `D((c.i)_!open[A]) ⋙ R((c.g)_*[A])`. Specializing its coefficient
  category to `ModuleCat.{u + 1} A` is precisely Rr_* Dj_! of the node.
- Ordinary unbounded derived module-sheaf categories: that declaration's
  source and target are `DerivedCategory (Sheaf T.smallEtaleTopology
  (ModuleCat.{u + 1} A))`. I also opened DerivedCategories.lean and the
  upstream Coefficients.lean definition of `DerivedCategoryModule` (line 52):
  these are the same categories, without a torsion-cohomology, boundedness,
  constructibility, Tor-amplitude, or pro-etale condition.
- Existence of a right adjoint f-times: `.IsLeftAdjoint` is exactly the
  Mathlib class with field `∃ right, Nonempty (left ⊣ right)` (Basic.lean:134).
  The node asks for existence, not an independently specified functor or
  additional preservation property. Exact match; quantifiers have the same
  order and the existence is on the whole ambient categories.

Edge cases: the empty scheme and identity compactifications are allowed;
there is no Nonempty or nonzero assumption. Zero objects and arbitrary
unbounded complexes belong to the ambient categories. There is no degree n
or index set binder to exclude degree zero or the empty coproduct. Coefficients
have unrestricted characteristic. The common scheme universe u and module
universe u+1 follow the actual recorded small-etale-site and coefficient
interfaces; a finite ring can always be represented in that universe. No
independent too-small testing universe or hidden site-universe equality is
introduced. All variables and universes are bound explicitly.

Independent searches (2026-10-15): msearch LeanFinder query "right adjoint of
compactification derived extension by zero proper pushforward etale modules"
returned eight underived module pushforward/restriction or condensed results,
not this statement. Loogle `CategoryTheory.Functor.IsLeftAdjoint` returned the
abstract existence class and transport lemmas, not the geometric theorem.
LeanSearch query "Existence of a right adjoint to derived proper pushforward
of finite etale coefficient sheaves" failed with Internal Server Error;
this is unavailable evidence, not a negative result. Direct rg searches in
Mathlib, the upstream WeilConjectures tree, and project lean/Sheaf used
`isLeftAdjoint.*(LowerShriek|lowerShriek)`, exceptional-adjoint names and the
blueprint id. I opened the upstream UpperShriek.lean instance at lines 86–100
and its surrounding binders: its functor is for the chosen compactification
under HasCompactification f, not this arbitrary specified c. It is therefore
not an exact existing match. The open-immersion adjoints and pro-etale
exceptional-adjoint data likewise are different assertions. There is no
second definition: this module only states a theorem using the recorded
compactification and compact-support constructions.

No new definition nodes, dependency modules, or statement correction are
present. No mismatch requiring a Lean or node edit was found; I preserved
the correct statement and docstrings. The single theorem has only `sorry`
as proof, and there is no definition with postponed data. I verified by
literal comparison that lean.statement is the file's exact signature.
The second reading adds this report only. Compilation and delivery-preflight
results are recorded below.

Validation: the independent scompile.py run compiled the sandbox and library
module cleanly (1.8 s and 1.9 s), with no errors or warnings. deliver2.py
--no-push printed OK: preflight and compiles passed, nothing pushed.
