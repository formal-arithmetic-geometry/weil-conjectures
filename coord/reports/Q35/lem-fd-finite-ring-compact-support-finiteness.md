## Worker report

The new module `Sheaf.AlgebraicGeometry.FiniteRingCompactSupportFiniteness` states
`AlgebraicGeometry.Etale.finiteRingCompactSupportFiniteness`, with one postponed theorem
and no new definitions. The node is unchanged except for its `lean` record. There are no
new nodes, dependency repairs, statement corrections, or disputed statements.

Hypothesis and conclusion correspondence:

- Any field k: `(k : Type u) [Field k]`; schemes are `{X Y : Scheme.{u}}`.
- Y of finite type over k: `[Y.Over (Spec (.of k))]`, together with
  `[LocallyOfFiniteType (Y ↘ Spec (.of k))]` and
  `[QuasiCompact (Y ↘ Spec (.of k))]`. No separatedness over k is required.
- Finite-type f: `(f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]`.
- The supplied factorization is `(c : Compactification f)`: `c.Z` is the ambient scheme,
  `c.i` is open, `c.g` is proper, and `c.comm : f = c.i ≫ c.g`. The upstream structure
  does not impose quasi-compactness of c.i, but `c.quasiCompact_openImmersion` derives it
  from the already assumed quasi-compactness of f. Thus the recorded Nagata notion is
  used without changing the admissible data in this theorem.
- The assertion that f is separated is the first conjunct `IsSeparated f`; it is a
  conclusion, not a hypothesis.
- Any finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This includes the zero ring and every characteristic, with no localness, invertibility,
  or finite-Tor-amplitude restriction.
- Ordinary small-etale module derived categories are `DerivedCategoryModule Λ X` and
  `DerivedCategoryModule Λ Y`, definitionally unbounded derived categories of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
- The exact prescribed compact-support functor is the existing
  `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c`, whose real body is
  `D(openImmersionLowerShriek _ c.i) ⋙ R(lowerStar _ c.g)`. This uses the total derived
  pushforward after the exact functor induced by extension by zero.
- For every bounded constructible M, the second conjunct asserts
  `DerivedCategory.isBoundedConstructible Λ Y` of that functor's value, under exactly
  `DerivedCategory.isBoundedConstructible Λ X M`.
- The last conjunct is `∃ N : ℕ, ∀ M, ... → ∀ a b : ℤ, ...`.
  It makes N nonnegative and independent of M and both proposed endpoints. Vanishing
  outside [a,b] is `∀ i : ℤ, (i < a ∨ b < i) → IsZero (...)`; the output replaces b by
  `b + (N : ℤ)` and leaves a unchanged. The cohomology is the recorded
  `_root_.DerivedCategory.homologyFunctor`. No extra order assumption on a,b is needed:
  the same assertion includes the zero-object case of a reversed interval.

Recorded statement dependencies read and used:

| Node | Module / declarations |
| --- | --- |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact` |
| def-nagata-compactification | `WeilConjectures.Compactification.Defs`, `AlgebraicGeometry.Compactification` |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`, `IsSeparated` |
| def-weil-pbc-etale-sheaves | `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, ordinary small-etale sheaf convention, `CategoryTheory.Sheaf` with `ModuleCat` coefficients |
| def-weil-pbc-derived-categories | `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `DerivedCategoryModule` (defined in its imported `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`), `DerivedCategory.homologyFunctor` |
| def-weil-pbc-extension-by-zero | `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `openImmersionLowerShriek` |
| def-weil-pbc-direct-image | `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `lowerStar`; total derived pushforward in the existing compactification functor |
| def-weil-pbc-constructible-complexes | `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, `DerivedCategory.isBoundedConstructible` |

The existing functor's defining module
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` is imported publicly; it supplies
both constituent statement-dependency functors transitively. Recorded proof dependency
modules are imported non-publicly, including the fibre-dimension bound, proper torsion
cohomological-dimension bound, coefficient-forgetting comparison, compactification
constructibility, exact-functor homology, Noetherian and morphism permanence results,
module-category injective and Grothendieck results, K-injective resolutions, bounded-below
comparison, and truncation spectral sequence. Their full eight-step application is in
the theorem docstring, copied from the node proof. No proof is supplied at stage 2.

Source inspection: read the local Stacks `more-etale.tex` section
`section-derived-lower-shriek-compactification`, `theorem-constructible-shriek` (0GL0), and
`lemma-derived-lower-shriek-bounded` (0G2A), including clause (3) and its proof. The former
allows any Noetherian torsion ring, hence every finite commutative ring. The latter gives
the cohomological interval bound without an invertibility assumption. Read the full
compactification structure and its quasi-compactness lemma, the functor body, and the
recorded bounded-constructible predicate. Used `scompile.py --source` for the current
DerivedCategories and BoundedConstructibleComplexes sources where the older checkout
was missing or potentially stale.

Edge cases checked before writing: empty X or Y (the input is zero when X is empty; a morphism to empty Y forces X empty), the
zero coefficient ring (every module is zero), M=0, a=b, negative a and b, reversed
intervals, N=0, coefficients of the residue characteristic, nonlocal finite rings,
and finite-type Y not separated over k. No binder excludes any of these. The field and
schemes have the established common universe u, the small-etale objects and module
values have size u+1, and all variables and universes are explicitly bound.

Searches (2026-10-18; raw msearch results are retained in the sandbox searches.jsonl):

- `msearch.py leanfinder`: “For every finite commutative ring compact support direct image
  of etale sheaves preserves bounded constructible complexes with a uniform cohomological
  bound”. Eight hits about the etale locus, affine limits, condensed locally constant
  modules, constructible subsets and supported complexes; none states this theorem.
- `msearch.py loogle`: `"constructible", "shriek"`; zero hits.
- `msearch.py grep`: `boundedConstructible_rightDerivedLowerShriek|constructib.*shriek|shriek.*constructib`;
  zero hits in Mathlib.
- `msearch.py leansearch`: “Compact support direct image preserves bounded constructible
  etale complexes over an arbitrary finite commutative ring and has a uniform cohomological
  bound”. Eight hits about compactly supported functions, etale ring maps and compact
  scheme fibres; none matches.
- `rg` over upstream WeilConjectures and project Sheaf for the item id and proposed
  declaration names found no existing theorem. A broader search found
  `isBoundedConstructible_compactSupport_and_baseChange` in CompactBoundedConstructibleBaseChange:
  its full signature was read; it restricts coefficients to a prime field with invertible
  characteristic and contains a base-change conclusion, so it does not state this item.
- `rg` of `dag/lean_names_upstream.json`, Mathlib, upstream and Sheaf for the new full-name
  components found no collision. The existing bounded-constructible predicate and existing
  unbounded compact-support functor are reused, without duplicate definitions.

Validation: prescribed scompile.py file-only compile passed with no errors or warnings
(sandbox 11.4 s, library 23.4 s). deliver2.py --no-push passed both compilation and
the server preflight: OK, dry-run commit dfbdd11f5f. The delivery wrapper repeats
these checks on the final packet before pushing.

## Second reading by Q35

Independent maintainer reading, 2026-10-18, of immutable delivery
50f1325bd80784558d748540f88470c8e1b6dfb7. The maintainer is filling this required
section; this does not assert that a second Q35 worker read the delivery.

I read the item, all eight statement-dependency snapshot records, the complete delivered
module and report, the source passages, and the definitions behind the statement.
The Lean says exactly what the node says:

- Arbitrary field and schemes: `(k : Type u) [Field k] {X Y : Scheme.{u}}`.
  `[Y.Over (Spec (.of k))]` supplies the structure map; its locally-finite-type and
  quasi-compact instances say precisely that Y is finite type over k.
- The two corresponding instances on f say finite type. Neither structure-map
  separatedness nor a separate structure map on X is assumed: X inherits the composite.
- `c : Compactification f` supplies the ambient scheme, open immersion, proper map and
  factorization equality. The existing structure omits quasi-compactness of its open
  immersion, but `Compactification.quasiCompact_openImmersion` derives it from the
  already supplied `QuasiCompact f`. Thus it also realizes the dependency node's
  quasi-compact-open convention in this context.
- `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` permits every finite commutative ring.
  There is no local-ring, nontriviality, invertible-exponent or Tor-amplitude instance.
- `DerivedCategoryModule` is the unbounded derived category of ordinary small-etale
  `ModuleCat`-valued sheaves. The recorded bounded-constructible predicate expands to
  constructibility of every integer-degree cohomology sheaf and vanishing outside some
  finite interval with ordered endpoints. Its constructibility predicate uses a finite
  locally closed partition with constructible strata and finite constant module values.
- The existing `rightDerivedLowerShriekOfCompactification` has the real body
  `D(openImmersionLowerShriek _ c.i) ⋙ R(lowerStar _ c.g)`. Extension by zero is the
  sheafified left Kan extension along the localization functor; direct image is
  precomposition with base change. The derived factor is the ordinary total right
  derived functor. This is exactly the specified functor, without a pro-etale replacement.
- The first conjunct concludes `IsSeparated f`. The second quantifies over all bounded
  constructible inputs and concludes bounded constructibility of this precise output.
- The last conjunct chooses `N : ℕ` before `M`, `a`, and `b`. The integer-degree
  `homologyFunctor` and `IsZero` conditions express vanishing outside [a,b] and
  [a,b+N] respectively. The lower endpoint is unchanged. The bound is independent of
  all three later variables. Quantification over reversed intervals only adds a
  redundant zero-input case and changes no mathematical content.

Source checks: `more-etale.tex`, section-derived-lower-shriek-compactification (line 3047),
Tag 0G2A, lemma-derived-lower-shriek-bounded (line 3574, clause 3 and proof), and Tag 0GL0,
theorem-constructible-shriek (line 4711 and proof). A finite ring is both Noetherian and
torsion. Finite type over a field makes Y, X and the proper ambient scheme Noetherian,
hence qcqs; finite-type morphisms here are finitely presented. No absolute separatedness
is needed. Tags 01L4 and 01KU(1) justify the separatedness conclusion. Tag 0A3V gives
one bound d for the proper map's fibres; Tag 095U gives the torsion bound 2d without
invertibility. The coefficient-forgetting isomorphism transfers it to module sheaves.
The bounded-below/unbounded comparison and the finite convergent truncation spectral
sequence give precisely the claimed interval [a,b+2d]. All eight proof steps appear in
the theorem docstring. The constructibility dependency's exact signature uses this same
compactification functor and this same constructibility predicate.

Edge cases: zero ring, nonlocal rings, coefficients in the residue characteristic,
zero input, empty source, empty target, N=0, a=b, negative degrees, reversed intervals,
and schemes not separated over k. If X is empty its input category is zero; Y may
still be nonempty. If Y is empty then X is empty. No binder excludes these cases.
All variables are bound; the common scheme/field universe u and coefficient/module
universe u+1 are the recorded small-etale convention. No new universe equality or
size restriction was imposed to evade an API problem.

Independent searches: LeanSearch for "Finite torsion coefficients: proper pushforward
after extension by zero preserves constructible bounded cohomology with a uniform degree
bound" returned constructible-set bounds, generic Ext and presheaf pushforward results,
not this theorem. Loogle for `"constructible", "support"` returned no results. Direct
`rg` searches of Mathlib, upstream WeilConjectures and project Sheaf for constructibility
with proper/compact/shriek, and for boundedConstructible_rightDerivedLowerShriek, found
related results but no exact duplicate. I opened the upstream finiteness theorem: it
requires `HasInvertibleExponent Λ X` and lacks this uniform-bound conclusion. The project
CompactBoundedConstructibleBaseChange theorem uses an invertible prime-field coefficient
ring. Neither can replace this declaration. Existing notions are reused; no definition
or helper was added by this delivery.

Mechanical checks: the immutable node, module and report bytes match the named commit.
Only the lean record was added to the node; there is no statement correction requiring a
citer audit. Its `lean.statement` equals the source signature verbatim. There is exactly
one theorem with proof `by sorry`, no local proof or new definition, and no line over
100 characters. Source-place and blueprint module/declaration docstrings are present.
No statement/proof dependency intersects origin/newtargets-dag:coord/route-pivot-dropped.txt;
there is no repair note for this item at that ref. The proof uses the ordinary derived
route and introduces no dropped machinery.

Compiler reproduction: ran the prescribed scompile.py Q35
lem-fd-finite-ring-compact-support-finiteness on the immutable snapshot module.
Exit code 0; sandbox 7.1 s and library 4.6 s; neither output contained errors or warnings.
The installed wrapper identifies itself as the 2026-10-17 server-overlay implementation;
these are server-side overlay results, not a claim of a local compile. Also read the
current DerivedCategories, BoundedConstructibleComplexes and TruncationHypercohomology
sources through scompile.py --source to resolve checkout gaps. The delivery separately
records successful sandbox/library compilation and preflight; this review independently
reproduced the per-file compile. No global build, direct ssh command, project edit,
claim, delivery or merge was performed.

Finding H11: the delivered Second reading section was only a placeholder. Replaced it
with this actual independent reading. Also clarified the worker's empty-source wording:
empty X does not force all sheaves on Y to vanish. No mathematical, Lean-signature,
node-record, missing-helper or universe repair was needed. This complete report replaces
the delivered report; the Lean module and node remain as delivered.
