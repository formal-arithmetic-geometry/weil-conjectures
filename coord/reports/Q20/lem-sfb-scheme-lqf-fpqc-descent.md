## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.IsLocallyQuasiFiniteOfFpqcCover` states
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_of_fpqcCover`, with proof `sorry`.
It is the descending direction of the locally quasi-finite assertion of Stacks
Tag 02VI, `descent.tex`, `lemma-descending-property-quasi-finite`; that source's
statement and proof were read. No definition or other theorem is introduced.
The node is changed only in `lean`.

Hypothesis and clause correspondence:

- Schemes and the arbitrary morphism `f : X → T`: `{X T : Scheme.{u}} (f : X ⟶ T)`.
- The family indexed by any set: `{I : Type v} (T' : I → Scheme.{u})`
  and `(g : ∀ i : I, T' i ⟶ T)`. Both universes are explicitly declared.
- The fpqc covering condition: `hcover : Presieve.ofArrows T' g ∈ Scheme.fpqcPrecoverage T`.
  This is exactly the recorded declaration of def-weil-pbc-fpqc-covering, including
  flatness and the finite affine-open image covering condition on every affine open
  of the target. Its quasi-compactness is a family condition; individual `g i` need
  not be quasi-compact. Read `fpqcPrecoverage`, `propQCPrecoverage`,
  `QuasiCompactCover`, and `QuasiCompactCover.exists_isAffineOpen_of_isCompact`:
  the latter explicitly recovers a finite list of affine opens with union of images
  equal to the specified compact open. Thus this encoding retains the node's
  equality-of-images condition as well as allowing repeated indices.
- The base change `f_i : X ×_T T_i → T_i` is the chosen second projection
  `pullback.snd f (g i)`.
- Every `f_i` locally quasi-finite: `h : ∀ i : I, (pullback.snd f (g i)).IsLocallyQuasiFinite`.
  This uses the project's Stacks predicate, not Mathlib's weaker predicate.
- Conclusion with local finite type: `f.IsLocallyQuasiFinite`. Unfolding the
  dependency gives quasi-finiteness at every point, whose affine witnesses include
  `Algebra.FiniteType`; no extra finite-type hypothesis is imposed on `f`.
- There are no quasi-compactness, separatedness, Noetherian, nonempty-index or
  individual-surjectivity hypotheses. These are explicit exclusions in the prose,
  correctly represented by their absence from the Lean signature.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (structure, local-affine field and Hom docstring).
- def-weil-pbc-fpqc-covering: `AlgebraicGeometry.Scheme.fpqcPrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`; also inspected its family-level
  quasi-compact condition in `Mathlib.AlgebraicGeometry.Cover.QuasiCompact` and
  `Mathlib.AlgebraicGeometry.Sites.QuasiCompact`.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- pqf-def-quasifinite: `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` and
  its constituent `IsQuasiFiniteAtPoint`,
  `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`. Read their full definitions
  and docstrings, including the affine finite-type clause.

Proof imports: `WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`
for lem-weil-pbc-lqf-locally-finite-type;
`Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover` for
lem-weil-pbc-fpqc-descend-locally-finite-type;
`Mathlib.CategoryTheory.Sites.Precoverage` for lem-galois-fpqc-covering-base-change
(`Precoverage.mem_coverings_of_isPullback`, with the fpqc stability instance).
The full signatures and docstrings of these were read. The remaining proof node
lem-sfb-scheme-quasifinite-at-base-change has no Lean record or Mathlib match in
this snapshot; its import is deferred until its statement lands, as required by
stage-2 rule 7. It is not needed to elaborate this statement. The theorem's docstring
retains all three proof steps and their precise DAG references.

Edge cases checked before writing:

- Empty source: the conclusion is a universal assertion over no points, and needs
  no nonemptiness hypothesis.
- Empty covering index: permitted, with `hcover` still required. An empty fpqc
  covering forces the target empty; a morphism to it also has empty source.
- Non-quasi-compact component morphisms: allowed, since no `QuasiCompact (g i)`
  binder is used and the fpqc definition imposes the family condition.
- Infinite disjoint unions of points: locally quasi-finite is not replaced by
  quasi-finite or finite type, so these are retained.
- Non-separated or non-Noetherian schemes: neither property appears in the
  definitions used or in the signature.
- Arbitrary index universe: `I : Type v` is independent of the scheme universe;
  this matches the fpqc-family interface and does not quantify over test schemes
  in a potentially vacuous smaller universe.

Searches actually run with msearch.py for this item:

- LeanFinder: `Local quasi finiteness including local finite type of scheme morphisms
  descends along fpqc covering families`: 8 hits, including
  `AlgebraicGeometry.LocallyQuasiFinite`, its multiplicativity and composition
  instances, `LocallyQuasiFinite.of_comp`, `locallyQuasiFinite_iff`, and the finite
  morphism implication. None is the requested descent theorem, and their basic
  predicate omits finite type (verified in Mathlib's source rather than the search
  service's approximate doc summaries).
- Loogle: `"LocallyQuasiFinite", "descends"`: 0 hits.
- Mathlib grep: `([Dd]escend.*[Qq]uasiFinite|[Qq]uasiFinite.*[Dd]escend|[Qq]uasiFinite.*[Ff]pqc)`:
  0 hits.
- Direct rg over both `lean/WeilConjectures` and `lean/Sheaf`:
  `IsLocallyQuasiFinite|isLocallyQuasiFinite|[Qq]uasiFinite.*fpqc|[Qq]uasiFinite.*[Dd]escen`;
  follow-up `(islocallyquasifinite.*(fpqc|descen)|((fpqc|descen).*islocallyquasifinite))`
  case-insensitively: existing predicate, composition/base-change and effective
  descent statements, but no exact scheme property descent theorem.
  `SeparatedLqfFpqcDescent` concerns effectiveness with separatedness, and
  `RepresentableLocallyQuasiFiniteCalculus` concerns representable stack maps;
  the latter's docstrings explicitly cite the present item as a prerequisite.
- The node-id grep in `lean/WeilConjectures` returned no match.
  The proposed full declaration name was also searched in `dag/lean_names_upstream.json`,
  Mathlib and both project source roots; no existing declaration was found.

No statement correction, missing notion, unusable dependency interface, or
STATEMENT-DISPUTED issue was found. No sub-agents were started; the maintainer
performs the independent review under the dispatcher's direct-delivery rule.

Validation: compiled through scompile.py; dry-run and delivery results are recorded
below after the wrappers complete.

The standalone scompile.py check passed both sandbox and module-name compilation
with no warnings. The deliver2.py --no-push dry run returned OK at 4f8cde0fc9b:
server preflight and per-file compilation passed. The only changed node field is
`lean`, and every Lean source line is at most 100 characters.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
