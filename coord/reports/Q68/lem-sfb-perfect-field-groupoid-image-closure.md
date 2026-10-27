## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectFieldGroupoidImageClosure` states
`AlgebraicGeometry.exists_reduced_image_groupoid_of_perfectField`, with its whole proof
`sorry`. No definition, dependency record, accepted stage-1 split, or natural-language
statement is changed. There are no new nodes. The inherited failure concerned a stage-1
unchanged-node submission; the current stage-2 queue lists the item and the live node has
no Lean record. This packet supplies that missing record and statement.

The source read is Stacks Project, `more-groupoids.tex`, Tag 04Q8
(`lemma-map-groupoids-on-perfect-field-image`), its setup and the preceding Tag 04Q7.
These apply to groupoids on a field spectrum, with no finiteness conditions. The absolute
version is obtained over Spec Z; no common k-linear structure on source and target is
assumed.

Hypothesis and conclusion correspondence:

- The field and its spectrum are `(k : Type u) [Field k]` and
  `Spec (CommRingCat.of k)`. The perfectness assumption is `[PerfectField k]`.
  Mathlib uses separability of every irreducible polynomial, equivalently the source's
  surjectivity of Frobenius in positive characteristic; characteristic zero is included.
- The two arrow schemes are `{R₁ R₂ : Scheme.{u}}`. Each supplied septuple has source,
  target, unit, inverse and composition as the binders `s₁ t₁ e₁ i₁ c₁` and
  `s₂ t₂ e₂ i₂ c₂`, with `h₁` and `h₂ : IsGroupoidScheme ...` giving every groupoid law.
  `IsGroupoidScheme` is the exact recorded absolute definition, on all test schemes.
- The morphism over the identity on objects is `a : R₁ ⟶ R₂`, with `hs` and `ht`
  commuting with source and target, `he` commuting with the unit, `hi` commuting with
  inversion, and `hc` commuting with composition. The pullback map in `hc` is the
  canonical induced map with both arrow components `a` and object component identity.
  Its proof arguments follow from `hs`, `ht`, and composition with the identity.
- The reduced closed subscheme exists as `∃ (Z : Scheme.{u}) (j : Z ⟶ R₂)`, with
  `IsClosedImmersion j` and `IsReduced Z`. Its underlying support is precisely
  `Set.range j = closure (Set.range a)` in the Zariski topology.
- The specified reduced induced structure is the equality
  `j.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range a), isClosed_closure⟩`.
  The Mathlib vanishing ideal, read in `IdealSheaf/Basic.lean`, has on each affine open
  the intersection of the primes lying in that closed subset. Thus it is precisely the
  ideal of functions vanishing at every one of those points. For a closed immersion
  `j` its `ker` agrees with its defining affine ideals: closed immersions are
  quasi-compact, so `Scheme.Hom.ker_apply` applies without any extra assumption on `a`.
- Restricted source and target are the actual composites `j ≫ s₂` and `j ≫ t₂`.
  The existential `e i c` gives the restricted unit, inverse and composition, with
  `c : pullback (j ≫ s₂) (j ≫ t₂) ⟶ Z`. Their laws are exactly
  `IsGroupoidScheme (j ≫ s₂) (j ≫ t₂) e i c`.
- Compatibility of `(id,j)` with unit and inversion is `e ≫ j = e₂` and
  `i ≫ j = j ≫ i₂`. Compatibility with composition is `c ≫ j = ... ≫ c₂`, where
  `...` is the canonical `pullback.map` induced by `j,j,id`. Source and target
  compatibility are expressed definitionally by the chosen composites.
- The identity case is included by specializing `R₁ = R₂`, the same five maps, and
  `a = 𝟙 R₂`. Then the image closure is all of `R₂`, and
  `Scheme.IdealSheafData.vanishingIdeal_top` identifies the displayed kernel with
  `R₂.nilradical`. Uniqueness of the reduced closed structure, in the recorded
  reduced-induced-closed-subscheme theorem, identifies `j` with
  `R₂.nilradical.subschemeι`; the operations transport across this isomorphism.
  Thus the canonical reduction inherits the asserted operations, without an
  added assumption that `R₂` is reduced.
- There is no finite-type, quasi-compactness, separatedness, flatness, characteristic,
  or equality-of-source-and-target hypothesis beyond perfectness. Every variable and
  the universe `u` are explicitly bound. No local notation or local instance is used.

Dependency declarations read and used:

- `Field` in `Mathlib.Algebra.Field.Defs`; `AlgebraicGeometry.Spec` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `AlgebraicGeometry.IsGroupoidScheme` in `Sheaf.AlgebraicGeometry.GroupoidScheme`:
  all six structural equations and all five laws on test-scheme points were read.
- `AlgebraicGeometry.IsReduced` in `Mathlib.AlgebraicGeometry.Properties` and
  `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- Reduction uses `Scheme.nilradical` in `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`
  and `Scheme.IdealSheafData.subscheme` / `subschemeι` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`. These are publicly available
  through the closed-immersion import. `vanishingIdeal`, `vanishingIdeal_top` and
  `Scheme.Hom.ker` in the same Mathlib ideal-sheaf API give the affine ideal description.
- `CategoryTheory.Limits.pullback`, `pullback.map` and the projections from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, available through
  the recorded groupoid module's public pullback import.
- Proof imports are the recorded
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
  (`Scheme.IdealSheafData.reduced_induced_closed_subscheme`),
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
  (`IsClosedImmersion.existsUnique_fac_of_range_subset_range`), and
  `WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced`
  (`isReduced_tensorProduct_of_perfectField`). The Mathlib proof leaves use
  `pullbackSpecIso`, `Scheme.pullback_map_isOpenImmersion`, and
  `Scheme.Pullback.range_map` in `Pullbacks` / `PullbackCarrier`.
  The proof dependency `lem-sfb-scheme-product-image-closure` has no Lean record yet,
  so it has no import; it remains in the unchanged proof plan and the docstring.

Edge cases checked before writing: characteristic zero and positive characteristic
perfect fields are both covered by `PerfectField`; the two k-structures may differ;
nonreduced arrow schemes remain allowed; the identity morphism gives the reduction
rather than forcing the original scheme to be reduced; no finite-type or compactness
assumption is introduced. An empty arrow scheme cannot satisfy the unit hypothesis
because the object field spectrum is nonempty. Thus the apparent empty-image case is
excluded by the actual groupoid data, not by a new hypothesis. Pullback maps have the
specified projections, so composition compatibility is not an arbitrary-map condition.

Searches for an existing theorem:

- `msearch.py leanfinder`, query “The reduced closure of the image of a morphism of
  groupoid schemes over a perfect field inherits the groupoid operations”: eight hits
  concern reduced schemes, image schemes, local closures and ordinary subgroupoids;
  none states this scheme-groupoid result.
- `msearch.py loogle`, query `"Groupoid", "closure"`: zero hits.
- `msearch.py grep`, query
  `groupoid.*closure|closure.*groupoid|groupoid.*reduc|reduc.*groupoid`: zero Mathlib hits.
- `msearch.py leansearch`, query “The closure of the image of a morphism of scheme
  groupoids over a perfect field has a reduced subgroupoid structure”: eight hits on
  support of kernels, reduced schemes and scheme images; none is the assertion.
- `rg` with the same groupoid/closure/reduction patterns and `IsGroupoidScheme` in
  `lean/WeilConjectures` and `lean/Sheaf`: groupoid definitions and unrelated invariant
  strata/orbit constructions; no theorem on reduced image closures. Searching the
  node identifier in `lean/WeilConjectures` gives no match. The proposed declaration
  name does not duplicate any source declaration.

Validation: the prescribed `scompile.py` compiled the module both as the isolated
sandbox file and under its delivery module path, cleanly (1.5 seconds each). The
remaining dry-run and delivery results are recorded below when available.

There is no statement dispute or correction, no new node, and no dependency-module
repair. The only postponed theorem is the named theorem of this item; its docstring
contains every step of the accepted seven-step proof plan.

Delivery validation: `deliver2.py Q68 lem-sfb-perfect-field-groupoid-image-closure
--no-push` returned `OK (dry run)` after the server preflight and per-file compile.
Only the item's `lean` record changes; the module has no lines over 100 characters.
The report is submitted for the maintainer's independent review; no independent
second reading is claimed by this worker.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
