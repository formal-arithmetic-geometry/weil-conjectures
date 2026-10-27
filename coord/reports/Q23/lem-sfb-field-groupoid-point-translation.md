## Worker report

The module `Sheaf.AlgebraicGeometry.FieldGroupoidPointTranslation` states
`AlgebraicGeometry.exists_fieldGroupoid_pointTranslation`, with `sorry` as its entire
proof. It introduces no definitions. The accepted split, dependencies and source are
unchanged. The source was read in `literature/stacks-project/more-groupoids.tex`,
lines 1111–1189, Stacks Tag 04LS, including both inverse computations.

Hypotheses and conclusions, clause by clause:

- The field is `(k : Type u) [Field k]`; the base scheme is exactly
  `Spec (CommRingCat.of k)`, rather than an arbitrary scheme or a relative group scheme.
- The arrow scheme is `{R : Scheme.{u}}`, and the five structure maps are explicitly
  bound as `s t`, `e`, `i`, `c : pullback s t ⟶ R`. The hypothesis
  `hG : IsGroupoidScheme s t e i c` is the recorded absolute groupoid structure.
- The point is `(r : R)`. The assumptions `hs : IsIso (s.residueFieldMap r)` and
  `ht : IsIso (t.residueFieldMap r)` are exactly invertibility of the two residue
  maps. Mathlib gives their domains as the residue fields at `s r` and `t r` in
  `Spec k`; these are canonically `k`. Composing a map with this canonical
  identification does not change whether it is an isomorphism.
- `∃ (u v : Spec (CommRingCat.of k) ⟶ R)` supplies the two sections. The first
  two conjuncts assert `∀ z, u z = r` and `∀ z, v z = r`, respectively. Since a
  field spectrum is nonempty and has one point, these say precisely image `{r}`.
- `u ≫ s = 𝟙 (Spec (CommRingCat.of k))` and `v ≫ t = 𝟙 ...` are the two section
  identities, with Lean's left-to-right composition convention.
- The witness `θ : Spec k ≅ Spec k` and equality `u ≫ t = θ.hom` say that
  `t ∘ u` is an automorphism. The next equality `v = θ.inv ≫ u` says
  `v = u ∘ (t ∘ u)⁻¹`.
- The witness `L : R ≅ R` is a scheme automorphism, including both inverse laws.
  The first universally quantified test-scheme clause, for every `T : Scheme.{u}`
  and `x : T ⟶ R`, states
  `x ≫ L.hom = pullback.lift (x ≫ t ≫ u) x h ≫ c`.
  Thus its first arrow is `u ∘ t ∘ x`, and its second is `x`, exactly as in the
  node. The existential equality `h` is just the composability certificate;
  its existence follows from `u ≫ s = 𝟙 _`, so this adds no assumption.
- The second test-scheme clause states
  `y ≫ L.inv = pullback.lift (y ≫ t ≫ v ≫ i) y h ≫ c`, exactly
  `c(i ∘ v ∘ t ∘ y, y)`. Its composability certificate follows from
  `i ≫ s = t` and `v ≫ t = 𝟙 _`. Both formulas refer to the SAME isomorphism.
- Finally `e ≫ L.hom = u` is `L_r ∘ e = u`. Together with the first image
  conjunct it gives the asserted image of the identity point. No separate
  redundant point-image conjunct is needed.
- There is no finite-type, reducedness, separatedness, characteristic, or
  algebraic-closure assumption. All variables and the universe are explicitly bound.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.GroupoidScheme`:
  `AlgebraicGeometry.IsGroupoidScheme`, full signature, docstring and every law.
- `Mathlib.Algebra.Field.Defs`: `Field`, supplied through the public imports.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`. The proof prerequisites are already in this same
  public module: `Scheme.SpecToEquivOfField`,
  `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`,
  `Scheme.fromSpecResidueField_apply`, and
  `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`. Their full signatures
  and surrounding docstrings were read; no additional proof-only module is needed.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  `pullback.lift`, supplied through the public groupoid module, which also supplies
  scheme pullbacks. No private copy of any dependency notion is used.

Edge cases checked mathematically before writing: the identity-only groupoid gives
identity translation; a field spectrum cannot be empty, so the image clauses are
nonvacuous; an empty arrow scheme has no point `r` and is legitimately excluded by
that input. For a pair groupoid over a smaller field with a nontrivial automorphism
of `k` (for example Frobenius on F₄ over F₂), the two sections can differ, so neither
`u = v` nor `θ = 𝟙 _` is imposed. The source and target are not assumed equal.
The inverse formula uses `v` followed by `i`, in the correct order. The test universe
contains `R` itself; applying the formula to its identity already determines the
scheme morphism, so the test-point presentation loses no morphism-level content.
Infinite-type groupoids and all characteristics are included.

Searches performed with `batch2/msearch.py Q23 lem-sfb-field-groupoid-point-translation`:

- LeanFinder: `A point of a groupoid scheme over a field with invertible source and
  target residue maps gives a translation automorphism`. Eight hits, including
  `Scheme.SpecToEquivOfField` and residue-field congruences; none states translation.
- Loogle: `"Groupoid", "Scheme"`. Zero hits.
- Mathlib grep: `groupoid.*translat|translat.*groupoid`. Zero hits.
- LeanSearch: `A groupoid scheme over the spectrum of a field admits translation
  by a point with invertible residue maps`. Eight hits, all concerning residue
  fields and field-valued points, not groupoid translations.
- Local `rg` in BOTH `lean/WeilConjectures` and `lean/Sheaf`:
  `groupoid.*[Tt]ranslat|[Tt]ranslat.*groupoid|field_groupoid|fieldGroupoid|` followed
  by the item ID. Only unrelated groupoid stabilizer-dimension and rank-filtration
  comments were returned. An item-ID search in `lean/WeilConjectures` found no hit.
- An exact declaration-name search in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` found no existing
  `exists_fieldGroupoid_pointTranslation`.

No statement dispute, new node, or dependency repair was necessary. The old blocked
ending was a stage-1 gate applied to the accepted split; the current queue assigns
stage 2 and the node has no Lean record. This is the handoff explicitly covered by
`coord/brief-stage2.md` §0; this delivery preserves the split.

Validation: the prescribed `scompile.py` compiled both its sandbox module and the
library-path module cleanly (3.9 seconds and 2.8 seconds respectively), with no
errors or unexpected warnings.

## Second reading by Q23

This is the author's second reading; the dispatcher explicitly forbids starting
another agent, and the maintainer supplies the independent delivery review.
I reopened the node and Lean file and checked every binder and conjunct against
the source. The section directions are `u ≫ s` and `v ≫ t`; the automorphism
relation is `u ≫ t = θ.hom`, and `θ.inv ≫ u` has precisely the required order.
The forward lift uses `(x ≫ t ≫ u, x)`, the inverse lift uses
`(y ≫ t ≫ v ≫ i, y)`, and the final identity is `e ≫ L.hom = u`.
The compatibility existentials are certificates for these actual fibre-product
lifts, rather than assumptions on test morphisms. The absolute groupoid dependency
supplies all the laws needed, with no extra finiteness hypothesis. No mismatch
was found and no statement change was made.
