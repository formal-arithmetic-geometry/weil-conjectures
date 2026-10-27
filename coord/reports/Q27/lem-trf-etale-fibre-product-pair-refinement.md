## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleFibreProductPairRefinement` states
`AlgebraicGeometry.etale_fibre_product_pair_refinement`. Its only theorem has
proof `sorry`; no definitions or additional nodes are needed. The DAG statement,
dependencies, proof and accepted stage-1 split are unchanged. The inherited BLOCKED
ending concerned stage 1; brief-stage2 §0 explicitly permits the stage-2 statement,
and the current queue lists this item at stage 2 without a Lean record.

Clause-by-clause correspondence:

- The four affine schemes are `S X M₁ M₂ : Scheme.{u}` with four `IsAffine`
  instances. This is the usual scheme-invariant expression that each is a spectrum;
  Mathlib's `IsAffine` is the assertion that its canonical map to `Spec Γ` is an iso.
- The two closed embeddings are `i₁`, `i₂` with `IsClosedImmersion` instances.
  The maps to `S` are `e₁`, `e₂`; agreement is `h : i₁ ≫ e₁ = i₂ ≫ e₂`.
  Only `e₂` is assumed étale, through `[Etale e₂]`.
- `P` is Mathlib's `pullback e₁ e₂`, with the actual projections
  `pullback.fst e₁ e₂` and `pullback.snd e₁ e₂`. The existential `s` is pinned
  to the canonical graph by `s = pullback.lift i₁ i₂ h`.
- `F₁` is `pullback (pullback.fst e₁ e₂) i₁`. The two identities for `t₁`
  uniquely characterize the induced section: its projection to `P` is `s`, and
  its projection to `X` is the identity. Thus no arbitrary section is substituted.
- The map `F₁ → X` is both `Etale` and `IsSeparated`; `t₁` is both
  `IsOpenImmersion` and `IsClosedImmersion`, exactly the open-and-closed section.
- The closed subset of `P` is the image under `F₁ → P` of `(Set.range t₁)ᶜ`.
  The explicit `IsClosed` conjunct and equality defining the carrier of `U₁`
  say that the open is obtained by deleting precisely this closed complement.
- `∀ x : X, s x ∈ U₁` says that it contains all of `s(X)`, so it is a
  neighbourhood for every point simultaneously. `s₁ ≫ U₁.ι = s` identifies
  the map from `X`. `Etale (U₁.ι ≫ pullback.fst e₁ e₂)` is the restricted
  first projection. `IsPullback s₁ (𝟙 X) (U₁.ι ≫ pullback.fst e₁ e₂) i₁`
  expresses `U₁ ×_{M₁} X ≅ X` scheme-theoretically with its specified map.
- The additional case is an implication `Etale e₁ → ...`, not an extra
  global hypothesis. It constructs `t₂` in `F₂`, with the same two projection
  identities, separated étale projection, and open-and-closed section. Its
  complement image is explicitly closed. The final open `U` is the complement
  of the union of the two specified closed subsets. Both restricted projections
  are étale, both squares are `IsPullback`, and `sU ≫ U.ι = s` gives the
  same compatible identification from `X` in both squares.
- `∀ x : X, IsIso (s.residueFieldMap x)` states that the canonical residue-field
  map induced by `s`, from `κ(s(x))` to `κ(x)`, is an isomorphism. It does not
  replace the canonical map by an arbitrary abstract field isomorphism.

Dependency declarations used and read:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its separatedness interface:
  `AlgebraicGeometry.IsSeparated`, whose diagonal is a closed immersion.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its documented
  `Limits.pullback`, `pullback.fst`, `pullback.snd` conventions for scheme base
  change. Its primary `moduleBaseChange` declaration concerns modules and is
  intentionally not applied to schemes; the record itself prescribes the pullback.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`; `IsAffine`
  from `Mathlib.AlgebraicGeometry.AffineScheme` is the spectrum characterization.
- Proof dependencies are imported: `pullback` and its universal property,
  `Etale.etale_isStableUnderBaseChange`, closed-immersion base-change stability,
  the affine-source separatedness instances, `Etale.of_comp`,
  `IsOpenImmersion.of_flat_of_mono`, `IsClosedImmersion.of_comp`,
  `IsOpenImmersion`, and `Etale.etale_comp`. Their signatures were read.
  The module docstring gives all seven DAG proof steps and the cited node ids.

Source checked: `literature/stacks-project/etale.tex`, Tag 024T,
`proposition-properties-sections` (3), including its graph-as-base-change proof.
It proves that a section of an unramified separated morphism is open and closed.
The node's complement removal then uses the actual open subscheme, not a reduced image.

Edge cases checked before stating: empty `X` gives empty fibres and empty deleted
sets, hence the full `P`; no inhabitance binder is imposed. Nonreduced `X` is
preserved because `IsPullback` is a categorical scheme square, not an equality of
point sets. If `e₁` is not étale only the first result is asserted. If both maps
are étale the union deletion retains every point of `s(X)`. The example of a
degree-two étale cover with a chosen section in the fibre deletes the other sheet.
Identity embeddings and maps require no exceptional case. All schemes share an
arbitrary explicit universe, and `autoImplicit` is disabled. No statement dispute
or correction was found.

Searches made using the prescribed `msearch.py` wrapper:

- LeanFinder: “An etale fibre product of affine schemes sharing a closed subscheme
  has an open neighbourhood obtained by deleting the complement of the graph
  section, with Cartesian closed immersion squares”. Eight hits, including
  `Scheme.instHasPullbacksEtale`, the separated diagonal-cover lemma,
  `FormallyUnramified.isOpenImmersion_diagonal`, and
  `IsImmersion.isPullback_toImage_liftCoborder`; none states this refinement.
- Loogle: `"Etale", "IsPullback"`: zero hits.
- Mathlib grep: `IsEtale.*pullback|Etale.*section|IsClopen.*range` in
  `AlgebraicGeometry`: zero hits.
- LeanSearch: “Open neighbourhood of a common closed subscheme in an etale
  fibre product obtained by removing the closed complement of a graph section”.
  Eight hits, consisting of basic-open, zero-locus, stalk and base-change facts;
  none states the node.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `fibre_product_pair_refinement|fiber_product_pair_refinement`: no matches.
  A broader search for étale refinement/closed-pair language returned unrelated
  sheaf refinement and ring-theoretic section-neighbourhood results.

Validation: the initial server compile found a carrier coercion ambiguity in
`Set (pullback e₁ e₂)`. Explicit `Scheme.{u}` annotations fixed it. The next
`scompile.py` passed both the sandbox and library module checks without warnings.
Final imports and explicit auto-implicit disabling are validated again by the
delivery dry run.

## Second reading by Q27

This is a second clause-by-clause self-audit with the node and file open; no
independent worker was started, as the dispatch expressly prohibits other agents.
The maintainer supplies the independent review. The audit checked all four affine
hypotheses, the two closed immersions and agreement, the one-étale hypothesis,
the canonical graph and section identities, the separated étale fibre, the clopen
section, the exact complement deletion, the canonical residue-field map, and the
two-étale union deletion with both Cartesian squares. No mathematical mismatch
was found. Explicit scheme coercions were the sole elaboration repair; no DAG
statement or dependency record was altered.
