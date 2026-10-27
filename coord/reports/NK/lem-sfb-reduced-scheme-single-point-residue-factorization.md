## Worker report

The module `Sheaf.AlgebraicGeometry.ReducedSchemeSinglePointResidueFactorization`
states `AlgebraicGeometry.exists_factor_through_residueField_of_isReduced_of_range_subset_singleton`.
Its sole proof is `sorry`. It introduces no definitions or additional nodes and makes
no statement correction. The theorem docstring gives all six proof steps of the DAG,
including the zero-ring case and gluing over potentially infinite covers.

The source was read in `literature/stacks-project/morphisms.tex`,
`lemma-factor-through-point`, Tag 0H1M (lines 15600–15617). Its hypotheses and
conclusion agree with the node; the source's affine-ring hint does not require a
finite cover of the source.

Hypothesis and clause correspondence:

- Schemes `Y` and `X`: `{Y X : Scheme.{u}}`, with the universe `u` explicitly declared.
- Reducedness of `Y`: `[IsReduced Y]`. Mathlib's sectionwise definition is the
  node's equivalent definition, and its stalk instance supplies the local-ring form.
- The specified morphism: `(f : Y ⟶ X)`.
- The specified point: `(x : X)`.
- Set-theoretic containment `f(|Y|) ⊆ {x}`: `(himage : Set.range f ⊆ {x})`.
  The coercion of `f` is its underlying point map.
- The residue field is exactly `X.residueField x`, the quotient of the stalk by
  its maximal ideal, rather than a chosen extension field.
- The spectrum is exactly `Spec (X.residueField x)`.
- The canonical residue morphism `i_x` is exactly `X.fromSpecResidueField x`,
  defined as `Spec.map (X.residue x) ≫ X.fromSpecStalk x`.
- Existence of the requested morphism is `∃ h : Y ⟶ Spec (X.residueField x), ...`.
- The equation `i_x ∘ h = f` is `h ≫ X.fromSpecResidueField x = f`.
  Category composition runs from left to right.
- Empty, non-quasi-compact, and non-Noetherian sources are permitted: there is
  no nonemptiness, compactness, separatedness, affineness, finiteness, or
  Noetherian binder. Only existence is stated, with no added uniqueness clause.

Statement dependencies were read from their node records and source declarations:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
- `lem-weil-pbc-morphism-from-spec-field`: its Mathlib match is the usable record,
  not a missing Lean interface. In `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.SpecToEquivOfField`,
  `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`, and
  `Scheme.fromSpecResidueField_apply` identify the canonical residue-point map
  and field-source factorization. The statement uses `Scheme.fromSpecResidueField`
  directly; it does not impose a field structure on `Y`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.

The modules of proof dependencies are plain imports, including the recorded
`WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField` (read in full).
The affine point and stalk lemmas are in `Mathlib.AlgebraicGeometry.AffineScheme`
and `OpenImmersion`; affine quasi-separatedness is in `Morphisms.QuasiSeparated`.
The prime-residue algebra is in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`;
vanishing-to-nilpotence in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`;
gluing in `Mathlib.AlgebraicGeometry.Gluing`; basic-open criteria in
`Mathlib.RingTheory.Spectrum.Prime.Topology` and `Mathlib.RingTheory.Ideal.Span`.
The recorded locally-ringed-space and localization interfaces are imported too.
No dependency interface needed repair.

Edge cases checked before drafting: if `Y` is empty, the containment is vacuous
and its unique morphism to the residue spectrum gives the asserted equation.
If an affine chart has zero coordinate ring, all its elements are units and its
spectrum is empty, as required in proof step 3. Infinite disjoint unions and
non-quasi-separated schemes are permitted: intersections are covered by affine
opens rather than assumed affine or quasi-compact. The point `x` need not be
closed. No perfection or characteristic restriction is made. An empty target
has no point `x`, consistently with the source. Reducedness is essential:
the identity on the spectrum of dual numbers has one-point image but does not
factor through its reduced residue point.

Searches for an existing statement:

- `msearch.py leanfinder`: “A morphism from a reduced scheme whose image is
  contained in one point factors through the residue field of that point”. Eight
  hits give canonical residue-point maps and field-source factorization, not the
  general reduced-source assertion.
- `msearch.py leansearch`: “A morphism from a reduced scheme with image contained
  in a singleton factors through the residue field at that point”. Eight hits,
  including `Scheme.SpecToEquivOfField` and `Scheme.fromSpecResidueField`;
  no matching theorem for arbitrary reduced sources.
- `msearch.py loogle`: `AlgebraicGeometry.IsReduced, AlgebraicGeometry.Scheme.residueField`.
  One hit, `AlgebraicGeometry.ext_of_fromSpecResidueField_eq`, an equality criterion
  rather than this factorization theorem.
- `msearch.py grep`: `factor.*[Rr]esidue|[Rr]esidue.*factor|range.*singleton`,
  restricted to Mathlib `AlgebraicGeometry`. Two hits in `ValuativeCriterion.lean`
  and `AlgClosed/Basic.lean`, neither a match.
- Direct `rg` of Mathlib `AlgebraicGeometry` with
  `exists.*[Rr]esidue|factor.*[Rr]esidue|[Rr]educed.*[Ss]ingleton|[Ss]ingleton.*[Rr]educed`
  found valuation-ring factorization and subsingleton reduced schemes, not this result.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` with
  `factor.*[Rr]esidue|[Rr]esidue.*factor|reduced.*single|single.*reduced` found the
  downstream algebraic-space statement `ReducedSingletonFieldFactorization.lean`
  and other specializations, but no duplicate. The downstream theorem was read:
  it concerns a quasi-compact field monomorphism into an algebraic space and cites
  this scheme theorem in its proof. It is not the present assertion.
- The exact blueprint-id search in `lean/WeilConjectures` returned no declaration.

No `STATEMENT-DISPUTED` issue was found.

## Second reading by NK

Reread the node, source, dependency signatures, and final module. The source object
is arbitrary reduced `Y`, not `Spec` of a field; the target point is supplied before
the containment hypothesis; containment rather than equality of ranges preserves
the empty case. The factorization uses the precise canonical residue-field map,
with the correct composition order. The conclusion adds neither uniqueness nor
an isomorphism. All variables and universes are explicit, and the theorem has no
hidden local notation, instances, choices, or additional assumptions. No mismatch
was found and no correction was made. This is the worker's own rereading; the
maintainer's independent review remains part of the prescribed delivery process.
