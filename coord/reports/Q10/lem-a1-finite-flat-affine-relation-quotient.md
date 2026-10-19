## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient`.
The main statement is `AlgebraicGeometry.finiteFlat_affineRelation_quotient`, with a
`sorry` proof. Its docstring contains all thirteen natural-language proof steps and
their dependency identifiers. No theorem is proved in this stage-2 delivery.
The node changes only in `lean`; no correction or disputed statement is needed.

Hypotheses and conclusions, clause by clause:

- “S a scheme”: `{S : Scheme.{u}}`. No affineness, separation, finiteness or
  Noetherian assumption is placed on S.
- “U = Spec A and R = Spec B affine schemes over S”: `{A B : CommRingCat.{u}}`,
  `a : Spec A ⟶ S`, `b : Spec B ⟶ S`. The objects `Over.mk a` and `Over.mk b`
  retain these particular structure maps. A bundled commutative ring includes
  its actual ring data, with no nonzero-ring assumption.
- “s,t : R → U over S”: `s t : Over.mk b ⟶ Over.mk a`; the commuting triangles
  are part of `Over.Hom`, rather than unmentioned additional hypotheses.
- “finite locally free”: `[s.left.IsFiniteLocallyFree]` and
  `[t.left.IsFiniteLocallyFree]`, using the recorded upstream class.
- “j identifies R(H) with an equivalence relation on U(H), for every S-scheme H”:
  `[Mono (prod.lift s t)]` supplies pointwise injectivity of the pair of maps;
  `hrel` asserts `Equivalence` of the relation
  `∃ r : H ⟶ Over.mk b, r ≫ s = x ∧ r ≫ t = y` on `H ⟶ Over.mk a`,
  for every `H : Over S`. Monicity is exactly the injectivity part of
  “identifies”, and the existential image relation is exactly R(H).
- “C = {a | s♯(a) = t♯(a)}”: `affineRelationInvariants s.left t.left` is
  `(Spec.homEquiv s.left).hom.eqLocus (Spec.homEquiv t.left).hom`.
  This specializes Mathlib's existing subring equalizer, with actual data.
- “M = Spec C” is literally
  `Spec (CommRingCat.of (affineRelationInvariants s.left t.left))`.
- “canonical U → M”: `affineRelationQuotientMap s.left t.left` is `Spec.map`
  of the subtype inclusion of that very invariant subring. It is never an
  arbitrary chosen arrow or an existentially chosen ring.
- “canonical map finite locally free and surjective”: the first two conjuncts
  are its `.IsFiniteLocallyFree` and `Surjective` predicates.
- “R ≅ U ×_M U compatibly with projections”: the existential `e` has source
  `Spec B` and target `pullback q q`, with
  `e.hom ≫ pullback.fst _ _ = s.left` and the corresponding equation for t.
  Thus this is an isomorphism of the original relation, not an unrelated pair.
- “unique S-structure making q an S-morphism”: the conclusion chooses
  `m : M ⟶ S`, `hq : q ≫ m = a`, and proves every `m'` with this equality
  is equal to m. This is uniqueness as a scheme morphism, not only up to iso.
- “represents the fppf sheafification of H ↦ U(H)/R(H)”: the topology is
  `Scheme.fppfTopology.over S`. The presheaf is
  `coequalizer (yoneda.map s) (yoneda.map t)`. Colimits of presheaves are
  objectwise, and with `hrel` this is the quotient by exactly the given
  equivalence relation. `Presheaf.IsSheaf ... (yoneda.obj (Over.mk m))`
  asserts that the proposed representer is a sheaf. The existential unit η
  goes from the quotient presheaf to that representable presheaf, with
  `coequalizer.π ... ≫ η = yoneda.map (Over.homMk q hq)`. Finally, for every
  fppf sheaf G, `Function.Bijective (fun k ↦ η ≫ k)` says that every map from
  the quotient presheaf into G factors uniquely through η. This is precisely
  the sheafification universal property of the recorded definition node.
  It includes the canonical quotient arrow, not just an abstract isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec` and `Spec.map` (scheme and affine-spectrum nodes).
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.homEquiv`, including
  its full signature `(Spec S ⟶ Spec R) ≃ (R ⟶ S)` and inverse `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree`, extending `IsFinite`, `Flat`, and
  `LocallyOfFinitePresentation`. Its degree class is not needed here.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, with scheme pullbacks supplied by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over` supplies `.over S`.
  This is the same over-topology recorded as `Scheme.overGrothendieckTopology`
  in `Mathlib.AlgebraicGeometry.Sites.Small`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: the universal property of
  `presheafToSheaf`, `toSheafify`, and `sheafificationAdjunction`. We state that
  property directly, rather than assume `HasWeakSheafify` for every small-valued
  presheaf on a big site. This follows the already published statement pattern
  in `EtaleRelationRestrictionQuotient` and `EtaleAffineQuotientRepresentable`.
- `Mathlib.Algebra.Ring.Subring.Basic`: `RingHom.eqLocus`, whose carrier is
  exactly equality of the two homomorphisms. The canonical map uses
  `Subring.subtype` from `Mathlib.Algebra.Ring.Subring.Defs`.

The module imports every stated proof dependency by its recorded module or
Mathlib-match file (ordinary `import` for proof-only dependencies). The four
new groupoid/basis proof prerequisites have no recorded declaration yet and
therefore have no module to import. No dependency record needed repair.
The two helper definitions merely specialize existing constructions belonging
to this theorem; they add no independent mathematical notion or new DAG node.

Edge cases checked before writing:

- A is the zero ring: Spec A is empty, the coordinate maps force B to be zero,
  and the actual invariant subring is zero. Thus M and the relation are empty,
  with the unique map M → S. On the empty test scheme the represented presheaf
  is a singleton, as the quotient presheaf must be. No `Nontrivial` assumption
  or positivity-of-rank assumption excludes this case.
- The identity relation s = t = id has C = A, q an isomorphism, and the
  coequalizer quotient is the representable itself.
- For the full relation on a finite faithfully flat affine cover of a field,
  the statement recovers the field spectrum and its actual kernel pair.
- No common fixed rank is assumed: varying finite locally free ranks are
  allowed. S may be non-affine and non-separated. The quantifier over H ranges
  over all objects of `Over S` in the same scheme universe; there is no lower,
  independent test universe that could make the relation hypothesis vacuous.

Searches for an existing statement or construction:

- `msearch.py grep` query `finite.flat.*quotient|quotient.*finite.flat|equivalence.relation.*affine`: 0 hits; no matches in Mathlib AlgebraicGeometry.
- `msearch.py loogle` query `"Scheme", "quotient"`: 3 hits; the three hits concern a quotient-ring ideal factorization, not a relation quotient.
- `msearch.py leanfinder` query `A finite locally free equivalence relation on affine schemes has quotient the spectrum of the invariant subring`: 8 hits; the hits concern affine space, affine schemes and finite morphisms; none states this quotient theorem.
- Direct `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for
  `finite.flat.*quotient|quotient.*finite.flat|affine.*[Rr]elation|[Rr]elation.*[Qq]uotient`:
  related étale-relation statements and unrelated module quotients, no finite
  locally free affine invariant-spectrum quotient theorem. Read the full
  `EtaleRelationRestrictionQuotient` and `EtaleAffineQuotientRepresentable`
  signatures: neither is this statement.
- `grep -rn` for the item identifier in upstream `WeilConjectures`: no match.
- Direct `rg` for all three proposed declaration names in Mathlib, upstream,
  side `lean/Sheaf` and `dag/lean_names_upstream.json`: no existing name.
- Read `RingHom.eqLocus`, `Subring.subtype` and `Spec.homEquiv` rather than
  inventing another equalizer ring or another scheme-coordinate convention.

Validation: `scompile.py Q10 lem-a1-finite-flat-affine-relation-quotient` on the
single delivered module, preserving its standard time limit. The first pass
identified the required `noncomputable` modifiers on the helper constructions;
the second identified one long line, now split. Final compile passed cleanly in sandbox form and under its module path (2.2 s
and 2.1 s respectively), with no errors or warnings. The node diff was checked:
only `lean` changes; the module contains two real definitions and exactly one
named theorem with `sorry`. All lines meet the 100-character limit.

Dry run: `deliver2.py Q10 lem-a1-finite-flat-affine-relation-quotient --no-push`
printed OK: the delivery passes the server preflight and per-file compilation.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
