## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGroupoidGenericAffineFlatThickening` states
`AlgebraicGeometry.groupoid_exists_generic_affine_flat_thickening`, with one postponed
theorem and no new definitions. The node is unchanged except for `lean`.

Source read: Stacks Project, `more-groupoids.tex`, Tag 0ABC,
`lemma-invariant-affine-open-around-generic-point`, both statement and proof. Its five
numbered conclusions agree with the node, whose invariance clauses make explicit the
meaning of the source's “R-invariant subschemes”. The absolute groupoid is exactly the
node's setting, with no field or Noetherian hypothesis.

Hypothesis and conclusion correspondence:

- `U R : Scheme.{u}`, maps `s t e i c`, and `hG : IsGroupoidScheme s t e i c`
  are the supplied groupoid. The recorded definition is used without replacement.
- `[IsFinite s] [IsFinite t]` are finiteness of source and target.
  `[LocallyOfFinitePresentation s] [LocallyOfFinitePresentation t]` complete their
  finite-presentation hypotheses: finite morphisms are already quasi-compact and
  quasi-separated, as required by the convention node. There is no flatness assumption.
- `[QuasiSeparatedSpace U]` is quasi-separatedness of the object scheme, equivalent
  to `QuasiSeparated (terminal.from U)` by
  `quasiSeparatedSpace_iff_quasiSeparated` in the recorded Mathlib module.
- `(m : ℕ) (p : Fin m → U)` is the list of selected points, including the empty list.
  `hgeneric` quantifies over every point of `t '' (s ⁻¹' {p j})`, exactly the stated
  orbit. Its conclusion `∃ Z ∈ irreducibleComponents U, IsGenericPoint x Z` says each
  point is the generic point of a component, not merely that the selected point is.
- The existential `V : U.Opens` supplies the open subscheme, with canonical open
  immersion `V.ι`. `hV : s ⁻¹ᵁ V = t ⁻¹ᵁ V` is its invariance as an open subscheme.
- `J : V.toScheme.IdealSheafData` supplies the closed subscheme `V' = J.subscheme`,
  with canonical closed immersion `J.subschemeι`. The closed immersion condition is
  inherent in this Mathlib construction (instance in Morphisms.ClosedImmersion).
  Every closed subscheme is represented by its kernel ideal, so this encoding
  excludes no closed subscheme structure.
- `IsAffine V.toScheme ∧ IsAffine J.subscheme` gives both affineness conclusions.
  `∀ j, p j ∈ Set.range (J.subschemeι ≫ V.ι)` gives exactly containment in `|V'|`.
- `LocallyOfFinitePresentation J.subschemeι ∧ QuasiCompact J.subschemeι ∧
  QuasiSeparated J.subschemeι` gives finite presentation, and
  `IsHomeomorph J.subschemeι` gives the homeomorphism of underlying spaces.
  Together with the inherent closed immersion, these are precisely the requested
  finitely presented thickening; no reducedness or square-zero condition is imposed.
- `J.comap (s ∣_ V) = J.comap (t.resLE V (s ⁻¹ᵁ V) (le_of_eq hV))` compares the
  pulled-back ideal sheaves on the SAME scheme `(s ⁻¹ᵁ V).toScheme = R_V`.
  The second map is the canonical target restricted using the equality `hV`.
  Mathlib `comapIso` identifies these ideals' subschemes with their respective
  fibre products. Thus this asserts scheme-theoretic invariance, including nilpotents.
- Write `j = J.subschemeι ≫ V.ι` for explanation only (there is no `let` in the
  signature). The actual restricted arrows are
  `pullback (pullback.snd j s ≫ t) j`, namely `(V' ×[U,s] R) ×[t,U] V'`.
  Their source is `pullback.fst _ j ≫ pullback.fst j s`, their target is
  `pullback.snd _ j`. The final two conjuncts assert `.IsFiniteLocallyFree` for
  these exact projections, using the recorded upstream class, not arbitrary maps
  or only the single pullback. The induced groupoid operations are inherited;
  the node asks no additional choice of operations in the conclusion.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (the convention's finite-presentation
  composite is rendered as above).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, `quasiSeparatedSpace_iff_quasiSeparated`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`; `Mathlib.Topology.Irreducible`:
  `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  through the canonical `Scheme.Opens.ι` and open restrictions.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, with the canonical ideal subscheme inclusion.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, underlying the affine
  definition; `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (finite, flat, locally of finite
  presentation; full class docstring and signature read).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `Scheme.IdealSheafData.comap`, `comapIso`; its Subscheme dependency gives
  `subscheme`, `subschemeι`, `range_subschemeι`. This is the same representation
  used by the recorded rank-filtration proof dependency, not a new notion.

All already stated proof dependencies are imported privately: the rank filtration,
DescentNormLocusAffine, IsAffineOfFiniteClosedCover, the upstream generic-point affine
neighbourhood result in `WeilConjectures.Mathlib.AlgebraicGeometry.Properties`, and
QuasiCompactOpenIntersection. Mathlib leaf proof dependencies are supplied by Proper,
QuasiFinite, Ideal.Operations, Spectrum.Prime.Topology and the public morphism modules.
The three proof prerequisites with no statement yet (generic-point-fp-closed-interior,
groupoid-subset-saturation-invariant, closed-immersion-finite-presentation-ideal) are
named with their exact roles in the nine-step proof docstring; no substitute theorem
is introduced and they are not needed to type this statement.

Edge cases checked mathematically before writing:

- `m = 0`: take `V` empty and the zero ideal there, so `V'` is empty; the canonical
  projections of the empty double restriction are finite locally free.
- Empty `U`: the empty-list case remains available; a nonempty list cannot be formed.
- Repeated selected points and different orbit sizes are allowed; no distinctness or
  common-rank hypothesis appears.
- Nonreduced schemes are allowed: ideal equality retains the full closed subscheme
  structures; the thickening need not be the reduction or have square-zero ideal.
- No quasi-compactness or Noetherian hypothesis on `U` was added. Schemes and all
  fibre products share the explicitly bound universe `u`; there is no independent
  smaller test-object universe. All variables are explicit binders.

Searches run (no exact existing statement found):

- `msearch.py leanfinder`: “A finite finitely presented groupoid scheme has an invariant
  affine open around finitely many generic orbits and a finitely presented thickening
  with finite locally free arrows”. Eight hits, including finite-presentation and finite
  affine morphism interfaces, none stating the result.
- `msearch.py loogle`: `IsGroupoidScheme, IsAffineOpen, IsFiniteLocallyFree`.
  Zero hits; the remote Mathlib index does not know `IsGroupoidScheme`.
- `msearch.py grep`: `groupoid.*(affine|thickening)|invariant.*generic`, in
  `AlgebraicGeometry`. Zero hits.
- `msearch.py leansearch`: “A finite groupoid of finite presentation has an invariant
  affine neighbourhood of finitely many generic orbits with a finite locally free
  thickening”. Eight hits about finite presentation and abstract groupoids, no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for finite groupoids, groupoid affine
  results, generic thickenings, and the exact node id. Existing affine groupoid results
  concern flat groupoids or different conclusions; the rank-filtration module was the
  relevant existing interface. No declaration for this statement was found.
- Exact proposed theorem name and node id searched in `dag/lean_names_upstream.json`
  and both source trees: no collision or pre-existing theorem.

Validation: prescribed `scompile.py` compiled both sandbox and library module modes
cleanly (4.5 seconds and 3.3 seconds); no errors or warnings. Every theorem proof is
`sorry` as required for stage 2. No new nodes, dependency repairs, or statement
correction were needed.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
