## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFlatAffineCharts` states
`AlgebraicGeometry.exists_relative_flat_affine_charts`, with its sole proof `sorry`.
The item node is changed only in `lean`. No definition, dependency repair, new node,
or statement correction is needed.

Sources read: `more-morphisms.tex`, Tag 05VJ,
`lemma-base-change-criterion-flatness-fibre`, especially the first two proof sentences;
`morphisms.tex`, Tag 02FV, `lemma-finite-presentation-permanence` (1);
`algebra.tex`, Tag 00RC, `theorem-openness-flatness`.
The node deliberately extracts the chart/openness assertion: the later arbitrary
parameter-base-change assertion of 05VJ needs base-flatness, whereas this item does not.
The module docstring carries all five steps of the node's proof.

Clause correspondence:

- Schemes S,X,Y are `{S X Y : Scheme.{u}}`, with explicit universe `u` and
  `set_option autoImplicit false`. The maps are `(p : X ⟶ S)`, `(q : Y ⟶ S)`,
  and `(f : X ⟶ Y)`. The commuting triangle is `(hf : f ≫ q = p)`.
- Local finite presentation of p is `[LocallyOfFinitePresentation p]`;
  local finite type of q is `[LocallyOfFiniteType q]`. There is no `Flat p` binder,
  nor any Noetherian, separated, quasi-compact, or globally finite-type hypothesis.
- For every x: `(x : X)` is an arbitrary argument. The existential `W`, `V`, `Z`
  are opens of S,Y,X, with `_hW`, `hV`, `hZ : IsAffineOpen ...`.
  `_hxW`, `_hxV`, `_hxZ` assert membership of p(x), f(x), x respectively.
  `hVW : V ≤ q ⁻¹ᵁ W`, `hZW : Z ≤ p ⁻¹ᵁ W`, and
  `hZV : Z ≤ f ⁻¹ᵁ V` assert exactly the three image containments.
  Separate hZW and hZV express containment in the stated intersection without
  assuming that intersection is affine.
- A,B,C are the canonical coordinate rings Γ(S,W), Γ(Y,V), Γ(X,Z).
  Mathlib's `IsAffineOpen` identifies each open scheme with the spectrum of its
  section ring. Thus naming the rings by these expressions loses no choice of
  chart and requires no additional independent ring objects or arbitrary maps.
- The induced A→B and B→C maps are `q.appLE W V hVW` and `f.appLE V Z hZV`.
  Their composite equals `p.appLE W Z hZW`, explicitly the first conjunction.
  Their finite-type/finite-presentation properties are the next three conjuncts:
  `(q.appLE ...).hom.FiniteType`, `(p.appLE ...).hom.FinitePresentation`, and
  `(f.appLE ...).hom.FinitePresentation`. `RingHom.FinitePresentation` unfolds
  literally to the recorded `Algebra.FinitePresentation` using the map's algebra
  structure; this uses the dependency notion, rather than introducing a copy.
- For every `z : Z`, `hZ.primeIdealOf z` is r. Its `comap` along the B→C map
  is b. The first pointwise clause says b is exactly `hV.primeIdealOf` of f(z).
  In particular the formula works for every prime, not only closed points.
- `eC` identifies the X-stalk with `Localization.AtPrime r.asIdeal`, and `eB`
  identifies the Y-stalk with `Localization.AtPrime b.asIdeal`. Their next two
  clauses send every germ of a coordinate-ring element to its image under the
  localization algebra map. This normalization specifies canonical equivalences:
  any ring map out of a localization is uniquely fixed by the original ring.
  They are not arbitrary unnormalized isomorphisms.
- The next clause, for every element b of the localized B-ring, states
  `eC (f.stalkMap z (eB.symm b)) = Localization.localRingHom ... rfl b`.
  This is the entire localized stalk-map formula. `rfl` witnesses only the
  definitional fact that the chosen source prime is the inverse-image ideal;
  it is not a postponed proof or an additional mathematical assertion.
- E is written explicitly as the set of `r : PrimeSpectrum Γ(X,Z)` where
  `((algebraMap Γ(X,Z) (Localization.AtPrime r.asIdeal)).comp
  (f.appLE V Z hZV).hom).Flat`. By the recorded `RingHom.Flat` definition,
  this is exactly that C_r is flat as a B-module for the chart-induced action.
  The next conjunct is `IsOpen` of this exact set, in the Zariski topology.
- The final `∀ z : Z, ... ↔ (f.stalkMap z).hom.Flat` identifies membership of
  the chart prime in E with flatness of f at z, exactly the dependency's
  stalkwise definition. No global flatness assumption replaces pointwise flatness.

Dependency declarations read and used (statement dependencies):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; the affine-open/spectrum coordinate dictionary comes from
  `Mathlib.AlgebraicGeometry.AffineScheme`, `IsAffineOpen`, `primeIdealOf`,
  `isoSpec`, and `fromSpec_primeIdealOf`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (no quasi-compactness is required).
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`,
  accessed through its exact bare-ring-map form `RingHom.FinitePresentation`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  and `Localization.localRingHom` (the existing canonical map, no new helper).
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, definitionally module flatness.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`,
  `Flat.iff_flat_stalkMap`; at a point use `(f.stalkMap z).hom.Flat`.

All stated proof dependencies are imported: the affine basis, affine-pair
finite-type and finite-presentation fields, affine stalk localization, and the
locally-ringed-space morphism live in the listed Mathlib modules. Cancellation is
`AlgebraicGeometry.locallyOfFinitePresentation_of_comp` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
Openness is `Module.isOpen_setOf_flat_localizedModule` in
`WeilConjectures.RingTheory.OpenFlatLocus`. Flatness over a localized base is
`Module.flat_iff_of_isLocalization` in `Mathlib.RingTheory.Flat.Localization`.
The Mathlib `IsAffineOpen.arrowStalkMapIso` and `comap_primeIdealOf_appLE` were
also read: they supply the canonical maps underlying the explicit pointwise
clause, without themselves asserting this item's chart/openness package.
Proof-only imports are plain `import`; statement imports are `public import`.

Edge cases checked before writing and again against the signature:

- Empty X: there is no x argument to discharge; no nonempty hypothesis is inserted.
- Identity maps: all chart localizations are flat over the chart base and E is all
  of Spec C, which is open. The canonical stalk formula reduces to the identity.
- Nonflat source over the base: take S=Y=Spec Z, X=Spec F₂, q=id and f=p the
  closed immersion. The finite-presentation hypotheses hold, and E is empty
  because the nonzero stalk F₂ is not Z-flat. The result permits this case.
- Nonmaximal primes: all pointwise binders run over Z or the full prime spectrum;
  there is no restriction to closed points or residue-field flatness.
- Zero coordinate rings give empty affine opens/spectra; an open containing x
  cannot be empty, and no assertion assumes that an empty intersection is affine.
- Arbitrary universe u covers schemes of every size allowed by the project;
  there is no independent universe for a family of test algebras that could
  make a hypothesis vacuous.

Searches actually run with `msearch.py NP lem-sfb-relative-flat-affine-charts`:

- `leanfinder`: "Compatible affine neighborhoods for a morphism over a base with
  source locally finitely presented and target locally finite type identify the
  stalk flat locus with the open locus of flat prime localizations". Eight hits:
  `Flat.iff_flat_stalkMap`, `Flat.stalkMap`, `flat_iff`, `Flat.of_stalkMap`,
  `Scheme.Hom.flat_appLE`, and `UniversallyOpen.of_flat` among them. These give
  flatness characterizations or assume global flatness; none gives this package.
- `loogle`: "AlgebraicGeometry.LocallyOfFinitePresentation,
  AlgebraicGeometry.LocallyOfFiniteType". Three hits: finite presentation implies
  finite type and two locally Noetherian results; none matches this statement.
- `leansearch`: "Compatible affine charts and openness of the pointwise flat
  locus of a locally finitely presented morphism". Eight hits on `Flat` affine
  fields, `LocallyOfFinitePresentation.mk`, and a smoothness instance; no match.
- Mathlib grep via msearch: `flatLocus|flat_locus|isOpen.*flat|relative_flat_affine`
  in `AlgebraicGeometry`. Seven hits on universally open maps, flat monomorphisms,
  and descent; no combined statement or replacement for the pointwise open locus.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `relative_flat_affine|flatLocus|flat_locus|lem-sfb-relative-flat-affine-charts`
  finds the distinct `RelativeFlatLocusBaseChange.isOpen_flatLocus_and_baseChange`.
  It requires base-flatness and asserts arbitrary parameter base change; it
  cannot supply this item's assertion without the forbidden stronger hypothesis.
- `grep -rn` for this node id in `lean/WeilConjectures` returned no declaration.
  `rg` of `dag/lean_names_upstream.json` for the proposed declaration,
  `relative_flat_affine|flatLocus|flat_locus` returned no match.

Validation: the prescribed `scompile.py` checked both sandbox and actual library
module names cleanly (1.9 s and 2.1 s); no errors or additional warnings. The module
has one theorem and one `sorry`, no helper definitions or diagnostic commands;
all lines are at most 90 characters. No statement dispute or node fault found.

## Second reading by NP

This is the author's second reading, performed without starting another agent,
as the dispatcher's explicit instruction requires. The maintainer performs the
independent review after delivery.

Reopened the node and the finished Lean file and compared the binders and every
conjunct. The node's S-morphism condition is precisely hf; p has local finite
presentation and q local finite type. The witnesses require affine W,V,Z and all
three memberships and containments. The three finite-algebra conditions are in
order A→B, A→C, B→C, with the displayed equality enforcing the same A→C map.
The prime of f(z) is explicitly identified with comap, rather than assumed.
Both stalk isomorphisms are normalized on all sections, so the map compatibility
cannot be satisfied by choosing unrelated ring isomorphisms. The canonical
`Localization.localRingHom` formula covers all fractions. Finally, the `IsOpen`
conjunct uses B-flatness of C_r, while the last iff uses flatness over the Y-stalk;
these are the two different notions whose equivalence is the node's last clause.
There is no Flat p hypothesis. The source's base-flatness requirement belongs to
the later parameter-base-change assertion, not these first two proof sentences.
No mismatch was found and no correction was made. The existing proof interfaces
in Mathlib agree with the chosen directions of eC and eB (stalk to localization).
