## Worker report

Item: `lem-sfb-finite-centre-proper-pinching`, group N9, 2026-10-24 UTC.
Module: `Sheaf.AlgebraicGeometry.FiniteCentreProperPinching`.
Declaration: `AlgebraicGeometry.exists_finiteCentre_proper_pinching`.
This is one theorem with a `sorry` proof, no new definitions, and no statement correction.
The theorem docstring contains all eight steps of the accepted natural-language proof.
Only the item's `lean` field changes.

Hypothesis and conclusion audit against the node:

- A commutative Noetherian ring is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
  The base is exactly `Spec (CommRingCat.of R)`, with no nontriviality assumption on R.
- `Z X T : Over (Spec (CommRingCat.of R))` supplies the three schemes and their
  structure maps. The morphisms `i : Z ⟶ X` and `j : Z ⟶ T` are morphisms over this
  base, so the requisite structural commutativity is part of the data, not omitted.
- Projectivity is `[IsHProjective X.hom]`, the exact finite projective-space embedding
  convention recorded by `def-kun-projective`, rather than a different projectivity notion.
- Finiteness over S is `[IsFinite Z.hom] [IsFinite T.hom]`.
- The closed immersion is `[IsClosedImmersion i.left]`.
- The finite surjection is `[IsFinite j.left] [Surjective j.left]`.
- Finiteness of the underlying set of Z is `[Finite Z.left]`. This places no closed-point
  condition on Z or its image in X. It also places no positive-cardinality condition.
- Properness of X/S is the first conclusion `IsProper X.hom`.
- An ample invertible sheaf is the existential `∃ (L : X.left.Modules)
  (hL : L.IsInvertible), @Scheme.Modules.IsAmple X.left L hL`. The explicit invertibility
  proof argument supplies precisely the prerequisite of the recorded ampleness predicate.
- The affine neighbourhood is `∃ U : X.left.Opens, IsAffineOpen U ∧
  Set.range i.left ⊆ (U : Set X.left)`. It contains the whole image, not just closed points.
- The pushout scheme and its maps are `∃ (P : Over (Spec (CommRingCat.of R)))
  (a : X ⟶ P) (b : T ⟶ P), ∃ hs : IsPushout i.left j.left a.left b.left, ...`.
  The `IsPushout` is in Scheme, not in affine schemes and not merely in `Over S`;
  hence its universal property tests all schemes in the same scheme universe.
  The Over data additionally supplies the induced structure map and compatible maps over S.
- `IsProper P.hom` states properness. Finite presentation is stated as the three conditions
  in the dependency's comparison clause: `LocallyOfFinitePresentation P.hom ∧
  QuasiCompact P.hom ∧ QuasiSeparated P.hom`. No weaker local-only condition is substituted.
- `IsFinite a.left ∧ Surjective a.left` states both assertions about a.
- `IsClosedImmersion b.left` and `IsPullback i.left j.left a.left b.left` state the
  closed immersion and cartesian square, with the same four maps as the pushout.
- The complement conclusion supplies opens U in X and V in P, a scheme isomorphism
  `e : U.toScheme ≅ V.toScheme`, and identifies their sets as `(Set.range i.left)ᶜ`
  and `(Set.range b.left)ᶜ`. The equation `e.hom ≫ V.ι = U.ι ≫ a.left` ensures this
  is the induced restriction of a, rather than an arbitrary complement isomorphism.
- The structure-sheaf description is the `∀ W : P.left.Opens, IsPullback ...` clause
  in CommRingCat. Its first two arrows are the actual maps induced by a and b from
  sections on W, and its latter two arrows are induced by i and j into the sections on
  c-inverse-image W. The equality `hs.w` identifies the two inverse-image opens for
  `c = i.left ≫ a.left = j.left ≫ b.left`. Since limits of ring sheaves are computed
  on all opens, this is exactly the claimed sheaf fibre product, with its actual maps.
- The simultaneous affine-chart clause supplies `ι : Type u`, opens W, and `iSup W = ⊤`.
  Each W and all three inverse images are affine. The A-to-D map is the actual
  `i.left.app (a.left ⁻¹ᵁ W k)` and is asserted surjective. A, E, D are their section
  rings; their canonical `toSpecΓ` isomorphisms identify the affine schemes with their
  spectra. The chart isomorphism identifies W with `Spec (pullback alpha beta)`.
  `pullback` in CommRingCat is the existing categorical fibre product, canonically
  identified with the coordinatewise ring `{(u,v) | alpha u = beta v}`. This concrete
  realization is Mathlib's `CommRingCat.pullbackCone` (Constructions.lean:450), built
  from `RingHom.eqLocus` in the product ring; `CommRingCat.pullbackConeIsLimit` proves
  its universal property. Thus no replacement ring notion is invented. Both equations
  for `morphismRestrict` identify a and b with the spectra of the two ring projections,
  just as in the existing Ferrand interface.
- The final `∀ V : P.left.Opens, IsPushout ...` uses `Over.pullback V.ι` to express
  the whole inverse-image square and asserts its pushout property in Scheme.
- No flatness, smoothness, fibre-dimension, degree-two, connectedness, or nonemptiness
  hypotheses occur. All universes are explicitly bound; the affine-cover index is in
  the scheme universe, following the published Ferrand theorem.

Dependency declarations and source reading:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with its ideal-finiteness
  docstring and `isNoetherianRing_iff_ideal_fg`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`, including its full finite-coordinate factorization field.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
  The integral clause of the same dependency is `IsIntegralHom` in Morphisms.Integral.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, with `IsSeparated` and
  `UniversallyClosed` from its imported property modules.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple` and its prerequisite
  invertibility argument. Its full definition was read, not inferred from its name.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit` / `IsColimit`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and projections.
  `IsPushout` and `IsPullback` are the corresponding universal-property interfaces in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`; their fields were read.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  the dependency explicitly defines full finite presentation by adding QC and QS.
- Proof-only imports include all recorded project modules:
  `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper.hProjective_properness`
  (declaration namespace `AlgebraicGeometry`),
  `WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible`
  (`AlgebraicGeometry.projective_closedImmersion_ample_invertible`),
  `Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine`
  (`AlgebraicGeometry.Scheme.exists_affineOpen_of_isAmple`), and
  `Sheaf.AlgebraicGeometry.FerrandSchemePushout`
  (`AlgebraicGeometry.exists_ferrand_scheme_pushout`). Their declarations and docstrings
  were opened in full. The mathematical proof-dependency instances and lemmas are provided
  by Finite, Integral, Proper, UniversallyClosed, Separated and Noetherian imports:
  finite implies integral/proper, closed immersions are affine/integral/closed,
  `UniversallyClosed.of_comp_surjective`, locally Noetherian bases turn local finite type
  into local finite presentation, and separated implies quasi-separated.

Sources checked locally: Stacks `more-morphisms.tex` Proposition 0E25, including the
section-sheaf construction, compatible affine charts and restriction argument; Lemmas
0E26 and 0E27; `properties.tex` Lemma 01ZY, which explicitly permits arbitrary finite
sets of points. The current blueprint direct-image proof was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
This node is a prerequisite extracted below the unit, not the unit's own statement.

Edge cases checked before writing:

- Empty Z forces empty T by surjectivity of j; the pushout is X and a is the identity.
  The structure-sheaf fibre product is over the zero ring and the complement is X.
- Empty X forces Z,T,P empty. The empty open is affine (Spec of the zero ring), and
  invertibility/ampleness cause no positive-cardinality obstruction.
- The zero base ring is allowed; its empty spectrum forces all the schemes empty.
- If j is an isomorphism, the pushout is X. If i is an isomorphism, it is T.
  The finite module-generator argument remains valid also when D is zero.
- A finite centre can contain nonclosed points. Neither `Finite Z.left` nor the
  affine-neighbourhood conclusion imposes a closed-point hypothesis.

Searches for an existing statement (using the prescribed msearch.py wrapper):

- leanfinder: `Finite closed pinching of a projective scheme has a proper finitely
  presented pushout and a finite surjective quotient morphism` — 8 hits, on Proj
  properness and finite-morphism stability; none states the requested pinching theorem.
- loogle: `"AlgebraicGeometry", "pushout"` — 12 hits, on gluing, affine spectrum
  pullbacks and flat pushout sections; no proper finite-centre pinching result.
- grep: `Ferrand|pinching|IsPushout` in Mathlib/AlgebraicGeometry — 25 hits on
  existing categorical diagrams, gluing, and tensor products; no matching theorem.
- Direct rg of `Ferrand|ferrand|finiteCentreProperPinching|finite_centre_proper_pinching|
  lem-sfb-finite-centre-proper-pinching` in lean/Sheaf and lean/WeilConjectures found
  the general Ferrand theorem and specialized pinching consumers, not this theorem.
- Direct rg of `Ferrand|pinching|finiteCentre|finite_centre` and grep of this node id
  in lean/WeilConjectures found no matching declaration. The existing general Ferrand
  theorem is reused in the proof plan and its section/chart interfaces are retained.

Validation: prescribed scompile.py compiled the sandbox and library module independently
against the live server build, cleanly (3.4 s and 2.8 s). No warning or error was emitted.
No new nodes, no dependency repairs, and no STATEMENT-DISPUTED fault were necessary.

## Second reading by N9

A second clause-by-clause self-audit was performed with the finished file and the node open;
the independent review is the maintainer's, as specified by the dispatcher brief.
No other agent was started. The audit specifically checked that finite presentation includes
QC and QS; the pushout is in Scheme; the complement isomorphism commutes with a; the sheaf
formula uses all opens; the affine spectra use the actual i/j section maps and projection
maps; and all inverse-image opens use the same commuting square hs.w. The scalar base maps
are carried by Over morphisms, so no compatibility equation is dropped. Every hypothesis and
clause is matched above. No mismatch or statement correction was found.
