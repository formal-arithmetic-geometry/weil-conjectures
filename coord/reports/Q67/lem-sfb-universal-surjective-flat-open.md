## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalSurjectiveFlatOpen` states
`AlgebraicGeometry.exists_universalSurjectiveFlatOpen`, with its sole proof `sorry`.
It states the scheme specialization of Stacks Tag 05XC exactly. I read the source
in `literature/stacks-project/spaces-more-morphisms.tex`, lines 11728–11789, together
with the preceding Tag 05XB and the node's seven proof steps. No statement correction,
new definition, dependency repair, or mathematical dispute is needed. The module's
docstring records all seven proof steps and their DAG prerequisites.

Hypothesis and clause correspondence:

- The schemes B, A and C are the explicitly universe-bound `{B A C : Scheme.{u}}`.
- The morphisms p, q and f are `(p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)`.
- The relation q ∘ f = p is `(hf : f ≫ q = p)` in Lean composition order.
- Flatness of p is `[Flat p]`, using the recorded flat-morphism declaration. Its
  stalkwise equivalence is `Flat.iff_flat_stalkMap`.
- Local finite presentation of p is `[LocallyOfFinitePresentation p]`.
- Closedness of the underlying map of p is `(hp : IsClosedMap p)`. This is ordinary
  closedness, as in the source; no universal closedness assumption is imposed.
- Local finite type of q is `[LocallyOfFiniteType q]`.
- Closedness of the underlying map of q is `(hq : IsClosedMap q)`.
- The existential open subscheme is `∃ V : B.Opens`, with scheme `V.toScheme`
  and its canonical open immersion `V.ι`.
- Every scheme T and map h are `∀ (T : Scheme.{u}) (h : T ⟶ B)`. No finiteness,
  reducedness, nonemptiness or other property of T is assumed. The arbitrary
  universe u follows the library's scheme and pullback universe convention.
- The base-changed arrow A ×_B T → C ×_B T is the canonical
  `pullback.map p h q h f (𝟙 T) (𝟙 B)`; its first compatibility proof is obtained
  from `hf.symm` by the identity law and its second by identity laws. Thus the
  arrow is fixed by the pullback universal property, rather than an arbitrary map.
- Surjectivity and flatness are the conjunction `Surjective (...) ∧ Flat (...)`.
  The two occurrences are the same canonical map; their equality proofs carry no
  additional hypothesis.
- “If and only if” is the displayed `↔`, with factorization expressed as
  `∃ l : T ⟶ V.toScheme, l ≫ V.ι = h`. There is no uniqueness or extra conclusion
  added to the node's statement.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme` (available through the public geometry imports).
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `def-weil-open-immersion`: Mathlib's canonical open subscheme `V.toScheme` and
  inclusion `V.ι`, in the scheme/open-immersion API, using the notion
  `AlgebraicGeometry.IsOpenImmersion` of `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.map`, in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. Scheme pullback
  existence comes from the public `Mathlib.AlgebraicGeometry.Pullbacks` import.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`, in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.

The stated Mathlib proof prerequisites are plain imports: `PullbackCarrier` gives
`Scheme.image_preimage_eq_of_isPullback` (lem-weil-pbc-base-change-image),
`Morphisms.UniversallyOpen` gives `UniversallyOpen.of_flat`
(lem-weil-pbc-flat-lfp-open), and `RingTheory.FinitePresentation` gives
`Algebra.FinitePresentation.of_restrict_scalars_finitePresentation`
(lem-weil-pbc-finite-presentation-over-finite-type-algebra).
The proof-only node `lem-sfb-relative-flat-locus-base-change` has no Lean record or
Mathlib match in the read checkout, so there is no module to import yet; its future
proof import can be added when that node is stated. It is not a statement dependency
and is not needed to type this theorem.

Edge cases checked before writing:

- Empty T: both surjectivity and flatness hold for the empty-to-empty base-changed
  map, and the unique map to the open gives factorization. No nonemptiness binder
  excludes this case.
- Empty B: A and C are empty and the unique open represents the property.
- Empty A with nonempty C: flatness of the empty map is vacuous; the representing
  open consists of the base points with empty target fibre. Closedness of q makes
  the complement of q(C) open, as required by the proof.
- Empty C forces A empty via f; V can be the whole base.
- For f an isomorphism, every base change is surjective and flat, so V is the whole
  base. The statement does not require surjectivity of p or q.
- Nonreduced test schemes and bases are retained: all objects are arbitrary schemes
  and no pointwise-only or field-only test replaces the universal quantification.

Searches for an existing declaration (all performed on 2026-10-22):

- `msearch.py leanfinder`: “For a map between scheme families with flat locally
  finitely presented closed source and locally finite type closed target, the base
  changes making the map surjective and flat are represented by an open subscheme
  of the base”. Eight hits: flat descent, `UniversallyOpen.of_flat`, etc.; none is
  a theorem constructing this universal parameter open.
- `msearch.py loogle`: `"AlgebraicGeometry", "Flat", "Surjective"`. Twelve hits:
  flat-surjective epimorphisms, affine faithfully flat criteria, faithful pullback,
  and descent properties; no match to Tag 05XC.
- `msearch.py leansearch`: “The base changes making a morphism of scheme families
  surjective and flat are represented by an open subscheme of the parameter base”.
  Eight hits: faithfully flat criteria and stability under base change, no
  representing-open theorem.
- `msearch.py grep` in Mathlib/AlgebraicGeometry:
  `where.*surjective|surjective.*flat.*locus|flat.*surjective.*locus`. Three incidental
  hits in Group/Affine, Morphisms/AffineAnd and Morphisms/FlatRank; no exact statement.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  `universalSurjective|universal_surjective|exists_universalSurjectiveFlatOpen|surjective.*flat.*locus|flat.*surjective.*locus`.
  No existing declaration. A separate search for the item id in upstream found no
  occurrence. The project occurrence in `UniversalIsomorphismOpen.lean` is a proof
  docstring citing this node, not its statement. A final exact-name search across
  Mathlib and both project roots also found no collision.

Validation: `scompile.py Q67 lem-sfb-universal-surjective-flat-open` compiled the
module in module mode against the live published library, with no errors or
warnings. The item node copy changes only `lean`; the existing stage-1 reviewed
split is preserved unchanged. The previous worker's stale-stage-1-dispatch refusal
does not call for resplitting or altering that reviewed proof.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
