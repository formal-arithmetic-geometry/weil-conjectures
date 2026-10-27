## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteImageNowhereDense` states
`AlgebraicGeometry.Scheme.Hom.isClosed_isNowhereDense_image_of_isFinite`.
Its proof is exactly `sorry`; no definitions or additional theorems are introduced.
The node is unchanged except for its `lean` record.

Source checked in full: Stacks Project, `morphisms.tex`, Tag 03HX,
`lemma-image-nowhere-dense-finite`, statement and proof. The statement has precisely
this node's assumptions and both conclusions. The declaration docstring carries
all six proof steps and names their DAG dependencies.

Hypothesis and clause correspondence:

- Schemes `Y` and `X`: `{X Y : Scheme.{u}}`, with `universe u` explicitly declared.
- A morphism `f : Y → X`: `(f : Y ⟶ X)` in the category of schemes.
- Finiteness of `f`: `[IsFinite f]`, the dependency's existing Mathlib definition.
- A subset of the underlying space of `Y`: `(T : Set Y)` using the canonical scheme carrier.
- Closedness of `T`: `(hT : IsClosed T)`.
- Nowhere density of `T`: `(hnow : IsNowhereDense T)`. Mathlib defines this as
  `interior (closure T) = ∅`, literally the node's explanation.
- The image `f(T)` is the ordinary underlying-point image `f '' T`.
- Closedness of that image: the first conjunct `IsClosed (f '' T)`.
- Nowhere density of that image: the second conjunct `IsNowhereDense (f '' T)`.
- There is no surjectivity, reducedness, integrality, Noetherianity or flatness
  assumption. The common scheme universe is the category's usual universe and is
  arbitrary; `set_option autoImplicit false` is unnecessary because every variable
  and universe in the declaration is explicitly bound.

Statement dependency declarations read, including their docstrings and signatures:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`
  in `Mathlib.AlgebraicGeometry.Scheme`, both imported publicly.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, imported publicly. Its affine-open
  finite-module condition is the node's finite-morphism condition. The sibling
  `AlgebraicGeometry.IsIntegralHom` in `Mathlib.AlgebraicGeometry.Morphisms.Integral`
  was also read; the present statement uses only the finite clause.
- `IsNowhereDense` in `Mathlib.Topology.GDelta.Basic` is imported publicly and reused.

Imports for already stated proof dependencies:

- `lem-weil-pbc-finite-closed-map-finite-fibres`: Mathlib
  `Morphisms.Proper` (finite morphisms are proper), `Morphisms.UniversallyClosed`
  (`Scheme.Hom.isClosedMap`) and `Morphisms.QuasiFinite`
  (`Scheme.Hom.finite_preimage_singleton`).
- `lem-weil-pbc-finite-morphism-permanence`: Mathlib `Morphisms.Finite`
  (base-change stability), `Morphisms.Affine` (`isAffine_of_isAffineHom`) and
  `Morphisms.Proper` (proper composition).
- `lem-weil-pbc-finite-affine-section-cover`:
  `AlgebraicGeometry.exists_finite_affine_section_cover` in
  `Sheaf.AlgebraicGeometry.FiniteAffineSectionCover`; the full signature and
  docstring were read.
- `def-pc-finite-locally-free`: `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`
  in `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.
- `lem-weil-pbc-flat-lfp-open`: `AlgebraicGeometry.UniversallyOpen.of_flat`
  in `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `lem-weil-pbc-base-change-image`:
  `AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback` in
  `Mathlib.AlgebraicGeometry.PullbackCarrier`.

`lem-sfb-nowhere-dense-section-cover-image` has neither a Lean record nor a
Mathlib match in the current DAG. It supplies a proof step, rather than an object
needed to type the present statement; there is consequently no module to import
for it yet. Its future import is left to the maintainer under stage 2 rule 7.
No import cycle was encountered. No dependency interface repair or new notion
was required.

Edge cases checked before writing:

- `T = ∅`: both its closure-interior and the image are empty.
- Empty source: the only subset is empty, so the conclusion holds for any target.
- Empty target: any source admitting a morphism to it is empty; the signature
  retains this case.
- `T = Set.univ`: nowhere density forces the source to be empty, so there is no
  excluded exceptional case or hidden nonemptiness assumption.
- Identity morphisms and finite closed immersions are included. A nonsurjective
  finite morphism does not require restricting the target to its image.
- Nonreduced and non-Noetherian schemes are included; no argument in the cited
  source uses such assumptions. A nonflat finite morphism is also included.

Searches for existing statements (all run for Q145 and this item):

- `msearch.py leanfinder` query:
  `A finite morphism of schemes maps a closed nowhere dense subset to a closed nowhere dense subset`.
  Eight hits, principally `Scheme.Hom.finite_preimage`, finite fibres, finite
  closed-immersion instances and `Scheme.Hom.isClosedMap`; no full statement.
- `msearch.py leansearch` query:
  `The image of a closed nowhere dense subset under a finite morphism of schemes is closed and nowhere dense`.
  Eight hits, including `Scheme.Hom.isClosedMap` and
  `Topology.IsInducing.isNowhereDense_image`. The former gives only closedness;
  the latter assumes a topology-inducing map, which an arbitrary finite scheme
  morphism need not be. Neither is an exact match.
- `msearch.py loogle` query: `AlgebraicGeometry.IsFinite, IsNowhereDense`.
  Zero hits.
- `msearch.py grep` query:
  `[Nn]owhere[Dd]ense|nowhere_dense|nowhere dense`, subdirectory `AlgebraicGeometry`.
  Zero Mathlib hits.
- Direct `rg` searches for `nowhereDense`, `NowhereDense`, `nowhere_dense` and
  `nowhere dense` in `lean/WeilConjectures` and `lean/Sheaf`, followed by searches
  for finite/nowhere-density combinations, found dimension-drop, support and
  alteration statements but no finite-image theorem with these hypotheses.
  `TranslatedCartierParameterFamily` mentions this item only as a proof reference.
- Direct `grep -rn` of the item id in `lean/WeilConjectures` found no occurrence.
  Direct `rg` of the proposed declaration name in both source roots found none;
  a name search of `dag/lean_names_upstream.json` also found no match.

The prescribed compact-object example module is withdrawn; its node points to
`WeilConjectures.CategoryTheory.CompactObject`, which was read for the current
module/header/docstring conventions. There is no repair note for this item.
No statement fault or dispute was found, and no natural-language statement changed.

Validation: prescribed `scompile.py` compiled the sandbox and actual library
module cleanly (5.1 s and 7.3 s respectively), with no errors or extra warnings.
The independent mathematical review belongs to the maintainer, as the current
worker brief requires.

## Second reading by Q145

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
