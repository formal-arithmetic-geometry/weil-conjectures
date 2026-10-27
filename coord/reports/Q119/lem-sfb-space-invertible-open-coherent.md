## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceInvertibleOpenCoherent` states
`AlgebraicGeometry.AlgebraicSpace.invertible_open_coherent`, with its proof left
entirely `sorry`. Its three concrete helper definitions are the existing line predicate
on coherent objects, the full total subcategory, and its actual inclusion. These are
constructions of the categories specified by this node, not new independent notions.

Source read: Stacks Project, literature/stacks-project/quot.tex,
lemma-picard-stack-open-in-coh, Tag 0D03, complete statement and proof. The source allows
an algebraic-space base B; this node specifies a scheme S and hence uses the special
case B=S, without changing the node.

Hypothesis and clause correspondence:

- S is `{S : Scheme.{u}}`; X is `{X : AlgebraicSpace S}`. The target of f is
  `schemeSpace (Over.mk (𝟙 S))`, namely the base scheme as its representable algebraic
  space. This expresses the node's f:X→S, with no chosen atlas.
- Flatness is `hflat : MapIsFlat f`; properness is `hproper : MapIsProper f`; finite
  presentation is `hfp : ProperQuotFinitePresentation f`. The last predicate includes
  local finite presentation, quasi-compactness and quasi-compactness of the diagonal,
  exactly the conjunction in flat_proper_fp_locality.
- The coherent category is literally `CoherentModuli.category f`. Its objects retain
  the test scheme and its map, a module on `properQuotFibre f T`, quasi-coherence,
  finite presentation, relative flatness and the closed-proper-support presentation.
  Its arrows are actual isomorphisms from the specified tensor pullback, with the
  existing normalized identity and composition comparisons. No eligibility condition
  is replaced with an abstract support or an arbitrary category.
- A line is `(properQuotFibre f F.base).IsLineModule F.module`, via
  `CoherentModuli.isLine f`. The existing definition is local isomorphism to the
  structure module on covering sieves of the small etale ringed site. The full
  subcategory and inclusion are `lineModuliCategory` and `lineModuliInclusion`.
- The first conjunct quantifies over EVERY raw line module L on EVERY test fibre,
  and supplies `F : CoherentModuli f` with `F.base = T` and `HEq F.module L`.
  HEq is necessary only because the module's type depends on the base; it identifies
  the exact original module after transporting by the stated base equality. Thus
  the line category loses no line module through the coherent eligibility fields.
- Fully faithful is explicitly the conjunction of `.toFunctor.Full` and
  `.toFunctor.Faithful` for the canonical inclusion.
- The existential `U : OpenModuliSubstack (CoherentModuli.category f)` has
  `U.property = CoherentModuli.isLine f`. In particular its fields assert the fibred
  groupoid property, stability under all cartesian arrows and, for every test map
  from h_T, an open immersion representing the actual 2-fibre product. Its
  `ModuliTwoIso` identifies the equivalence's projection with that open immersion.
- For each F the final conjunct supplies `W : F.base.left.left.Opens`, the actual
  open subscheme W.toScheme of its base scheme. For every `T'` and `v : T' ⟶ F.base`,
  the line condition is exactly tensor pullback along `properQuotFibreMap f v`, and
  the other side is `∃ a, a ≫ W.ι = v.left.left`. This is precisely factorization
  through the open immersion. No flatness, finite type or reducedness condition is
  placed on v. Every underlying scheme map into the base is represented this way,
  using its composite to S (and its consequent map to the terminal scheme space).
- Representation of the 2-fibre product is supplied by `U.open_pullback`. The
  universal factorization property identifies its open with W: both represent the
  same line predicate on all scheme tests. Thus the explicit open and the
  open-substack clause describe the same subfunctor, including projection data.
- No Noetherian, reduced-fibre, section or cohomological-flatness hypotheses occur.

Dependencies read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `Modules`,
  `structureSheaf`, `IsLineModule` (available publicly through the imported dependencies).
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality:
  `flat_proper_fp_locality`; its existing morphism predicates are used in the signature.
- Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral: `CoherentModuli`, its `Hom`,
  `category`, and the full signature and proof docstring of `coherent_stack_general`.
- Sheaf.AlgebraicGeometry.SpaceCotangentRingMap: the recorded enlarged-site interface,
  read with the underlying `EnlargedEtaleRingedSite.schemeSpace` construction.
  Tensor pullback remains the recorded canonical chart-normalized adjoint construction,
  not an arbitrary functor or map and not an additional parameter.
- Sheaf.AlgebraicGeometry.OpenModuliSubstack: `fullModuliSubcategory`,
  `fullModuliInclusion`, `OpenModuliSubstack`, and its `open_pullback` field.
- Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor, through the coherent-category import:
  `ProperQuotTest`, `properQuotFibre`, `ProperQuotFinitePresentation`,
  `properQuotFibreMap` (actual sheaf fibre products and induced maps).
- Proof imports: AlgebraicSpaceRelativeFiniteFreeLocusBaseChange,
  AlgebraicSpaceAffineEtaleCover, AlgebraicSpaceFibreProductsEtaleCovers,
  AlgebraicSpaceModuleOperations, and WeilConjectures.FieldTheory.CommonExtensionFields.
  Their recorded declarations and source proof explanations were read. The theorem's
  docstring carries the complete node proof: eligibility and pullback stability,
  relative free locus, rank one, proper image complement and point lifting, and the
  contractible-fibre representing equivalence.

Edge cases checked before writing: empty X and empty fibres give all of T as the
line-admissible locus, since the zero and unit modules agree on the empty site;
F=0 or a locally free module of constant rank two on a nonempty fibre excludes
that fibre; rank-one modules give the whole base. Mixed ranks use the complement
of the rank-one locus, rather than support. Arbitrary nonflat and nonreduced test
schemes are included in the universal quantifier. A single explicit universe u
follows the existing algebraic-space size convention and does not equate independent
site universes or restrict test schemes beyond the established convention.

Searches made (2026-10-24):

- msearch.py leanfinder: "Invertible modules form an open substack of coherent flat
  modules with proper support on a flat proper finitely presented algebraic space
  over a scheme". Eight hits, including Module.isOpen_freeLocus,
  UniversallyOpen.of_flat and algebra smooth/etale loci; none states this theorem.
- msearch.py loogle: `"IsLineModule", "OpenModuliSubstack"`. Zero hits.
- msearch.py leansearch: "The line bundles form an open substack in the stack of
  finitely presented relatively flat quasi coherent modules with proper support".
  Eight hits, including SheafOfModules finite-presentation/quasi-coherence results;
  no open-substack theorem.
- msearch.py grep: `invertible.*(stack|locus)|PicardStack|picard_stack|coherent.*stack`.
  Zero Mathlib hits. The corresponding rg search of lean/WeilConjectures and
  lean/Sheaf found only related scheme loci, existing coherent-stack interfaces,
  and mentions of the scheme-only openness prerequisite; no algebraic-space theorem.
- rg for IsLineModule/LineModuli/lineModuli found the existing IsLineModule definition
  and its consumers, reused here; no existing full line-family category in this setting.
- rg for the item id in lean/WeilConjectures, and for the chosen declaration in
  dag/lean_names_upstream.json, returned no hits. The actual chosen declarations
  do not duplicate upstream or Mathlib names.

No statement dispute, statement correction, new node or dependency repair is needed.
The compile wrapper successfully compiled both the sandbox and named library module,
with no diagnostics. The only postponed theorem is invertible_open_coherent.

## Second reading by Q119

I reopened the node, the complete Tag 0D03 proof and the final module for a separate
reading after compilation. This is the dispatcher's single-worker rereading; the
maintainer's independent review remains separate, as required by this assignment.
No other agent was started.

The read checked every node clause against the correspondence above. In particular,
the ambient category is the algebraic-space coherent category, not the older
scheme-module category; the line predicate is the original small-etale predicate;
finite presentation includes both quasi-compactness conditions; and no hypothesis is
imposed on the test maps. The first conjunct is essential: without it a full
subcategory of coherent objects alone would not expressly retain every raw line
module named in the node. It identifies both base and module, so no extra assumption
on a raw line is hidden. The Full/Faithful fields refer to the actual inclusion.
The `OpenModuliSubstack` equality fixes precisely the line predicate; its open-pullback
representation includes the projection 2-isomorphism. The final universal criterion
identifies the same representing open by Yoneda. Empty and rank-zero cases were
reread against the proof's closed complement C, not a support complement.

The initial compile caught an extra closing parenthesis in each of two test-type
binders. These were removed; the subsequent sandbox and library-mode compile was
clean. No mathematical statement or dependency interface changed during this reading.
