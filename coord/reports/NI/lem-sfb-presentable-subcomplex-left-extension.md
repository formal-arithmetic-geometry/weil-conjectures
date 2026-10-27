## Worker report

The module `Sheaf.CategoryTheory.PresentableSubcomplexLeftExtension` states
`CategoryTheory.presentable_subcomplex_left_extension`, with `sorry` as its entire proof.
There are no new definitions, axioms, helper theorems or other nodes. The module docstring
and theorem docstring name the source and blueprint id; the latter gives all eight
steps of the accepted construction, including the two omitted invariant checks.

The input is the current accepted stage-1 split (NE). The stage-2 queue lists this item
and the node has no Lean attachment. The previous unchanged-item rejection was a stage-1
handoff, addressed by coord/brief-stage2.md section 0; the accepted split is preserved.
Only `lean` is added to the node. No repair note for this item is present.

Source checked: Hall--Neeman--Rydh, [arXiv:1405.1888v2](https://arxiv.org/html/1405.1888),
proof of Theorem A.3, induction conditions (1)--(3) and the construction from the first
pullback through the final epimorphic lift. The printed final N^i is N^{i-1}.
Read the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/_section.md`; this is an auxiliary input, not that unit statement.

Hypothesis-by-hypothesis and clause-by-clause translation:

- The universe U is `v`: ambient Hom sets are in `Type v`, the cardinal is
  `Cardinal.{v}`, and presentation categories and coproduct index sets are in `Type v`.
  Ambient objects are `B : Type u`, with independent `u`, so no smallness of the whole
  category or equality of object and Hom universes is imposed.
- Ambient Grothendieck abelian: `[Category.{v} B] [Abelian B]
  [IsGrothendieckAbelian.{v} B]`.
- Full replete A: `A : ObjectProperty B`, its Mathlib `A.FullSubcategory`, and
  `[A.IsClosedUnderIsomorphisms]`. Contains zero: `[A.ContainsZero]`. Closure under
  kernels and cokernels between its objects: `[A.IsClosedUnderKernels]` and
  `[A.IsClosedUnderCokernels]`. Extension closure is `[A.IsClosedUnderExtensions]`.
  In particular A is NOT assumed closed under arbitrary ambient subobjects.
- A Grothendieck abelian with induced exact structure is
  `[Abelian A.FullSubcategory] [IsGrothendieckAbelian.{v} A.FullSubcategory]`.
  The category is the full subcategory of B, not a separate abstract category.
  The kernel/cokernel closure assumptions ensure that its kernels and cokernels
  are the ambient ones: see `ObjectProperty.createsKernels` and `createsCokernels`
  in Mathlib.CategoryTheory.ObjectProperty.Kernels. Thus no independent or altered
  exact structure is introduced. Closure under U-small ambient coproducts is
  `hcoprod : ∀ I : Type v, A.IsClosedUnderColimitsOfShape (Discrete I)`.
- Regular infinite cardinal is `[Fact κ.IsRegular]`; uncountability is
  `hκ : Cardinal.aleph0 < κ`. Mathlib's `IsCardinalFiltered` quantifies over diagrams
  with fewer than κ arrows. Mathlib's `IsCardinalPresentable` says the Hom functor
  preserves these U-small filtered colimits. These are reused, not redefined.
- S = B^κ is `isCardinalPresentable B κ`. Its three closure hypotheses are exactly
  the `IsClosedUnderSubobjects`, `IsClosedUnderQuotients`, and
  `IsClosedUnderExtensions` instances on this property.
- The ambient presentation hypothesis is `hpresentation`: for each X with `A X`,
  a U-small κ-filtered category J, a diagram F in B, and a cocone `ι` with vertex X
  are supplied. `Nonempty (IsColimit (Cocone.mk X ι))` says it is the ambient colimit;
  each `ι.app j` is monic, and every `F.obj j` lies in A and is κ-presentable.
  This is a colimit of subobjects, not an arbitrary abstract presentation.
- Small epimorphism lifting is `hlift`: for every epic p and every f from a
  κ-presentable n there is a κ-presentable m, an epic q to n, a map a to X,
  and the square `a ≫ p = q ≫ f`. `Mono f → Mono a` is the conditional monic
  choice. It imposes no monicity when f is not monic.
- The unbounded ambient complex is `Z : CochainComplex B ℤ`. `hZ` states
  `A (Z.homology j)` in every integer degree. No boundedness on Z is assumed.
- The integers and their inequality are `i b : ℤ` and `hib : i ≤ b`.
- The given partial subcomplex is encoded as `N : CochainComplex B ℤ` with
  `n : N ⟶ Z`, degreewise monic by `hn`. `hbelow` pads it with zero below i;
  `habove` is its stipulated vanishing above b. Padding is an encoding of the
  partially specified complex: there is no condition imposed on ambient Z below i.
  The cochain-map equation and monicity say precisely that the retained
  differentials are the restrictions of the ambient differentials.
- Presentability of its terms is `hsmall`. The padding terms impose no additional
  mathematical restriction, since zero is κ-presentable for infinite regular κ.
- Cohomology in each j>i lies in A intersect S by the two conjuncts of `hcohom`.
- The initial cycle-image invariant is `himage`. `N.cycles i` is the kernel of
  its outgoing differential. `HomologicalComplex.cyclesMap n i ≫ Z.homologyπ i`
  is the canonical map from this kernel to H^i(Z). Its actual categorical image
  is required to satisfy A and `IsCardinalPresentable`.
- The output `M` and degreewise monic `m : M ⟶ Z` encode the extended partial
  subcomplex. It is zero below i-1 and above b; all its terms are κ-presentable,
  in particular the new term `M.X (i-1)` is the required presentable subobject of
  `Z.X (i-1)`. The cochain-map identity gives the restriction of d_Z into degree i.
- The output cohomology conjunct quantifies over every j>i-1 and requires both A
  and κ-presentability. The next conjunct requires both properties for the image
  of the canonical cycles-to-H^{i-1}(Z) map, exactly as in the initial invariant.
- Retention is the last existential: `e j hj : N.X j ≅ M.X j` for every j≥i,
  with `(e j hj).hom ≫ m.f j = n.f j`. Thus the old and new monomorphisms define
  the SAME subobject of `Z.X j`, not merely isomorphic abstract objects.
  The final equation identifies every retained differential under these
  identifications. This is categorical retention of the chosen subobjects and
  their maps. No isomorphism of the entire complexes is asserted, and nothing
  requires the new incoming differential to be zero.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic/convention-only record; rendered by the
  explicit `u v` and size binders above.
- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian`,
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic; signature and
  universe-w docstring read. Here w=v, as its mathlib_match specifies.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone`, `IsColimit`,
  `colimit`, `colimit.desc`, `CategoryTheory.IsFiltered` in the recorded Mathlib
  limits/filtered modules. A supplied cocone with the universal property is used
  rather than imposing a particular choice of colimit object equal to X.
- `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic
  imported publicly. Its underlying `CochainComplex` and canonical cohomology
  constructions are used; no localization or extra HasDerivedCategory hypothesis
  is needed to state this assertion about complexes.
- `def-sp-abelian`: Mathlib.CategoryTheory.Abelian.Basic, `CategoryTheory.Abelian`.
- `lem-sp-abelian-refinements`: recorded Mathlib.CategoryTheory.Abelian.Refinements,
  `ShortComplex.exact_iff_exact_up_to_refinements` and
  `epi_iff_surjective_up_to_refinements`; signatures and documentation read and
  module imported privately for the proof plan.
- `lem-weil-pbc-pushout-short-exact-sequence`: recorded upstream
  WeilConjectures.CategoryTheory.PushoutShortExactSequence,
  `CategoryTheory.pushout_short_exact_sequence`; full signature and proof
  docstring read. Imported privately; no duplicate Sheaf version imported.

Additional existing Mathlib interfaces read: Presentable.Basic
(`IsCardinalPresentable`, `isCardinalPresentable`), Presentable.IsCardinalFiltered,
ObjectProperty.Kernels, Extensions, ContainsZero, EpiMono, FullSubcategory,
ColimitsOfShape, Abelian.Subcategory, and Algebra.Homology.ShortComplex.HomologicalComplex
(`cyclesMap`, `homologyπ`, `cyclesIsKernel`, `homology`). No missing notion needs a
new node or a dependency repair.

Edge cases checked before writing and again against the source: i=b (one initial
term); the zero ambient complex; the zero subcategory; L=0, T=0 or P=0 in the
construction; nonzero T (A need not be subobject-closed); arbitrary negative i;
and no lower bound on Z. All are admitted by the signature. Empty presentation
index categories are correctly excluded by κ-filteredness (κ is infinite), not
by an additional assumption. The displayed isomorphisms retain zero terms above b.

Searches for an existing statement (all searches produced no exact match):

- msearch.py leanfinder: "Extend a presentable partial subcomplex one degree to the
  left with cohomology in a weak Serre subcategory". Eight hits: derived fractions,
  CM5b, K-projectives and derived boundedness; none gives these invariants.
- msearch.py leansearch: "Extending a small subcomplex to the left while controlling
  cohomology in a weak Serre subcategory". Eight hits: extend-complex homology data
  and Serre extension closure; none is this construction.
- msearch.py loogle: "CategoryTheory.IsCardinalPresentable,
  CategoryTheory.IsCardinalFiltered". Eleven hits, including presentable Hom
  factorization through colimits. These provide the existing definitions used;
  none states the partial-subcomplex extension.
- msearch.py grep: "subcomplex|subComplex", Algebra/Homology: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id,
  `presentableSubcomplex`, `presentable_subcomplex`, and the combined phrases
  `presentable.*subcomplex|subcomplex.*presentable`: no existing declaration.
- rg in the same project roots for `IsCardinalPresentable|IsCardinalFiltered`:
  existing uses in presentability, Gabriel--Popescu, plus construction and
  derived-factorization modules, no partial-subcomplex extension.
- tools/blueprint_refs.py search "partial subcomplex": zero matching blueprint nodes.
  Read the neighboring cardinal-package DAG node: that is the cardinal-existence
  package, not this one-degree extension statement. Its properties are already
  explicit hypotheses of this item's accepted statement.

No statement correction, new nodes, dependency modules, or STATEMENT-DISPUTED flag.

Validation: scompile.py compiled this file both as its isolated sandbox module and
as `Sheaf.CategoryTheory.PresentableSubcomplexLeftExtension`, cleanly in 1.2 seconds
per file, under the default 60-second limit. No compiler warnings or errors remain.

## Second reading by NI

I made a separate clause-by-clause reread of the finished file against the DAG
statement and HNR A.3; this is a worker self-check, not an independent review.
The maintainer's independent delivery review remains required. No other agent was
started, as the dispatcher brief prohibits delegation.

The reread checked in particular that the small lift includes its conditional
monicity, presentations have monic ambient cocone legs, A is only weak Serre,
all integer degrees and independent object universe u remain available, and the
new cycle-image condition is at i-1. Retention is over Z and includes the outgoing
differentials, so it does not replace a chosen subobject by an unrelated copy.
The only compiler repair was parentheses around the isomorphism type in the
dependent retention family. No mathematical mismatch was found or silently changed.
