## Worker report

The delivery states `AlgebraicGeometry.ClosedIntersection.closed_intersection_vertex_contraction`.
Its only theorem has proof `sorry`; every helper is actual data or a structure of data and
identities. No definition chooses a complex, a comparison, or a contraction from existence.
The original statement, proof, proof dependencies, status, and source are unchanged.

Hypothesis and clause correspondence:

- `X Z : Scheme.{u}`, `i : Z ⟶ X`, `[IsClosedImmersion i]` give the ambient scheme and
  closed augmentation support. `W : Fin m → Over X` and `hclosed` give the ordered closed
  family; `hfactor` supplies its factorizations through Z. The nonempty family is `hm`.
  There is deliberately no covering hypothesis.
- `hqc` and `hqcW` express precisely quasi-compact complementary open immersions, using
  scheme opens with the stated complementary ranges. These are morphism quasi-compactness
  assumptions, not quasi-compactness of the open subscheme as a space.
- `A : Sheaf (ProEt.topology X) CommRingCat.{u+1}` is an arbitrary commutative ring sheaf.
  `Modules A` abbreviates the recorded `ringedSiteModules` of its underlying ring sheaf.
  All coefficient rings are actual `inverseRing` objects, with no finite, constant,
  flatness, or scheme-affineness assumption on X.
- `intersection i W s` is Z at the empty index and the existing scheme-theoretic finite
  product over X otherwise. `term` is the recorded inverse image followed by direct image.
  `unit` is the recorded section-normalized adjunction unit, not an arbitrary adjunction.
- `Row.restriction_unit` specifies actual restrictions by the unit equation. Under the
  hypotheses these units are epimorphisms by ringed open-closed localization, so that
  equation uniquely fixes the pushed unit, including the augmentation. Non-inclusions are
  zero. There is no arbitrary unspecified natural transformation in place of a restriction.
- `Degree m p` consists of subsets of cardinality p+1; the empty subset has degree -1.
  `graded` is their finite categorical product, hence the canonical finite direct sum in
  this abelian category. `Row.terms` and `Row.differential` identify the entire complex
  with these terms and the explicitly defined signed deletion matrix. It gives coefficient
  (-1) to the number of preceding vertices, exactly the position of the deleted vertex.
  In degree -1 this is the all-singleton augmentation. The support conjunct of the theorem
  explicitly covers p < -1 and p ≥ m.
- The first conclusion is finite-limit and finite-colimit preservation for every `term`,
  including the empty term E_Z: exactness in the module category.
- The affine-cover conjunct quantifies over every universe-indexed family of affine opens
  covering X, and every integer cochain complex K. Its equivalence of `Acyclic` predicates
  is exactness detection on that cover. An empty cover of an empty scheme is permitted.
- Every open immersion g has an augmented pulled-back row D' and `OpenCompatibility`.
  Its `units`, `faces`, `rowIso`, and `components` give the claimed open restriction
  identifications, not just an unnormalized isomorphism of complexes. The `baseChange`
  field records the actual closed base-change mates for every summand.
- If Y is affine, every vertex has `VertexContraction D' a`. Its base-change comparisons
  identify the pulled-back summands with direct images from the fibre-product intersections.
  `squareCoefficients` is the canonical comparison of the two inverse-image rings.
  `BaseChange.normalized` fixes the inverse-image square on successive original unit
  sections, using the canonical pasting of test objects; `mate` fixes the closed direct
  image comparison as the adjunct of that square followed by the closed counit.
  `unionIntersection` identifies those actual fibre products with the union-index
  intersections over X. The `faces` and `restriction_units` equations identify faces
  with the actual unit-preserving restrictions on these intersection summands.
- `augmentation` and `augmentation_unit` give i_a^* E_Z ≅ i_a^*, preserving the actual
  augmentation. The `back`, `left_inverse`, and `right_inverse` fields give the inverse
  of the restriction adjoining a vertex, including the empty index. Its identification
  with the closed counit is the triangle identity under the prescribed base-change mate.
- `h`, `component_zero`, and `component_insert` specify the entire natural homotopy by
  product projections. The insertion coefficient is exactly (-1)^{card {b ∈ J | b<a}}.
  The empty output uses the singleton projection followed by `back ∅`. `contraction`
  is dh+hd=1 in every integer degree. The canonical `XIsoOfEq` only identifies
  (p+1)-1 with p; it changes neither map nor degree convention.
- The last conclusion is zero after restriction to every complementary open in the affine
  chart, in every degree and for every module. Every construction is a functor, natural
  transformation or natural isomorphism of module categories, so all asserted maps are
  linear over their displayed inverse-image rings and natural in M.

Dependency declarations read and used:

- Mathlib: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Scheme.ProEt`, `ProEt.topology`,
  `IsClosedImmersion`, `IsOpenImmersion`, `QuasiCompact`, `Limits.pullback`, and
  `HomologicalComplex`/`CochainComplex`/`Acyclic`. The finite-type node's quasi-compact
  declaration is the relevant clause; local finite type is not imposed.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is the
  existing `SheafOfModules` abbreviation for an arbitrary ringed site.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage` and
  `proEtaleModuleInverseImage`, retaining the small site's object universe u+1 and
  morphism universe u.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`: `proEtaleModuleCoefficients`,
  `proEtaleRingedDirectImage`, and `proEtale_ringed_open_closed`.
- `Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection`:
  `ProEtaleClosedProjection.adjunction` and its unique sectionwise-unit characterization.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`: `Rings`, `Modules`,
  `inverseRing`, `inverse`, `restrict`, `inverseSection`, `ringComp`, `moduleComp` and
  their unique section-normalization characterizations.
- Existing finite-intersection helpers in `FiniteClosedCoverResolution` are attached to
  the new primitive definition node. Its covering-resolution theorem is not assumed.
  That parent theorem has this item as a proof dependency, so citing its theorem as a
  DAG prerequisite would make a cycle. Its helper definitions have real independent data.
- The recorded ordinary composition, geometric inverse exactness, ring-sheaf base-change
  mates, localized restriction exactness, module colimits/forgetful, and weakly-etale
  localization modules are imported as proof dependencies. Mathlib adjunction and
  homology-preservation imports supply the recorded Mathlib proof leaves. The unstated
  signed-refinements proof dependency has no module to import and is not assumed as a
  hypothesis; the theorem's proof plan cites it as the accepted split does.

Sources read: proetale.tex at labels lemma-closed-immersion (09AA),
lemma-closed-immersion-complement-retrocompact-exact (09BM), and
lemma-ses-associated-to-open (09AH), together with every step of the item's accepted proof.
The contraction is the agent-formulated consequence in that proof, not an assertion that
Stacks directly supplies an insertion homotopy.

Edge cases checked before drafting: m=1, repeated/equal members, empty closed members,
empty Z or empty affine chart, non-covering families, degree -1, singleton subsets, the
full vertex set in degree m-1, and degrees outside the finite range. If a belongs to J,
only deletion of a survives in dh; otherwise deletion of inserted a gives the identity
and each other deletion cancels with the matching dh term. This checks the exact sign.
No restriction on coefficient characteristic occurs; the signs are integer scalar actions.

Searches actually run through msearch.py (full results recorded in searches.jsonl):

- leanfinder: "An augmented alternating complex of closed intersections of proetale module
  sheaves contracts after inverse image to one member"; 8 hits, including profinite
  Nobeling exactness and condensed-module constructions; none is this statement.
- loogle: "Homotopy, CochainComplex"; 12 hits about general homotopies and mapping cones;
  none constructs these closed-intersection comparisons or this finite insertion formula.
- grep: "vertex.*contract|closed.*intersection|insertion.*homotop"; 25 unrelated topology
  and finite-intersection hits, no canonical sheaf comparison/contraction.
- leansearch: "Finite closed intersection diagram and alternating Cech cochain differential
  for module sheaves"; 8 hits, including generic alternating coface complexes, none for
  these finite closed-intersection module rows and their augmentation.
- rg on both lean/WeilConjectures and lean/Sheaf found the finiteClosedIntersection,
  finiteClosedRestriction, finiteClosedUnit and signed-differential helpers in the parent
  module. Those are reused. No exact theorem for the present node was found; searching
  its exact id in WeilConjectures found none. DAG grep found no owning definition node
  for these helpers. tools/blueprint_refs.py search "finite closed intersection" returned
  zero blueprint nodes. Its ancestor command returned None, matching the item's own
  blueprint.from.node; the new nodes preserve this source route and prepend this item.

No statement correction and no STATEMENT-DISPUTED flag.

## New nodes

`def-sfb-closed-intersection-primitives` attaches the exact existing intersection,
closed-restriction, unit, family/complex pullback, and normalized compositor helpers to
a definition node. It creates no Lean module or duplicate construction. The helper
signatures/docstrings were read in the parent finite-cover and tensor-comparison modules.
Searches above found these declarations but no definition node owning their notions.
The parent covering theorem is intentionally not used as a prerequisite.

`def-sfb-closed-intersection-augmented-row` defines the data structures and explicit
signed matrices described above in its own module. This adds the empty-index augmentation,
canonical square coefficients and mates, open row comparisons, and specified vertex
contraction data that no usable recorded interface supplies. Existing module inverse
images, site/module categories, intersections and units are reused. Every structure merely
packages actual objects/maps and equations; existence is the item's postponed theorem.
The three search services, Mathlib grep, project grep and blueprint/DAG searches above
were checked before writing it.

## Second reading by Q134

Self-audit only: this dispatcher explicitly forbids starting another agent; the maintainer
will perform the independent reading. Re-read the node and both modules clause by clause.
Caught and repaired the distinction between the empty product X and augmented empty term Z;
kept the latter explicit. Checked that the homotopy uses both inverse equations, that its
sign counts vertices in the output subset, and that the degree arithmetic cast uses the
canonical complex equality isomorphism. Added explicit face/unit compatibility on the
base-changed intersection terms. The normalized square uses the actual sectionwise
pasting equation and its beta has the prescribed counit mate, preventing scalar twists.
There is no cover hypothesis. No original node field other than lean and the authorized
new-definition stmt_deps entry is changed.

Validation: scompile.py compiled both delivered modules cleanly. The first dry run requested
`import_flags` on new definition nodes; added empty arrays as required by current preflight.
