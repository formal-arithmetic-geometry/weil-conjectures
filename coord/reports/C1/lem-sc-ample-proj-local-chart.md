## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AmpleProjLocalChart.lean` states
`AlgebraicGeometry.Scheme.Modules.exists_sectionRing_proj_affine_charts` with its only
proof `by sorry`. No definitions or auxiliary theorems are delivered.

Hypothesis and clause correspondence:

- An arbitrary scheme X is `(X : Scheme.{u})`; `universe u` is explicit and unrestricted.
- The invertible module is `(L : X.Modules) [L.IsInvertible]`, using the recorded upstream
  class, without a field, finite-type, nonempty, Noetherian, or separation assumption.
- The graded ring S is `InvertibleSectionRing L`, implicitly the carrier of
  `sectionRingGrade L`: its degree-n subgroup is the range of `DirectSum.of` into the
  direct sum of `SectionRingComponent L n = Γ(L.tensorPow n, ⊤)`. Its multiplication
  tensors sections and applies `tensorPowAddIso.inv`; its unit is the degree-zero 1.
- A homogeneous section is `(s : sectionRingGrade L d)`. Its underlying ring element is
  `s.val`, and its actual section in degree d is `s.val d`. Every global section of
  the tensor power gives such a ring element by `DirectSum.of`, and evaluation recovers
  it; thus no section is excluded or introduced.
- Positive degree is `0 < d`, both in the cover and in the universal chart clause.
- The open X_s is `generatingLocus (s.val d)`. For an invertible module, freely generating
  at a point means that the local coefficient in a trivialization is a unit; this is
  exactly nonzero residue-field value, or germ outside maximal-ideal times the stalk.
- The assumption that these opens cover is `hcover : ∀ x : X, ∃ (d : ℕ)
  (s : sectionRingGrade L d), 0 < d ∧ x ∈ generatingLocus (s.val d)`.
- Existence of the canonical morphism is `∃ f : X ⟶ Proj (sectionRingGrade L)`.
  To specify "canonical", the second conjunct records the local quotient formula of
  01PZ/01N8: `f.app` composed with `Proj.awayToSection` sends `ξ/s^n` to the function
  whose scalar product with the restricted `s^n` equals the restricted numerator.
  Powers are the actual ring powers of `s.val`, and numerator degree is `n • d`.
  This is a characterization of the word canonical, not a further hypothesis on X or L.
  The denominator section is a free generator on X_s, so the formula determines every
  quotient uniquely; `HomogeneousLocalization.Away.mk_surjective` covers all fractions.
- The inverse-image clause is literally `f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val =
  generatingLocus (s.val d)`, for every homogeneous positive-degree section.
- Ampleness in the last conditional is `IsAmple X L` from the recorded absolute
  ampleness module, not the upstream relative very-ample-power notion.
- Affineness of X_s is `IsAffineOpen (generatingLocus (s.val d))`.
- The induced chart morphism being an isomorphism is
  `IsIso (f ∣_ Proj.basicOpen (sectionRingGrade L) s.val)`. The source of this restriction
  is the inverse-image open; the first conjunct identifies it with X_s. Consequently
  this is exactly X_s → D_+(s), with no extra choice of unrelated isomorphism.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, tensor powers and exponent isomorphisms
  (available through the section-ring import).
- `Sheaf.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme` and `.Basic`:
  `AlgebraicGeometry.Proj`, `projIsoSpec`, `Proj.basicOpen`, `Proj.awayToSection`.
- Newly landed `Sheaf.AlgebraicGeometry.InvertibleSectionRing`:
  `InvertibleSectionRing`, `SectionRingComponent`, `sectionRingGrade`,
  `sectionRingGCommRing`, `sectionRingGradedRing`.
- `WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus`:
  `generatingLocus`, `GeneratesAt`, and its docstring/local coefficient criterion.

The two already-landed definition node IDs `def-sc-invertible-section-ring` and
`def-sc-section-generating-locus` are added to `stmt_deps`, under the standing rule
allowing landed statement dependencies. These definitions appeared during this worker's
search; the provisional duplicate section-ring draft was removed. Their complete modules
and node records were read. The canonical-map statement
`exists_sectionRing_proj_morphism` in `Sheaf.AlgebraicGeometry.AmpleProjCanonicalMap`
was also read: it has the same cover, inverse-image identity, and quotient formula.
It does not assert the additional affine-chart isomorphism, so it is not an existing
match for this item. It is a proof dependency, not an extra assumption or a copied definition.

Edge cases checked: the empty scheme needs no nonempty assumption and satisfies the
pointwise cover vacuously. The zero positive-degree section has empty nonvanishing open
and D_+(0) is empty, so the chart assertion is the empty-scheme isomorphism.
Degree d = 0 is deliberately excluded by the node; numerator exponent n = 0 is included
and gives the degree-zero functions formula. Nilpotent sections also have empty
nonvanishing loci. No characteristic or quasi-compactness assumption is imposed for the
canonical-map clause; quasi-compactness enters only through the conditional ampleness.
For X affine and L trivial this specializes to the standard polynomial-ring Proj chart;
for projective space with O(1) it gives the usual affine standard opens.

Source checked directly: the local literature checkout lacks properties.tex, so the
public Stacks pages https://stacks.math.columbia.edu/tag/01PZ and
https://stacks.math.columbia.edu/tag/01Q1 were opened. The first gives the cover hypothesis,
canonical morphism and inverse-image identity; the second's localization paragraph proves
the affine-chart conclusion. The theorem docstring carries all five DAG proof steps.
There is no statement correction, dispute, missing dependency, or new node in this delivery.

Searches (real tool calls recorded in searches.jsonl):

- LeanFinder: "canonical morphism from scheme to Proj of section ring of invertible sheaf,
  inverse image of standard open and affine chart isomorphism" returned generic Proj
  basic-open isomorphisms and toBasicOpenOfGlobalSections, not this line-bundle theorem.
- Loogle: "DirectSum, GradedMonoid.GCommRing, GradedRing" returned no hits and an unknown
  identifier diagnostic for GradedMonoid.GCommRing; no claim of a successful match.
- Mathlib grep: "sectionRing|SectionRing|GradedMonoid|section.*[Rr]ing" in AlgebraicGeometry
  returned generic graded Proj/localization declarations, no section-ring theorem.
- LeanSearch: "graded section ring direct sum of global sections of tensor powers of a
  line bundle" and "canonical morphism from scheme to Proj of the section ring locally
  sends t over s to t divided by s" were unavailable (Internal Server Error).
- LeanFinder: "graded section ring direct sum of global sections of tensor powers of an
  invertible sheaf with tensor multiplication" found only generic Proj structure-sheaf
  declarations and awayToSection, no graded section-ring construction.
- Local rg of WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `sectionRing|SectionRing|sectionMul|SectionGrade|IsSectionRingMorphism|ample_proj_local_chart`
  found the newly landed section ring and canonical-map statement, not the affine-chart
  result. The exact node ID search in WeilConjectures had no match.
- DAG rg and `tools/blueprint_refs.py search 'section ring'` initially found no definition;
  a later rg found the two landed definition nodes, which this delivery uses.

Validation: server compilation of the final 70-line module succeeded in 1.9 seconds
without any warning or error. Every variable and universe is explicitly bound.


## Second reading by C1

I independently opened the item node, its sandbox module, every statement-dependency
node and the actual declarations they record. The local Stacks checkout is absent.
I read the public pages for 01PZ, 01Q1, 01N8 and 01PS, then read the corresponding
raw `properties.tex` and `constructions.tex` from the Stacks project itself:
https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex and
https://raw.githubusercontent.com/stacks/stacks-project/master/constructions.tex.
The opening of the ample-invertible-sheaves section assumes no ambient field,
Noetherian, separated, finite-type or characteristic hypothesis. The node extracts
the canonical-map and affine-chart assertions; it does not request every other
conclusion of 01PZ or the dense-image assertion of 01Q1.

Object, hypothesis and conclusion checklist (in the node's order):

1. Arbitrary scheme X: `(X : Scheme.{u})`. Verdict: exact. I read Mathlib's
   `Scheme` structure and morphisms, not just the dependency name.
2. Invertible O_X-module L: `(L : X.Modules) [L.IsInvertible]`. Verdict: exact.
   The recorded `Scheme.Modules.IsInvertible` class requires local isomorphism
   to the structure sheaf; this is local freeness of rank one, and therefore
   implies quasi-coherence. It introduces no additional assumption on X.
3. Nonnegatively graded section ring S: `sectionRingGrade L` grades the direct
   sum `InvertibleSectionRing L`. Verdict: exact. The landed dependency module
   defines `SectionRingComponent L n` as the actual tensor-power global sections,
   multiplication using `tmulSection` and `tensorPowAddIso.inv`, and the unit via
   `unitSectionsEquiv`. I read all operations and grading instances. Their data
   are explicit; their postponed laws are named theorems, not hollow data.
4. Positive-degree homogeneous s: `(d : ℕ) (_hd : 0 < d)
   (s : sectionRingGrade L d)`. Verdict: exact. The range of `DirectSum.of`
   identifies these elements with all global sections of `L.tensorPow d`;
   evaluation `s.val d` recovers the section. `s.val` is its ring element.
5. Nonvanishing open X_s: `generatingLocus (s.val d)`. Verdict: exact.
   I read upstream `GeneratesAt`, `generatingLocus`, `IsFreeGenerator` usage and
   `generatesAt_iff_mem_basicOpen`: in a trivialization the coefficient is a unit
   exactly on this open. For rank one this agrees with the nonzero residue-field
   value in the node and source; it is not the nonzero-stalk-section locus.
6. Positive-degree nonvanishing opens cover X: the pointwise `hcover` existential
   over d and s, with `0 < d ∧ x ∈ generatingLocus (s.val d)`. Verdict: exact.
   No finite cover, common degree, affineness or ampleness is assumed here.
7. A single canonical morphism X → Proj(S): `∃ f : X ⟶ Proj (sectionRingGrade L)`.
   Verdict: exact, including canonicality. I read the actual Mathlib Proj
   definition, `Proj.awayToSection`, `HomogeneousLocalization.Away.mk` and
   `Away.mk_surjective`. The middle conjunct says that f pulls a fraction ξ/s^n
   back to the coefficient whose product with the restricted section s^n is ξ.
   The equation is in sections of `L.tensorPow (n • d)` on the inverse-image
   open, not in the ring on a different open. The first conjunct identifies
   that open with X_s, where s^n is a free generator. Consequently the equation
   uniquely determines each chart ring map; surjectivity of Away.mk covers all
   fractions, and the covering hypothesis determines the global morphism.
   This renders the canonical morphism of 01PZ/01N8 rather than strengthening
   the node with an unrelated ring-map requirement.
8. Every positive-degree homogeneous s has the inverse-image equality:
   `f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val =
   generatingLocus (s.val d)`. Verdict: exact, for every s, not just cover members.
9. If L is ample and X_s affine, the induced map is an isomorphism:
   `IsAmple X L → IsAffineOpen (generatingLocus (s.val d)) →
   IsIso (f ∣_ Proj.basicOpen (sectionRingGrade L) s.val)`. Verdict: exact.
   I read the recorded absolute `Scheme.Modules.IsAmple`, which requires
   quasi-compactness and an affine nonvanishing neighbourhood at each point,
   exactly as 01PS. I also read Mathlib's `morphismRestrict` in `Restrict.lean`:
   its source is the inverse-image open and its target the standard open.
   Thus the first equality identifies precisely the induced X_s → D_+(s),
   not some independently chosen isomorphism. Ampleness and affineness remain
   conditional conclusions, with neither smuggled into the input binders.
10. Quantifiers: one f is chosen before all d and s; both the inverse-image and
    chart assertions concern that same f. Verdict: exact. No section-dependent
    choice of f, hidden extra instance or unbound variable occurs.

Edge cases: the empty scheme satisfies hcover vacuously and is not excluded.
The empty family can cover only an empty scheme; no index-type constraint is
introduced. A zero positive-degree section has empty generating locus and
`Proj.basicOpen_zero = ⊥`; the formula and chart isomorphism include this case.
A nilpotent homogeneous section likewise has empty locus. The zero module on
a nonempty scheme is not invertible in either the source or Lean, while the
empty scheme admits its vacuous invertibility condition. Degree d = 0 is
excluded exactly as S_+ in the node, but fraction exponent n = 0 is included:
tensorPow 0 is the structure-sheaf unit and the formula is the degree-zero
pullback formula. No characteristic restriction occurs. Explicit universe u
is arbitrary; the section ring and its Proj have the same universe as X, so
there is no extra smallness assumption.

Independent searches, using different phrases from the worker (recorded by
msearch.py in searches.jsonl):

- LeanFinder: "ample invertible sheaf affine nonvanishing open isomorphic Proj
  homogeneous localization" returned eight generic Proj/localization hits.
  I opened `basicOpenIsoSpec`, `basicOpenIsoAway`, `awayToSection` and their
  signatures: they give the target chart description for any graded ring,
  not this section-ring morphism or its affine source-chart isomorphism.
- Loogle: `AlgebraicGeometry.Proj, CategoryTheory.IsIso` returned zero hits.
- LeanSearch: "An ample line bundle gives a canonical morphism to the Proj of
  its section ring which identifies each affine nonvanishing open with the
  corresponding standard open" was unavailable (Internal Server Error).
  This is a recorded service failure, not evidence of absence.
- rg of Mathlib AlgebraicGeometry, upstream WeilConjectures AlgebraicGeometry
  and project lean/Sheaf/AlgebraicGeometry for Proj with ample/invertible,
  ample with Proj, section-ring variants and Γ_* found only generic charts,
  the landed section-ring definition and canonical-map theorem, and upstream
  finite-coordinate projective-space constructions. I opened
  `exists_isImmersion_projectiveSpace_of_isAffineOpen`: it assumes a separated
  locally finite-type morphism over an affine base and has a finite family
  of sections, and concludes an immersion into projective space. It is not
  this unrestricted section-ring theorem. The landed
  `exists_sectionRing_proj_morphism` was read in full: it has the covering,
  inverse-image identity and fraction formula but no affine-chart isomorphism.
  Exact theorem-name and node-name searches across all three Lean trees had
  no existing match. Thus H4 does not call for dropping this module.

No new definition node or dependency module is delivered. The two added
statement dependencies are already-landed nodes, and their recorded notions
are usable as-is. The item has no statement correction, so the corrected-node
and citer-verdict checks are inapplicable. I found no mathematical or Lean
mismatch and made no change to the statement, node record, imports or proof.
The module and theorem docstrings name the source and blueprint id and carry
all five proof steps, including the Veronese reindexing and the affine
Spec–Gamma criterion. There is exactly one theorem with proof `by sorry`, no
new definition, no proof attempt, and no line over 100 characters. The recorded
`lean.statement` was checked by an exact string comparison against the file's
signature and agrees verbatim.

Independent validation: scompile.py compiled the unchanged 70-line module on
the server in 2.0 seconds, exit 0, with no error or warning. Second reading
changed only this report, adding the independent clause-by-clause review.
