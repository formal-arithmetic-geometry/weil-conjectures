## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent` states
`AlgebraicGeometry.locallyOfFinitePresentation_of_fpqc_cover`, with only `sorry` as proof.
No definitions, new nodes, dependency modules or statement corrections are needed.
The source was read at https://stacks.math.columbia.edu/tag/02KY because the local
literature/stacks-project/descent.tex is absent. Tag 02KY states fpqc locality on the base;
this node takes its descent direction. Its finite-type slips in the proof are already
identified in the node, and do not affect the statement.

Hypothesis and clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`; morphism f: `(f : X ⟶ S)`.
- Arbitrary indexing set I: `{I : Type v}`, with `v` explicitly declared and independent
  of the scheme universe. No nonemptiness, finiteness or smallness assumption is imposed.
- Schemes S_i and morphisms g_i: `(S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)`.
- The family is an fpqc covering: `hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`.
  This uses exactly the declaration recorded by def-weil-pbc-fpqc-covering: flatness,
  joint surjectivity and quasi-compactness of the covering family. In particular it does
  not demand that every g_i is quasi-compact. The affine finite-image condition agrees
  with QuasiCompactCover, including its n = 0 case.
- X ×_S S_i is the chosen `pullback f (g i)`. Its second projection to S_i is
  `pullback.snd f (g i)`; the first projection would have the wrong codomain.
- Every f_i is locally of finite presentation: the explicit proof argument
  `h : ∀ i, LocallyOfFinitePresentation (pullback.snd f (g i))`.
- Conclusion: `LocallyOfFinitePresentation f`. No global finite presentation,
  quasi-compactness, quasi-separatedness or affine hypothesis is added.

Dependency declarations used (all dependencies have status mathlib, so no Sheaf import
or dependency record repair is necessary):

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`, in
  Mathlib.AlgebraicGeometry.Scheme. Read the structure definitions and their docstrings:
  schemes are locally ringed spaces locally isomorphic to affine spectra, and morphisms
  are locally ringed-space morphisms.
- def-weil-pbc-fpqc-covering: `AlgebraicGeometry.Scheme.fpqcPrecoverage`, in
  Mathlib.AlgebraicGeometry.Sites.Fpqc. Read its full definition and docstring, and
  Mathlib.AlgebraicGeometry.Cover.QuasiCompact (QuasiCompactCover and the finite affine
  refinement lemma). It is `propQCPrecoverage @Flat`, precisely the recorded definition.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback` and `pullback.snd`, in
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback. Read their full signatures
  and docstrings; schemes have pullbacks, so no existence hypothesis is introduced.
- def-sbc-locally-finite-presentation: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  in Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation. Read its full class signature
  and docstring. The dependency's Mathlib match explains equivalence of its affine-open
  condition with the node's pointwise condition. The comparison with global finite
  presentation in that definition is not a hypothesis or conclusion of this item.

Both imports are used: FinitePresentation supplies the property, Sites.Fpqc the covering.
The declaration docstring gives all six proof steps and their DAG references.

Edge cases checked: I may be empty (a covering by the empty family forces the base to
be empty, so the conclusion is vacuous). The empty source is allowed. Empty covering
components and repeated indices are allowed. Finite affine refinements permit n = 0
for the empty affine open. The schemes are arbitrary, not Noetherian, separated, affine,
or over a field. All variables and universes are explicitly bound.

Searches for an existing statement, performed by msearch.py and source reads:

- LeanSearch: “locally of finite presentation descends along fpqc covering families of
  schemes”. Service unavailable (Internal Server Error); recorded in searches.jsonl.
- LeanFinder: the same query. Eight hits, including LocallyOfFinitePresentation,
  base-change/composition instances and single-morphism flat-descent machinery;
  no specialization to this covering-family statement.
- Loogle: `AlgebraicGeometry.LocallyOfFinitePresentation,
  CategoryTheory.Limits.pullback.snd`. One hit: the instance asserting that base change
  preserves local finite presentation; it is the opposite direction to this node.
- msearch grep: `LocallyOfFinitePresentation|of_isPullback` in AlgebraicGeometry/Sites.
  Seven hits concern fppf coverings, effective epimorphisms and general covering stability;
  no theorem for descent of local finite presentation along an fpqc family.
- rg of WeilConjectures for the item id and local-finite-presentation descent names:
  no exact specialization. Read WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc,
  especially `AlgebraicGeometry.Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`.
  That generic theorem quantifies over a property P, arbitrary cartesian squares and
  a covering sieve in the generated topology. It provides a proof route after
  specialization and passage from precoverage to topology, but does not itself have
  the node's signature using its recorded fpqc family and chosen second projections.
- rg of lean/Sheaf for fpqc and descent: related Etale, closed/open immersion and finite
  descent statements, but none stating this item. FpqcDescentEtale uses the same
  covering-family and second-projection representation.
- rg for `locallyOfFinitePresentation_of_fpqc_cover` throughout the source checkout
  and lean/Sheaf: no collision.

No STATEMENT-DISPUTED finding or node fault. Server compilation and the delivery dry run
are the validation; the second reader supplies the independent second reading.

## Second reading by J1

I independently read the item node, its four statement-dependency nodes, their
recorded Mathlib declarations and the delivered module. The object/hypothesis/conclusion
list, in the node's order, is:

1. Schemes X and S: `{X S : Scheme.{u}}`. The structure `Scheme` at
   Mathlib/AlgebraicGeometry/Scheme.lean:42 is a locally ringed space with affine
   neighbourhoods; `Scheme.Hom` at line 74 is a locally ringed-space morphism.
   These are precisely def-pc-scheme's objects. Verdict: exact.
2. An arbitrary morphism f from X to S: `(f : X ⟶ S)`. No affineness,
   separation, Noetherian, field or finite-type condition is introduced. Verdict: exact.
3. An indexing set I, schemes S_i and maps g_i to S: `{I : Type v}`,
   `(S' : I → Scheme.{u})`, `(g : ∀ i, S' i ⟶ S)`. The family is quantified
   before its hypotheses, with no finiteness or nonemptiness requirement. Verdict: exact.
4. This family is an fpqc covering: the argument
   `hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`. I read
   `fpqcPrecoverage := propQCPrecoverage @Flat`,
   `propQCPrecoverage P := qcPrecoverage ⊓ Scheme.precoverage P`, the latter's
   joint-surjectivity and arrow-property conditions, and `QuasiCompactCover`.
   Its finite compact-open image condition is equivalent to the finite affine-open
   image condition of def-weil-pbc-fpqc-covering: compact opens admit finite affine
   covers, and affine opens are compact. The precise finite affine refinement is
   `QuasiCompactCover.exists_isAffineOpen_of_isCompact`. Repeated indices are permitted.
   Individual g_i need not be quasi-compact. Verdict: exact, not a singleton specialization.
5. For each i, the fibre product X ×_S S_i and its projection f_i to S_i:
   `pullback f (g i)` and `pullback.snd f (g i)`. I read the chosen limit
   definition and the second projection's signature in HasPullback.lean:95,115,
   together with `HasPullbacks Scheme` in AlgebraicGeometry/Pullbacks.lean:485.
   No extra existence binder is needed. This is def-pc-fibre-product's chosen object
   and correctly oriented projection. Verdict: exact.
6. Every f_i is locally of finite presentation: the argument
   `h : ∀ i, LocallyOfFinitePresentation (pullback.snd f (g i))`. I read the
   class's affine-pair condition at Morphisms/FinitePresentation.lean:45 and
   `HasRingHomProperty.iff_exists_appLE` at RingHomProperties.lean:651. With the
   finite-presentation localization stability used by that class's ring-property
   instance, this equals def-sbc-locally-finite-presentation's pointwise condition.
   No global finite-presentation condition is imposed. Verdict: exact.
7. Conclusion: `LocallyOfFinitePresentation f`, the same property as in item 6,
   on the original morphism. There is no additional conclusion. Verdict: exact.

Source check: local Stacks TeX was absent. I fetched the official Stacks repository's
`descent.tex` into this item's scratchpad and read lines 5280–5342 and 5767–5795,
including the surrounding setup and definition of locality. This agrees with
[02KY](https://stacks.math.columbia.edu/tag/02KY) and
[02KO](https://stacks.math.columbia.edu/tag/02KO); the covering definition is
[022B](https://stacks.math.columbia.edu/tag/022B).
There are no standing Noetherian, affine or separated hypotheses on the general
statement. The affine assumptions in the proof concern its reduction only. The
generic base S in 02KO imposes no restriction here: local finite presentation is a
property of the underlying morphism, independent of such a base. Both finite-type
phrases in the source proof are accounted for by the node's finite-presentation
argument. The delivered docstring follows each of the six node proof steps and
names their dependencies, including tensor-factor exchange and the final criterion.

Edge cases: an empty I is allowed; joint surjectivity then forces S empty, and a
morphism X → S forces X empty too. Empty X, empty components and repeated indices
are allowed. The finite affine refinement quantifies over `n : ℕ`, so n = 0 is
allowed for the empty affine open. No characteristic, nonzero-ring, field or rank
assumption appears. Explicit universes u and v are unrestricted; the index universe
is independent of the schemes' universe and has no smallness instance. Any finite
collection of schemes can be placed in one common universe. There are no quantified
test schemes in a smaller universe that could make the hypotheses vacuous.

Independent searches, with different queries from the worker:

- LeanSearch via msearch: "finite presentation locally descends on a scheme under
  flat covering families". The service returned Internal Server Error; unavailable,
  not evidence of absence, and recorded in searches.jsonl.
- LeanFinder via msearch: "local finite presentation property descends from jointly
  covering flat quasi compact families". Eight hits: the generic single-map
  flat-descent instance and the definition/affine characterization, composition and
  openness results; no exact covering-family theorem.
- Loogle via msearch: `"fpqc", AlgebraicGeometry.LocallyOfFinitePresentation`.
  Zero hits.
- rg on Mathlib, WeilConjectures and lean/Sheaf for fpqc, local finite presentation,
  descent spellings and the proposed declaration name. I opened
  Morphisms/LocalFlatDescent.lean and the source's
  WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:115–126. The former
  states descent along one surjective flat quasi-compact morphism; the latter is
  `Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`, parameterized by a morphism
  property, its locality/descent/base-change instances, arbitrary cartesian squares
  and a covering sieve in the generated topology. It is a proof tool for this node,
  not an existing declaration with this node's hypotheses and conclusion. No exact
  specialized theorem or name collision was found in either project tree.

No mismatch was found. The Lean module and node record are unchanged. No new
definition nodes, dependency modules or statement correction are present or needed.
There is one theorem, with only `sorry` as its proof, and no definitions that could
be hollow. Both imports are used; the namespace, header, blueprint docstrings and
line lengths follow the conventions. All variables and universes are explicitly
bound. The recorded `lean.statement` equals the signature in the file verbatim.
The independent server single-file compile passed in 1.7 seconds, exit code 0,
with no warnings. This reading adds only this report section and search evidence.
