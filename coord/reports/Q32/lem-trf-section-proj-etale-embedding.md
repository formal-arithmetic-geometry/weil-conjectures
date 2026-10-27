## Worker report

Item: `lem-trf-section-proj-etale-embedding`; group Q32; stage 2; 2026-10-24 UTC.
Module: `Sheaf.TraceFormula.SectionProjEtaleEmbedding`.
Main declaration: `AlgebraicGeometry.AlgebraicSpace.section_proj_etale_embedding`.
The only postponed proof is this named theorem, whose docstring gives all five DAG
proof steps and the source places. `SectionProjModel` is a structure with actual data
and equations; there is no data-valued sorry, axiom, chosen arbitrary map, or proof of
a new theorem in this delivery. The node changes only in `lean`.

Sources read: Stacks `spaces-descent.tex`, Tag 0D3C,
`lemma-descending-property-ample`, lines 2125–2207, especially its section algebra,
evaluation, full generation locus, and canonical open-immersion paragraphs; the
recorded declarations and docstrings for Tags 0D2Z and 01O9 in
`SpaceLineModuleProjInput` and `SpaceLineModuleProjMap`. The latest blueprint
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` was checked.
As the accepted split already records, its current local-term lemma is no longer the
historical polarized-scheme descent sentence: this node is the independently sourced
0D3C geometric sublemma, not the unit's own statement.

Hypotheses, one by one:

- Schemes S and T over S: `(S : Scheme.{u}) (T : Over S)`. Keeping the structural
  morphism of T as part of `Over S` renders the stipulated morphisms over S.
- Algebraic space X: `(X : AlgebraicSpace S)` from the recorded definition.
- Morphism f over S: `(f : X.obj.obj ⟶ yoneda.obj T)` is the natural transformation
  of the underlying sheaves on Sch/S, exactly the full-category notion of morphism.
- Quasi-compactness and separation: `hqc : IsQuasiCompactPresheafMap f` and
  `hsep : IsSeparatedPresheafMap f` are the recorded dependency predicates. There is
  no representability or scheme hypothesis on X.
- Line module: `L : X.Modules`, `hL : X.IsLineModule L`. Its actual cartesian
  realization is the existing `lineTestFamily X L hL`, not an independently chosen
  line bundle. Its `module` at an étale scheme test is canonically isomorphic to
  `schemeRestriction` of L; the theorem explicitly returns those isomorphisms for
  each local X_i and for the final representing scheme.
- The indexed schemes and maps are `I : Type v`, `Tᵢ`, `g`; étaleness is `hget`.
  The index universe is unrestricted independently of u, as no limit is indexed by I.
- Joint surjectivity is `hcover`: every scheme-test map to T lifts to some T_i
  locally for the fppf topology. For an étale scheme family this is equivalent to
  joint surjectivity on points: base change a surjective étale family to get the
  local lifts; conversely a covering sieve with such lifts detects every point.
  It does not assert that a test map globally lifts to one member. The stronger
  `IsJointlySurjectiveEtaleFamily` in SpaceQCSeparatedEtaleLocal is deliberately
  not used: for example two proper opens covering a scheme do not globally lift
  its identity to either open. The same local-lifting encoding is already used in
  the recorded open-immersion descent theorem.
- Scheme realizations of X_i and their projections: `Xᵢ`, `k`, `fᵢ`, `hcart`.
  `IsPullback (k i) (yoneda.map (fᵢ i)) f (yoneda.map (g i))` is the universal
  property identifying X_i with the sheaf fibre product, not just a commutative square.
- Forming A_i and psi_i: `Mᵢ i : SectionProjModel ...` presents the actual
  section algebra of the restricted line module. `Mᵢ i` is supplied as the
  canonical object mentioned in the node, in any presentation. Its
  `SpaceSectionAlgebra.sections` field is the full compatible-section universal
  property and its `evaluation_cartesian` and `sections` equations uniquely fix
  the adjunction evaluations. Its `degreeIso` is a linear equivalence on all
  homogeneous affine sections; `mul`, `unit`, `restriction` identify the entire
  graded algebra, and `evaluation_eq` fixes every homogeneous evaluation. Hence
  these binders do not assume existence of arbitrary comparison maps or an extra
  geometric property. They allow every presentation of the canonical local objects.
- The given local canonical maps are `rᵢ`. `hgen` states the positive-degree
  generation open is top. `hcanonical` is precisely the recorded
  `GradedLineMap.IsCanonicalMap` predicate, using the top-subfunctor inclusion to
  give the requested domain. `hopen` states the ordinary scheme maps are open
  immersions. No ampleness assumption was added.

Conclusions, clause by clause:

- The existential global `M.sections : SpaceSectionAlgebra ...` gives A. Its
  `degree` is the degreewise direct image characterized by compatible sections;
  `degree_quasiCoherent`, `graded`, `total`, `inclusion`, `sum`, `sum_mul`,
  `sum_unit` give the quasi-coherent unital graded Zariski algebra and its sheaf
  coproduct, with all nonnegative degrees, including zero. Sections of an infinite
  coproduct on arbitrary opens are not confused with a direct sum of sections.
- Its affine presentation is `M.affine`. The linear `M.degreeIso` identifies each
  homogeneous piece on every affine open; the adapter's equations identify products,
  units and restrictions. Since the affine graded ring is an internal direct sum,
  these equivalences specify a graded algebra isomorphism on each affine open and
  hence specify the same quasi-coherent graded sheaf algebra used by relative Proj.
- `M.evaluation` and `evaluation_eq` identify the Proj-input graded homomorphism
  with the actual `M.sections.evaluation`, not an arbitrary map. Linearity gives
  the tensor formula with arbitrary local scalar coefficients from its formula
  on every `1 ⊗ s`.
- For each i the actual `SpaceSectionAlgebraBaseChange β` gives all degree and
  total isomorphisms, compatibility with each homogeneous inclusion, products and
  unit, and equality of evaluations on every scheme chart. Its `evaluation` field
  is exactly the identity of the restricted section and its evaluated image.
- `D : PullbackData ...` gives the coefficientwise base change of the affine
  graded presentation. The displayed equation involving `D.map`, `degreeIso`,
  `β.degree` and `sectionAlgebraPullSection` fixes that comparison as the actual
  restriction/tensor-pullback comparison in every degree and every affine subopen.
  The `IsBaseChange` conjunct identifies the canonical graded evaluation maps.
- The existing `M.affine.relProj` is already a `Scheme.{u}`; no separate assumed
  scheme realization of P or arbitrary Proj object is introduced. `projOver` retains
  its actual structural map to T and S.
- `M.evaluation.IsGenerationOpen ⊤` is U(psi)=X. The global map r has the full
  original X as its domain; composing with the top inclusion gives exactly the
  domain requested by `IsCanonicalMap`. That predicate fixes its homogeneous-fraction
  chart construction and its map over T.
- `IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) r` gives the global
  representable open immersion, on every scheme test, with no new hypothesis.
- `IsPullback D.relProjComparison ...` expresses the canonical local-Proj fibre
  product identification. The following equation on every scheme test W and every
  W→X_i says that the very supplied r_i, rather than merely some local maps, are
  base changes of r under this identification.
- The final `U`, `e : yoneda.obj U ≅ X.obj.obj` explicitly exhibit X as a scheme.
  The scheme map q is an open immersion and its Yoneda map is `e.hom ≫ r`.
- `M.sections.AgreesWithSchemes` quantifies over every representing scheme and
  identifies each degree with ordinary `Scheme.Modules.pushforward` of the actual
  line-module tensor power, and each evaluation with its ordinary tensor-pullback
  adjunction counit. In particular it applies to the returned U and e.hom. The
  local `AgreesWithSchemes` clauses give the same normalization on each X_i.
  `IsCanonicalMap` itself is the ordinary homogeneous-fraction formula on schemes,
  as specified in the recorded Proj-map dependency. Thus q is the ordinary canonical
  map for this ordinary section algebra and its evaluation. The final `schemeRestriction`
  isomorphism explicitly identifies its invertible module with the recorded restriction
  functor applied to L.

Recorded dependency declarations used (all their signatures and relevant docstrings
were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `Modules`, `IsLineModule`,
  `IsRepresentableWith`, `IsEtale`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`,
  `IsSeparatedPresheafMap` (the stronger global-lift family predicate is not needed).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`,
  carried by `TestLineFamily.invertible` on the actual restricted modules.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `Sheaf.TraceFormula.SpaceLineModuleProjMap`: `space_line_module_proj_map`;
  its public input module provides `lineTestFamily`, `TestLineFamily.pullback`,
  `GradedLineMap`, `IsGenerationOpen`, `IsCanonicalMap`, `IsBaseChange`, `projOver`.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`: `QuasiCoherentAlgebra`.
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`: `GradedSheafAlgebra`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`: `GradedAlgebraData.relProj`,
  `relProjHom`; BaseChange provides `PullbackData`, `relProjComparison` and `isPullback`.
- `Sheaf.TraceFormula.SpaceSectionAlgebraEtaleBaseChange`: `SpaceSectionAlgebra`,
  `SpaceSectionAlgebraBaseChange`, `SpaceSectionAlgebra.AgreesWithSchemes`,
  `sectionAlgebraPullSection`, `space_section_algebra_etale_base_change`.

Plain imports retain the already-stated proof dependencies:
`GradedEvaluationZariskiEtaleComparison`, `RelativeProjAffineRestriction`,
`AlgebraicSpaceFibreProductsEtaleCovers`, `SpaceOpenImmersionEtaleLocal`.
`lem-trf-graded-pushforward-etale-restriction` has neither a Lean record nor a Mathlib
match in the current DAG, so has no proof import yet (stage-2 rule 7 applies only to
stated proof dependencies). It is not needed to type this statement. Its intended
restriction formula is already part of the statement via the section-algebra comparison.

Edge cases checked before writing and in the second pass:

- Empty I: hcover forces T empty; the morphism then forces X empty. No `Nonempty I`
  or selected cover member appears, so this valid case remains included.
- Empty X or empty local scheme: no point or nonzero-section hypothesis is used.
- Identity cover: the comparisons include identity base change and return the ordinary
  scheme section algebra and canonical map, not merely an unspecified isomorphic map.
- Infinite covers: the covering sieve and every local-map clause allow them; no finite
  subcover is hypothesized, and the index universe v is explicit and unrestricted.
- Degree zero is retained in every linear equivalence, unit and comparison. No equality
  A_0=O_T is imposed; e.g. a nontrivial affine f and L=O_X need not have that equality.
- The generation condition concerns some positive degree, via the recorded predicate;
  it does not impose degree-one generation. No finite generation of A is assumed.
- For a scheme with L=O(-1) over a point, the local hypotheses need not hold; the
  theorem does not silently infer them from the line-module hypothesis alone.
- The base-change condition uses full pullback squares; commutativity alone is not
  substituted for the fibre product.

Searches made with the prescribed wrapper and direct source searches:

1. `msearch.py ... leanfinder "An algebraic space whose canonical section algebra Proj
   maps are open immersions on an etale scheme cover is a scheme"`: 8 hits, including
   locally-ringed-space open-immersion scheme construction, `Proj`, `IsAffine`, and
   étale scheme objects; no matching theorem.
2. `msearch.py ... loogle "AlgebraicGeometry.Proj, AlgebraicGeometry.IsOpenImmersion"`:
   4 hits on affine Proj chart immersions and affine chart maps, no descent statement.
3. `msearch.py ... grep "section.*[Pp]roj|[Pp]roj.*section" AlgebraicGeometry`:
   18 hits on affine Proj sections and homogeneous-fraction maps, no algebraic-space
   section-algebra embedding theorem.
4. `rg` for `lem-trf-section-proj-etale-embedding`, `section_proj_etale_embedding`,
   `SectionProjModel`, and section/Proj patterns in the exact read-only
   `lean/WeilConjectures`, `lean/Sheaf`, relevant Mathlib directories, and the upstream
   name index; and `grep -rn` for the exact node id in `lean/WeilConjectures`:
   no existing declaration for this node or adapter. Existing `SpaceSectionAlgebra`
   and canonical Proj-map declarations were found and reused rather than copied.

The interface adapter is a helper belonging to this item's statement, under the
human's missing-helper authorization; it adds no independent mathematical notion
and therefore no new DAG node. There are no dependency modules or statement corrections.
No STATEMENT-DISPUTED flag is needed for this item. The family-predicate defect noted
above is avoided by spelling out the existing local-lifting cover encoding, without
changing the dependency node or strengthening this statement.

Validation: both the initial module and the final restriction-comparison version were
compiled with the prescribed `scompile.py Q32 lem-trf-section-proj-etale-embedding ...`.
Both sandbox and library-module compiles were clean; the final pair took 7.6 s and
4.9 s, within the unchanged 60-second limit. No local or global build was run.

## Second reading by Q32

A separate pass through the source node and the completed module was made in this
worker session. The dispatcher explicitly forbids starting another agent; this section
records a fresh self-reading, not a claim that an independent worker reviewed it.
The maintainer's independent review is still the delivery review.

The main mismatch found in the first draft was the absence of an explicit comparison
to the recorded `schemeRestriction` functor. The final statement now returns its
isomorphism to the actual cartesian line-family module for each X_i and for the final
representing U. A redundant repeated `AgreesWithSchemes` conjunct was removed from
that final existential: the universal clause near the start already applies to U.
The revised file was recompiled cleanly.

On re-reading, f is still arbitrary quasi-compact separated (not assumed representable),
X is still an algebraic space, and the local schemes are full pullbacks. The cover is
only locally split as it should be, the canonical maps are the supplied r_i, and every
homogeneous section is identified by an actual linear equivalence. Those equivalences
respect restriction, products and the unit, and evaluation_eq fixes the entire graded
map. The β and D comparison normalizations agree on all local tensor generators,
including degree zero. The global generation locus is top, r is representably open,
the returned U represents X, and its map q agrees with r and hence the ordinary
canonical homogeneous-fraction construction. No hypothesis or conclusion of the node
was removed or changed. Only the `lean` field of its JSON copy was changed.
