## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProjDegreeOneQuotients` states
`AlgebraicGeometry.AlgebraicSpace.existsUnique_spaceProj_degreeOne_quotient` with
`sorry`. Its auxiliary definitions expand the quotient input and the specified
fraction-chart conclusion; their data are explicit. No mathematical theorem is proved.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `{X Y : AlgebraicSpace S}` are precisely
  the existing fppf-sheaf algebraic spaces. The one explicit universe `u` is the
  universe of schemes and coefficients used by the recorded space interfaces.
- `A : SpaceProjInput X` has the actual homogeneous module sheaves `A.piece`,
  `A.algebra : EtaleGradedModuleAlgebra A.piece`, and degreewise `IsQuasicoherent`.
  No total-section direct-sum equality is assumed.
- `_hzero : IsIso A.algebra.unit` says that the structural map identifies A_0
  with O_X, including its prescribed scalar and unit structure.
- `_hgen` says the algebra of each affine open on every scheme pullback is
  `Algebra.adjoin` of its degree-one piece. Since its degree-zero structural map
  is invertible and each degree is quasi-coherent, this is equivalent to
  surjectivity of A_1^{tensor n} to A_n as sheaves, for every positive n:
  locally a homogeneous degree-n element is a linear combination of degree-n
  monomials, and on affines quasi-coherence identifies a surjection with the
  corresponding module surjection. No finite set of generators is chosen.
- `C : SpaceProjCoefficients S` and `R : SpaceProjRealization C A` are the
  existing normalized coefficients and realization in the conclusion of
  `exists_space_relativeProj_scheme_tests`; these specify the relative Proj
  named in the node. They are parameters for that same object and its
  scheme-test comparisons, not an additional existence or geometric hypothesis.
- `f : Y ⟶ X`, `L : Y.Modules`, and `hL : Y.IsLineModule L` are the given
  S-morphism and small-etale line module. `lineTestFamily Y L hL` is the recorded
  cartesian realization of this very line, determined up to its unique compatible
  isomorphism by `exists_linePresentation`. There is no arbitrary auxiliary line.
- The quotient map is `ψ : SpaceProjLineQuotient C A f (lineTestFamily Y L hL)`.
  This uses the adjoint scheme-test description already employed by
  `GradedLineMap`: on every test `g : schemeSpace W ⟶ Y`, its `component` is the
  O_W(V)-linear map from `(C.scheme A W (g ≫ f)).affine.grading V n` to the actual
  sections of the n-th tensor power of the pulled-back line. `unit` preserves
  the degree-zero unit and `mul` preserves homogeneous multiplication through
  the existing tensor-power concatenation isomorphism. `naturality` identifies
  all homogeneous images after the specified coefficient base change and
  cartesian line pullback. It applies to every scheme map `a`, including open
  restrictions and identities. These are the data and laws of the original
  graded sheaf-algebra map in its equivalent adjoint presentation, not additional
  constraints. The HEq only handles the associativity equality of the composite
  scheme-test maps; the coefficient morphism itself is C.schemeBaseChange.
- `_hψ : ψ.IsSurjectiveInDegreeOne` is the sheaf surjectivity condition expressed
  locally: at every point of every scheme test an affine neighbourhood has a
  degree-one homogeneous section whose image is a basis of the pulled-back
  line. A surjection of a quasi-coherent module onto a line locally lifts a
  basis; conversely these lifted bases make it a sheaf epimorphism. The existing
  right unitor identifies tensorPow 1 with the line itself.
- The conclusion is `∃! r : Y ⟶ R.space, ψ.IsCanonicalMap R r`.
  Its first clause is exactly `r ≫ R.projection = f`.
- The remaining clause of `IsCanonicalMap` quantifies over every scheme test,
  every affine base open V, every a of degree one, and every smaller open U
  on which its image is a free generator. It supplies an actual morphism
  `q : U.toScheme ⟶ Spec (HomogeneousLocalization.Away ... a.val)` and an
  S-morphism `b` into the scheme-test Proj. The first equation identifies b
  with q followed by `Proj.awayι` and `affine.relProjι V`. This is precisely
  the requested factorization through D_+(a). The next equation identifies
  its image under `R.compare` with the restriction of `g ≫ r`.
- For every n and homogeneous v of degree n, the final equation is
  `lineProjScalar U q (Away.mk ... n v) • psi(a)^tensor n = psi(v)|_U`.
  Here `lineProjFramePower` forms the actual tensor power, and the right
  unitor identifies psi_1(a) with a line section. Because this section is a
  basis, the equation is equivalent to v/a^n mapping to psi_n(v)/psi_1(a)^n.
  It implies the formula in every chosen frame, without selecting a frame or
  division by a possibly nonunit scalar. Replacing a frame by u times that
  frame scales the two degree-n coefficients by the same u^{-n}; hence the
  quotient is unchanged. All source opens and all scheme tests are quantified,
  so the normalization is retained after arbitrary chart changes.
- There are no quasi-compactness, quasi-separatedness, Noetherian, separation,
  flatness, or finite generation hypotheses. Uniqueness expresses the word
  canonical: the local fractions cover the source by degree-one surjectivity.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `Modules`,
  `IsLineModule`, the small etale structure sheaf and site.
- `def-weil-size-convention` is the recorded metatheoretic convention, with
  explicit universe binders rather than a duplicate Lean definition.
- `Sheaf.TraceFormula.EtaleGradedModuleAlgebra`: `EtaleGradedModuleAlgebra`
  and its unit and multiplication fields, reexported through the Proj input.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the recorded
  specialization of `SheafOfModules.IsQuasicoherent` on this space site.
- `Sheaf.AlgebraicGeometry.SpaceRelativeProjSchemeTests`: `SpaceProjInput`,
  `SpaceProjCoefficients`, `SpaceProjRealization`, `spaceProjScheme`,
  `spaceProjOpenChart`, and `exists_space_relativeProj_scheme_tests`.
  The scheme coefficient maps, normalized affine homogeneous sections, and
  realization comparison are reused without modification.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `moduleTensorSection`, `moduleTensorAdjunction`;
  these are the tensor pullbacks underlying the reused coefficient system.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and the
  existing ordinary-scheme tensor-power API provide the recorded sheaf tensor.
- Added the already landed `def-trf-space-line-module-proj-input` to stmt_deps,
  using `Sheaf.TraceFormula.SpaceLineModuleProjInput`: `lineTestFamily`,
  `TestLineFamily`, `SchemeTests`, and the existing tensor-power pullback
  comparisons `boundaryPullbackPowIso` and `boundaryTensorPowIso` it imports.
  The space-base `SpaceProjLineQuotient` expands this same adjoint graded-map
  presentation using the existing C.scheme coefficients; it is not a second
  construction of tensor powers, line modules, or relative Proj.
- `Sheaf.TraceFormula.LineProjAffineChartAtlas`: `lineProjFramePower` and
  `lineProjScalar`, and Mathlib's `HomogeneousLocalization.Away.mk` and
  `Proj.awayι` give the actual normalized fraction-chart formula.

All recorded proof dependency modules that have declarations are imported.
The proof docstring follows all seven DAG steps: compatible scheme atlases,
Zariski/etale and tensor transport, the local degree-one covering argument,
fraction-chart gluing, equality on overlaps, etale morphism descent, and
independence/uniqueness and change of frame. The original node statement and
proof are unchanged. No dependency repair or new DAG node is needed.

Sources read: spaces-divisors.tex, lemma-relative-proj-generated-in-degree-1
(Tag 085D), and the complete setup and characterization (3) of
lemma-invertible-map-into-relative-proj (Tag 0D2Z). The latter explicitly uses
arbitrary commuting scheme-chart squares, rather than only cartesian ones.

Edge cases checked: empty X, empty Y and empty scheme tests impose no
nonemptiness binder; zero source with a nonempty target cannot satisfy the
local basis condition; if A has only degree zero, no nonempty source admits a
surjective degree-one quotient. Empty opens permit the unique zero-ring map.
The fraction formula includes n=0 and uses the structural unit, n=1 uses the
right unitor, and nilpotent or zero a has empty generator locus on nonempty
ordinary schemes. No assumption about reducedness, integral domains, or
nonzero denominators globally is made. Infinite generating families and
non-affine scheme overlaps are allowed. The explicit universe u is the same
one fixed by all recorded space, line, and tensor coefficient interfaces.

Searches made using msearch.py:

- LeanFinder: "A graded algebra map to tensor powers of a line bundle
  surjective in degree one defines a morphism to relative Proj over an
  algebraic space". Eight hits, led by Proj.fromOfGlobalSections, Proj,
  Proj.toSpecZero and Proj.awayι. No exact space-base line-quotient theorem.
- Loogle: `"Proj", "invertible"`. Only Module.Invertible.instProjective;
  this is projectivity of an ordinary module, not the requested map.
- grep in Mathlib/AlgebraicGeometry:
  `AlgebraicSpace|generatedInDegreeOne|invertible.*[Pp]roj|[Pp]roj.*invertible`.
  Zero hits.
- LeanSearch: "Relative Proj represents line bundles with a surjective
  graded algebra map in degree one". Eight scheme Proj hits including
  Proj.fromOfGlobalSections and its restriction formula, no exact match.
- rg of the upstream WeilConjectures source for degreeOne, DegreeOne,
  proj/quotient combinations, and the exact node id found no exact theorem.
  rg of lean/Sheaf found the reusable SpaceRelativeProjSchemeTests,
  SpaceLineModuleProjInput, SpaceLineModuleProjMap, and LineProjAffineChartAtlas.
  The existing space_line_module_proj_map has a scheme base T and arbitrary
  positive generation locus, so is not the present space-base statement.
  The existing GradedSheafAlgebra.IsGeneratedInDegreeOne is a Zariski-site
  definition, not the small-etale space-algebra interface, so the hypothesis
  is expressed with existing Algebra.adjoin on the recorded scheme tests.

Validation: the prescribed scompile.py checks the complete module on the server.
Only the named main theorem contains sorry. There are no disputed statements
or source-based statement corrections.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
