## Worker report

The module `Sheaf.AlgebraicGeometry.PositiveCopyProjAffineComparison` states
`AlgebraicGeometry.existsUnique_positiveCopyProjAffineComparison`, with `sorry`.
The item node changes only in `lean`. No new nodes, dependency repairs, or statement
corrections are needed.

Three helper definitions belong to the comparison itself, not new independent notions.
`positiveCopyDirectImageAlgebra h` is literally `Under.mk` of `h.c` into the sheaf
pushforward of `T.sheaf`; its sections and structural map are definitionally
`Γ(T, h ⁻¹ᵁ U)` and `h.app U`. `PositiveCopyProj.chartUnit` is the image of the
coefficient unit in degree one. `PositiveCopyProj.fraction` uses the existing
`HomogeneousLocalization.Away.mk` to construct `a[n+1]/t^(n+1)`. All data are explicit;
the homogeneous-membership argument in the fraction definition is only index arithmetic.
The only postponed theorem is the item's theorem, whose docstring contains all seven
steps of the node proof with the dependencies used.

Hypothesis and clause correspondence:

- The schemes and affine morphism are `{T S : Scheme.{u}} (h : T ⟶ S) [IsAffineHom h]`.
  The universe is arbitrary and shared with both schemes and all section rings.
- The algebra E is the actual `positiveCopyDirectImageAlgebra h`; the explicit
  `[...toModule.IsQuasicoherent]` retains the node's quasi-coherence assumption.
- The graded algebra B is `S.GradedAlgebraData`, the recorded relative-Proj input.
  This is the equivalent affine-basis presentation of a quasi-coherent graded algebra,
  with genuine degreewise base-change restrictions. For every affine open and every
  degree, `e U n` is a linear equivalence from the existing `positiveCopyPiece E n`
  onto the degree-n submodule of B. Thus degree zero is the base section ring and
  every positive degree is the actual ring of sections over the inverse image.
  The internal grading on B is already a direct sum; e identifies its summands.
- `hzero` identifies the zeroth inclusion with the algebra structure map, including
  the unit. Linearity of the positive e's gives both mixed scalar products using
  `h.app U`. `hmul` gives every positive-positive product, indexed by m+1 and n+1.
  No multiplicativity of e within one degree is assumed (it would be ill-typed).
- `hres` uses the genuine section restriction of each `positiveCopyPiece` and B's
  recorded graded restriction. It is the compatibility of these identifications
  for every affine inclusion. These hypotheses specify the algebra described in
  the node; they impose no further condition on h or the base.
- α is a ring equivalence from the recorded degree-zero homogeneous localization
  of B at `chartUnit` to the actual coefficient ring on h inverse U.
  Its scalar equation with `fromZeroRingHom` and `e U 0 r` is exactly preservation
  of the base R-algebra structure (and avoids adding competing Algebra instances).
- `Proj.basicOpen ... chartUnit.val = ⊤` says the whole open subscheme is D_+(t).
  It is not just a statement about closed points.
- The `∀ U n a, α U (fraction ... n a) = a` clause is the displayed extraction formula
  for all m≥1, with m=n+1. The next clause gives `(α U).symm a = fraction ... 0 a`.
- `θV U` identifies the affine relative-Proj chart with `(h ⁻¹ᵁ U.1).toScheme`.
  Its equation after the standard-open inclusion is precisely `basicOpenIsoSpec`,
  followed by `Spec.map` of the inverse coefficient ring equivalence, followed by
  `(U.2.preimage h).isoSpec.inv`, the canonical affine identification with the
  actual open subscheme of T. The spectrum map has the contravariant direction
  required in the node.
- ℓ is the restriction homomorphism of the localized chart rings. Its fraction
  equation specifies it on all positive-exponent representatives, hence uniquely
  on all elements. The following two clauses explicitly assert commutation with
  coefficient extraction and with its inverse. The restriction is the actual
  `T.presheaf.map` along `h.preimage_mono i`, not an arbitrary coefficient map.
- The next two clauses express naturality of `(θV U).hom` and `(θV U).inv` for every
  affine inclusion, using the recorded `B.relProjFunctor.map` and `T.homOfLE`.
  This includes all affine refinements of overlaps; intersections need not be affine.
- `∃! θ : B.relProj ≅ T` asserts existence and uniqueness with the prescribed chart
  identifications. `θ.hom ≫ h = B.relProjHom` makes it an isomorphism over S, and
  `B.relProjι U ≫ θ.hom = (θV U).hom ≫ ...ι` gives its local formulas.

Dependency declarations read and reused:

- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`; `IsAffineOpen.preimage` supplies the affine
  identification of every inverse image.
- `def-weil-pbc-quasi-coherent-algebra`:
  `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`,
  `Scheme.IsQuasiCoherentAlgebra` and `Scheme.CommAlgebraSheaf.toModule`.
  Its underlying module predicate is used literally in the hypothesis.
- `lem-trf-positive-copy-graded-quotient`:
  `Sheaf.AlgebraicGeometry.PositiveCopyGradedQuotient`, `positiveCopyPiece` and
  `exists_positiveCopyGradedQuotient`. Read the full theorem and construction.
  The theorem supplies the algebra whose affine-basis presentation the comparison
  takes as input; the definition of its homogeneous pieces is reused literally.
- `def-nagata-relative-proj`:
  `WeilConjectures.AlgebraicGeometry.RelativeProj.GradedAlgebraData` and `.Basic`,
  `Scheme.GradedAlgebraData`, `relProj`, `relProjHom`, `relProjι`, `relProjFunctor`.
  Read also `RelativeProjAlgebra.affineData` in
  `Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction`: it confirms the sheaf
  and affine-basis inputs agree, and no cover/intersection choices are required.
- `def-pc-proj` and `def-nagata-affine-proj`: existing Mathlib `Proj`,
  `projIsoSpec`, `ProjectiveSpectrum.basicOpen`, `Proj.toSpecZero`.
- `def-nagata-homogeneous-localization-degree-zero`:
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`,
  `HomogeneousLocalization.Away`, `.Away.mk`, `.fromZeroRingHom`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- Proof imports: `WeilConjectures.AlgebraicGeometry.RelativeProj.Universal`
  (`existsUnique_relProjIso`, chart colimit uniqueness), and
  `Mathlib.AlgebraicGeometry.Gluing` (`Scheme.Cover.glueMorphisms`,
  `ι_glueMorphisms`, `hom_ext`). The other proof dependencies are already available
  from public imports: `Proj.basicOpenIsoSpec`, `Localization.Away`, affine basis,
  affine Proj and its structural map. Their source signatures and docstrings were read.

Edge cases checked before writing and on the finished statement:

- A=0, even for nonzero R: no Nontrivial assumption; t=0 is permitted by `Away.mk`
  and the Proj standard-open theorem, so its localization is zero and Proj empty.
- Noninjective R→A, for instance Z→Z/2: e in degree zero identifies R with C_0,
  not with A. No injectivity of the coefficient structure map is asserted or used.
- Every positive exponent occurs, including m=1 (`fraction ... 0`); degree-zero
  scalars are covered separately by the explicit scalar equation.
- The empty scheme/base and empty affine opens are included; no Nonempty binder.
- Arbitrary non-Noetherian bases, nonfinite affine h, and nonaffine intersections
  are included. All affine opens/inclusions are quantified without finiteness or
  separatedness assumptions; refinements handle overlaps.

Searches actually run:

1. msearch.py leanfinder: "Relative Proj of the graded algebra with degree zero R and
   a copy of an R algebra A in every positive degree is canonically Spec A".
   Eight hits, including `Proj.toSpecZero`, `projIsoSpec`, `projIsoSpecTopComponent`,
   `ProjectiveSpectrum.Proj.isIso_toSpec`; all concern ordinary Proj or its standard
   chart, not this coefficient equivalence or global affine comparison.
2. msearch.py loogle: `HomogeneousLocalization, AlgebraicGeometry.Proj`.
   Two hits: `Proj.awayι_toSpecZero` and its assoc lemma, not the comparison.
3. msearch.py grep: `projIsoSpec|positiveCopy|positive.copy`, in
   `AlgebraicGeometry/ProjectiveSpectrum`. Five documentation hits about ordinary
   chart isomorphisms; no positive-copy comparison.
4. msearch.py leansearch: "Proj of R plus a copy of an R algebra A in every positive
   degree is Spec A via the degree one unit chart". Eight hits about ordinary Proj,
   its structure map and standard chart, no exact statement.
5. rg in `lean/WeilConjectures` and `lean/Sheaf` for
   `positiveCopy|PositiveCopy|positive.copy`: only the predecessor positive-copy
   graded-quotient module, whose declarations were read in full; no comparison.
   grep of `lean/WeilConjectures` for the item id found no declaration.
6. rg for direct-image CommAlgebraSheaf constructions located the existing literal
   `Under.mk ⟨h.c⟩` expression in `RelativeSpecBaseChange`, not a reusable named
   direct-image algebra definition. The helper reuses that same sheaf construction.

Source checked: `literature/stacks-project/morphisms.tex`, label
`lemma-finite-projective` (0B3I), its projective-bundle embedding and affine calculation.
The explicit positive-copy verification is the node's agent-written refinement of that
argument. No source discrepancy or disputed statement was found.

Validation: prescribed scompile.py compiled this file in both sandbox and library modes
cleanly (2.9 seconds each); no warnings were printed. No live files were edited and
no Git commands or global builds were run directly.

## Second reading by Q25

Sequential rereading by the dispatched worker, with the node and finished module open;
no additional agent was started, as instructed. The maintainer supplies the independent
review. I checked the affine-morphism and explicit quasi-coherence binders; the literal
pushforward coefficient algebra; all degrees of e; the zero, mixed, and positive products;
and the actual restriction maps. I then matched the node's chart equality, extraction
formula, inverse formula, R-scalar compatibility, Spec direction, two coefficient
restriction squares, two scheme restriction squares, and unique global comparison.
The initial draft omitted explicit coefficient restriction squares (although local scheme
naturality implied them); the finished statement adds ℓ, its generator formula, and both
squares. The initial chart unit needed its coefficient-ring type explicitly written, and
the direct-image helper needed noncomputable; both were corrected and recompiled.
No mathematical hypothesis or conclusion was changed in the node.
