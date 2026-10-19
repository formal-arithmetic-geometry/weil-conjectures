## Worker report

The module `Sheaf.Paper.TraceFormulaCurveIntegralLattice` states
`WeilConjectures.exists_curve_integral_lattice`, with its sole theorem proof `sorry`.
The helpers are actual constructions from recorded coefficient actions, homology,
kernels, cokernels, compact sections, scalar extension, and derived localization.
All are listed in `lean.declarations`; no new independent notion or dependency repair
is needed. The node's natural statement and dependencies are unchanged.

Source read: main-20261015,
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`, Step 5,
and all four proof steps of the DAG item. The helper docstrings give this same source.

Hypotheses and conclusions, in their Lean order:

- `T : TraceFormulaCoefficientConventions.{u}` supplies the global finite-field datum,
  prime distinct from its characteristic, finite coefficient extension, valuation ring,
  uniformizer, separated finite-type `X₀`, geometric fibre, and its structure map.
  The positive level stored in T is immaterial: every conclusion quantifies over all
  levels, using n+1 for the source's positive integer n.
- `_hdim : topologicalKrullDim T.X₀.left ≤ 1` is exactly the curve dimension bound;
  there is no smoothness, connectedness, or nonemptiness hypothesis.
- `K_E` and `K_O` are in the recorded intrinsic rational and integral categories.
  `_alpha` is the given isomorphism from the localization of K_O to K_E.
- `_hheart : sfRationalHeartProperty ... K_E` is, definitionally, the intersection of
  `sfRationalStandardClass ... true 0` and `sfRationalStandardClass ... false 0`.
  It assumes precisely that K_E is a degree-zero rational sheaf. There is no Weil
  structure, finite-level antecedent, or admissibility hypothesis.
- `latticeCohomology K_O` is C = H⁰(K_O), in the actual completed-coefficient module
  category `scalarReductionSource`. `latticeScalar C n` is its scalar action by ϖ^n,
  obtained by restricting `integralScalarChainAction` to the single complex.
- The existential exponent e and first conjunct assert that every positive-power
  kernel lies in the kernel at e+1. As this kernel is itself in the family, its
  union D equals that kernel and is killed by ϖ^(e+1). This equivalent stabilized
  kernel formulation avoids introducing a second power-torsion notion.
- `latticeQuotient K_O e` is the cokernel of that kernel inclusion, exactly C/D.
  The existential integral object M and its isomorphism to the single complex of
  this quotient assert that it is an integral constructible sheaf in degree zero.
  `Mono (latticeScalar ... 1)` is injectivity of multiplication by ϖ on the quotient.
- The next isomorphism is K_E ≅ Q(M), the asserted rational lattice identification.
- For every n, the derived reduction of M is isomorphic to the degree-zero single
  complex of `scalarReductionExtension` of its quotient sheaf. Ordinary extension
  along the completed coefficient quotient is precisely M/ϖ^(n+1)M.
- For every n the fixed-coordinate `F : DerivedCategory.Plus ...` is identified with
  this intrinsic derived reduction by `sfIntrinsicDerivedEquivalence.inverse`.
  `FixedEtaleOriginWitness ... F` retains the actual pair of an etale antecedent
  and a comparison isomorphism. Existence is stated using `Nonempty` because the
  whole result is a proposition; its witness type contains both pieces of data.
- `S : TraceFormulaASystem T` has each level in the recorded ctf full subcategory,
  and its levels are identified with the derived reductions. `S.IsNormalized`
  concerns the adjoints of S's actual transitions. The family `eta` and displayed
  commuting equation identify its restricted adjacent transitions with the
  canonical `sfDerivedReductionTransition` of M. These are the quotient-induced
  transitions; an unrelated normalized system is insufficient.
- For every compactification c of the geometric structure map, the complex P has
  a finite interval outside which `IsZero (P.X i)`. Each term is both
  `Module.Free` and `Module.Finite` over the lifted valuation ring. This is the
  requested bounded finite-free representative, including the empty/zero case.
- `latticeModel P ≅ (latticeCompactSections c M).obj` identifies P with the
  recorded integral RΓ_c. `latticeModelReduction` applies the actual quotient
  scalar-extension functor to P termwise. Since P is bounded and free, this is
  its derived tensor with A_(n+1). Its comparison with `latticeFiniteCompactSections`
  states the displayed finite reduction comparison at every positive level.
- The final isomorphism, for every integer i, identifies rational H_c^i(K_E)
  with scalar extension of the homology module of P to E. `ModuleCat.uliftFunctor`
  and the quotient-free coefficient homomorphism through `ULift.ringEquiv`
  express the same modules in the universe required by the point-section API;
  no alternative coefficient ring or rational cohomology is used.

Dependency declarations read and used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `TraceFormulaCoefficientConventions`, `geometricBaseChange`, `structureMap`,
  `geometricFiniteType`, `geometricQuasiCompact`, `geometricSeparated`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalStandardClass`,
  `sfRationalHeartProperty` (the intersection of the recorded standard classes).
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the recorded completed
  coefficient construction and scalar action reexported by this module;
  `scalarReductionSource` is modules over that completion, not discrete O_E.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`.
- `Sheaf.Paper.TraceFormulaAdicSystem`: `TraceFormulaASystem`, `IsNormalized`,
  `restrictedObjects`, `restrictedStep`, `adicLevel`.
- `Sheaf.Paper.QcqsCompactSupportRealization`: the recorded compact-support
  realization, reexporting integral/rational compact-support values.
- `Sheaf.Paper.OrdinaryCompactCohomology`: `integralCompactSections`,
  `rationalCompactCohomology`, `finiteCompactSections`.
- `Sheaf.Paper.PointSectionsDerivedReduction`: `pointReductionQuotient`.
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`: `integralScalarChainAction`.
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`:
  `finiteRing_constructibleDerived_origin` and the intrinsic comparison coordinates.

Proof-only imports retain the recorded plan: `IntegralResidueTor`,
`IntegralStratifiedPerfectCharacterization`, `CompactSupportRepresentativeIndependence`,
and `ConstructibleTruncations`. The remaining proof dependency
`prop-trf-adic-coefficient-morphism-systems` has no Lean record, so there is no
module to import for it. It is used only in the natural-language proof, not as
an extra assumption or a replacement definition.

Edge cases checked: empty X; dimension zero; zero K_E with a nonzero power-torsion
integral representative; nonzero-degree torsion cohomology of K_O; nonzero torsion
in H⁰(K_O); and the first positive level. None is excluded. Even when D=0, e=0
is an allowed positive bound e+1. No characteristic-equal case is silently included:
T supplies l distinct from p. No disputed statement or source correction was needed.

Searches retained from the earlier attempt in `searches.jsonl`:

- LeanFinder: "torsion-free integral lattice constructible sheaf on curve perfect
  compact support derived reduction"; eight results about integral schemes/curves,
  none states this theorem.
- Loogle: "Module.Free, CategoryTheory.DerivedCategory"; no hits, reporting the
  latter identifier unknown. This does not supply an existing declaration.
- LeanSearch: "A constructible integral sheaf on a curve modulo its torsion is
  torsion free and has a perfect complex of compactly supported cohomology";
  returned module sheaf constructions and abelianity, no matching result.
- Mathlib grep via msearch: "integral.lattice|torsion.free.*constructible|
  compact.support.*finite.free"; one unrelated root-system file.
- Direct rg in upstream `WeilConjectures/`, `dag/lean_names_upstream.json`, and
  `lean/Sheaf/` for the item id, `exists_curve_integral_lattice`, `latticeScalar`,
  and `latticeQuotient`: no duplicate declaration; the separate
  `LatticeSheafLocallyConstant.latticeScalarMap` is a different notion.
  Earlier conceptual searches found `AdmissibleLattices.IntegralLattice`
  (legacy category) and `LatticeSheafLocallyConstant.IntegralLatticePair`
  (locally constant sheaves), neither the arbitrary curve statement here.

Validation: the prescribed scompile.py completed both sandbox and library-name
single-file checks cleanly on resumption. The former missing TraceFormulaAdicSystem
artifact no longer blocks compilation. The subsequent dry run is recorded below.
Prior interrupted-attempt reports remain in `scratchpad/report-prior-attempts.md`.

## Second reading by Q15

Self-check on resumption, with the current node, source Step 5 and complete module
open; no separate agent was launched, per the dispatcher's instruction. The
maintainer supplies the independent review. Matched every hypothesis and conjunct
as listed above, especially the non-Weil A-system, the completed coefficient
category, the positive-level index shift, and the ordinary versus derived reductions.
The stabilized-kernel condition is equivalent to the stated bounded torsion union,
not an additional finite-level hypothesis. The compact-support complex uses the
same geometric structure map and compactification at every coefficient level.
Found and repaired one omitted proof-only import: `ConstructibleTruncations`.
No declaration statement or node mathematical field was changed in this reading.
