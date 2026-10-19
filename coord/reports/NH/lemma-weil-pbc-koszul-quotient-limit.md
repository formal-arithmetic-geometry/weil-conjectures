## Worker report

The module `Sheaf.Paper.KoszulQuotientLimit` states
`AlgebraicGeometry.Scheme.koszulQuotientLimit`, with proof `sorry`.
There is no change to the informal statement and no new or repaired dependency node.

Hypothesis and conclusion correspondence:

- `X : Scheme.{t}` and `Λ : Type t` with `[CommRing Λ]` are the scheme and coefficient
  ring, on the recorded small pro-etale site, including its distinct site universes.
- `d : CompleteCoefficientDatum Λ` includes Noetherianity, a finitely generated ideal,
  additive torsion of Λ/I, and perfectness of every positive-power quotient. It adds
  neither adic completeness nor flatness of the quotients.
- `r : ℕ`, `f : Fin r → Λ`, and `hf : Ideal.span (Set.range f) = d.ideal` give exactly
  the finite generating list, including the empty list.
- The existential families range over every `K : proEtaleDerivedCategory X Λ` and every
  `M : AdicKFlatModel X Λ K`. Both towers use the identical `M.complex`; `M.isKFlat`
  and `M.realization` supply the recorded representative and its identification.
- `koszulTensor`, `koszulPowerSheaf`, and `koszulTensorTransition` use Q_(n+1) and its
  exterior transition. `adicReductionComplex` and `adicReductionComplexStep` use
  P_(n+1) and its quotient transition. Thus all and only positive levels occur.
- The family `v` is the strict tensor augmentation. Its first equation is the quotient
  on the degree-zero tensor unit. Its second equation vanishes on every other Koszul
  degree, expressed using `HomologicalComplex.ιMapBifunctor`. In Koszul degree zero
  the unit is an isomorphism onto that factor, so these formulas determine the entire
  tensor map, rather than an arbitrary augmentation. The third equation is its strict
  compatibility with the two recorded transitions.
- `w` acts by `Limits.Pi.map (v K M)` on both cone coordinates. Its first equation
  specifies the x coordinate (the mapping-cocone first projection); its second specifies
  the shifted y coordinate (the second projection cochain). These determine the map
  componentwise. They exclude a choice of an unspecified triangle filler.
- `c K M` is an isomorphism from the recorded `intrinsicKoszulCompletion` to the
  recorded `adicCompletionObject`, and its hom is exactly the localization of `w`.
  These explicit product cones compute the total derived strict inverse limit here,
  using exact countable products on the pro-etale site, rather than arbitrary choices
  of Roos triangles.
- The next equation is exactly κ_K followed by c_K equals comp_K, using the recorded
  `intrinsicKoszulCompletionUnit` and `adicCompletionMap`.
- The final clause expresses naturality on representatives. `g` is any map of models;
  `τ` is its tensor with the identity on Q; `σ` is its reduction, characterized by
  commuting with the quotient augmentation (which is degreewise epimorphic). `a` and
  `b` are the resulting cone maps, both coordinates explicitly fixed. The concluding
  equation is the naturality square after localization. Since flat-term K-flat
  resolutions exist, derived morphisms are represented by roofs between these models;
  the same squares for quasi-isomorphisms give descent and independence of models.
  In particular this includes maps representing identities and arbitrary derived arrows.

Dependency declarations read and used:

- `Sheaf.Paper.CompleteCoefficientDatum`: `CompleteCoefficientDatum`, `AdicKFlatModel`,
  `adicLocalization`, and the underlying `adicChange`/`adicRestrict` reduction model.
- `Sheaf.Paper.AdicDerivedInverseLimit`: `AdicDerivedInverseLimit` describes the
  product-cone triangle, supplied for the concrete model by CompletionMap.
- `Sheaf.Paper.CompletionMap`: `adicReductionComplex`, `adicReductionComplexStep`,
  `adicReductionAugmentation`, `adicReductionProductShift`, `adicCompletionComplex`,
  `adicCompletionProjection`, `adicCompletionObject`, `adicCompletionMap`.
- `Sheaf.Paper.IntrinsicKoszulCompletion`: `koszulPowerSheaf`, `koszulTensor`,
  `koszulTensorUnit`, `koszulTensorTransition`, `koszulOneSubShift`,
  `koszulCompletionComplex`, `intrinsicKoszulCompletion`, `intrinsicKoszulCompletionUnit`.
- `Sheaf.Algebra.Homology.DerivedTensor`: `derivedTensor` supplies the shared total
  tensor convention, implemented in the Koszul and coefficient model dependencies.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`:
  `CategoryTheory.ringedStrictTowerHomotopyLimit` is imported for the proof plan;
  `Sheaf.RingTheory.NoetherianKoszulAugmentationProZero` supplies
  `ExteriorAlgebra.noetherian_koszul_augmentation_pro_zero`.
- Other stated proof dependencies are imported, including the canonical ringed-topoi
  tensor comparison and K-flat resolution modules; the two sheafification leaves are
  Mathlib interfaces in the corresponding imports.

Edge cases checked: r=0 gives I=0 and identity coefficient towers; the zero coefficient
ring and the zero derived object remain allowed; I=Λ yields zero quotients and a
pro-zero Koszul completion; no boundedness or regular-sequence assumption is imposed.
All positive powers are covered by n+1. The empty scheme is allowed.

Searches (2026-10-15): `msearch.py leanfinder` with “Koszul completion quotient tower
derived inverse limit natural isomorphism” returned ordinary AdicCompletion algebra
isomorphisms and Kaehler differentials, no exact match. `msearch.py loogle` with
“AdicCompletion, CochainComplex.mappingCocone” returned zero hits. `msearch.py grep`
with “koszul.*completion|Koszul.*quotient.*limit” returned zero hits. Direct `rg` in
WeilConjectures and lean/Sheaf for the comparison name and quotient-limit patterns,
and for the blueprint id in WeilConjectures, found no existing comparison. Broader
project/DAG searches found the already recorded intrinsic completion, quotient
completion, and Noetherian augmentation nodes; these are used, not duplicated.

The blueprint unit source and the full node proof were read. The proof docstring
records all four steps, including the direct I-power augmentation, exact constant
sheafification, K-flat tensor-cone sign, strict derived-limit criterion, naturality,
and the unit equation. No statement fault or mathematical dispute was found.

## Second reading by NH

I reread the node statement, its blueprint source place (proper-base-change, order 1259), and the complete Lean signature.
The correspondence is as follows.

- The node's (X,\Lambda,I=(f_1,\ldots,f_r),K) are rendered by `X : Scheme.{t}`, `Λ : Type t`,
  `[CommRing Λ]`, `d : CompleteCoefficientDatum Λ`, `r : ℕ`, `f : Fin r → Λ`,
  `hf : Ideal.span (Set.range f) = d.ideal`; `K` is quantified through each `v`, `w`, and `c`
  over `proEtaleDerivedCategory X Λ`, with `M : AdicKFlatModel X Λ K`.
- The positive quotient and Koszul towers are rendered by `adicReductionComplex ... n` and
  `koszulTensor ... n`; their strict maps are `v`, with the degree-zero unit equation,
  vanishing on every nonzero Koszul degree, and the transition equation all present.
- The strict cone comparison is rendered by `w`; both mapping-cocone coordinates are fixed by
  the displayed `fst` and `snd` equations, so it is not an unspecified filler.
- The natural isomorphism is `c ... : intrinsicKoszulCompletion ... ≅ adicCompletionObject ...`;
  its hom is required to equal `(adicLocalization X Λ).map (w K M)`.
- The unit identity is exactly the displayed equation between
  `intrinsicKoszulCompletionUnit ≫ (c K M).hom` and `adicCompletionMap`.
- The final quantified block gives representative naturality: `g`, `τ`, `σ`, `a`, and `b` are
  introduced explicitly, their tensor/augmentation/projection coordinate equations are imposed,
  and the localized naturality square is the conclusion.

No hypothesis is added: there is no flatness or boundedness assumption on `K` or quotient modules,
no regular-sequence condition, and the site universes remain `Scheme.{t}` with sheaf coefficients
in universe `t + 1`. The quantifier order in the Lean signature agrees with the node's families.

Edge cases checked: `r = 0` is allowed (`Fin 0` and `I = 0`); zero rings and zero derived objects
remain admitted; `I = ⊤` gives zero quotient towers; all levels are positive via the `n + 1`
conventions in the dependency constructions; and the empty scheme is not excluded.

I searched Mathlib and the project/source tree with LeanFinder/Loogle/grep queries for Koszul
completion quotient towers, product-cone derived limits, and the blueprint identifier. These found
only unrelated adic-completion, filtration, or Koszul-connection declarations and no existing
statement. The dependency declarations listed by the worker were opened and match the uses in the
module. No mismatch was found, so no source or node change was necessary.

The module compiled cleanly with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NH lemma-weil-pbc-koszul-quotient-limit lean/Sheaf/Paper/KoszulQuotientLimit.lean`.
