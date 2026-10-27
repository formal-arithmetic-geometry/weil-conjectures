## Worker report

The module `Sheaf.RingTheory.CotangentSheafModel` states
`Algebra.CotangentSheaf.exists_model`. The sole postponed proof is this theorem.
Its auxiliary definitions and specification records expand the constructions in
this node's own statement; no object is selected from the existence theorem.
The mathematical node statement is unchanged.

Clause-by-clause correspondence:

- A homomorphism of commutative rings is `f : Arrow CommRingCat.{u}`. Its
  source, target and homomorphism are `f.left`, `f.right` and `f.hom`.
- The common infinite variable bound is `κ : Type u` with `[Infinite κ]`.
  `ContainsRings κ f` expresses the stipulated bound on the rings. For any
  collection of rings and resolutions one first enlarges this bound, exactly
  as the node requires. This is not an algebraic finiteness assumption.
- `Presentation f κ` consists of a subset of κ and the images of its variables
  in B. `presentationObject` is the actual polynomial A-algebra and its
  evaluation augmentation. `Presentations` is the induced category in the
  over category of commutative A-algebras over B. Thus its maps are ALL
  A-algebra maps commuting with augmentations, and no object is required to
  surject onto B. It is small, with both objects and morphisms in u. This
  concrete small presentation model is equivalent to a small skeleton of
  polynomial algebras within the bound; the extra polynomial coordinates
  supply representatives, not a restriction on morphisms.
- The site in the node is `(Presentations f κ)ᵒᵖ` with topology ⊥, precisely the
  identity-cover topology used by `CategoryColimitBarSystem.models`.
  `rings`, `base` and `augmentation` give O(P)=P, its A-structure, and its
  augmentation to B. The naturality is inherited from the over category.
- `coefficientTerm p` is Mathlib's extension of scalars applied to
  `CommRingCat.KaehlerDifferential (base p)`, namely B ⊗_P Ω[P/A]. Symmetry
  identifies this with the tensor order Ω[P/A] ⊗_P B in the node.
  `Coefficients` provides its functor with term identifications and the exact
  restriction formula on the spanning elements `generator p b x = b ⊗ dx`.
  `presheaf` writes it on the opposite site. Identity-cover module sheaves
  are identified with module presheaves using the bar dependency's recorded
  `CategoryColimitPoint.modules`, which uses `ringedSiteModules`.
- `lowerShriek S f κ` is exactly degree-zero embedding followed by the
  bar dependency's total derived colimit. Its bar models, triangulated
  structure, adjunction and canonical generator normalization are those of S,
  rather than a second definition of a derived functor.
- Polynomial resolutions are the dependency's
  `CotangentResolution.IsPolynomialResolution`, including degreewise
  polynomiality, surjectivity and the augmentation quasi-isomorphism.
  `FitsBound` spells out the stipulated variable bound. `ResolutionLift`
  transports such a resolution into the chosen presentation category, with
  its underlying ring diagram, A-structure and augmentation explicitly
  identified. `Model.lift` asserts these transports for every resolution
  within the bound. `Model.standardFits` includes the standard resolution.
- `evaluation` is precisely s(F(P_•)): precomposition, the dependency's
  `negativeComplex`, and no positive cohomological terms. `Model.comparison` supplies `ResolutionComparison.iso`,
  a natural ISOMORPHISM of functors from ALL module presheaves to D(B).
  There is no flatness or exactness hypothesis on F. `natural_resolution`
  is naturality in every map of augmented resolution diagrams. All maps of
  the resolutions transport to such maps by the induced full category.
- To specify CANONICAL comparisons, `ResolutionComparison.augmentation` and
  `augmentation_formula` use the ordinary colimit cocone in degree zero;
  `IsNormalized` and `normalization` identify it with S's universal left-derived comparison.
  `ResolutionComparison.exact`, `PreservesBoundary` and `boundary` assert compatibility with connecting
  morphisms. Thus these are the normalized derived homological functor
  comparisons, not an uncharacterized choice of an isomorphism.
- `Model.differentialIso` and `differential_formula` identify evaluation on
  the differential presheaf with the dependency's differential complex on
  every generator in every degree. `theta` is evaluation on the standard
  resolution followed by this identified differential complex. Its target
  is exactly `CotangentResolution.cotangentComplex C f`, in D(B).
  `Model.agrees` says that every polynomial-resolution comparison is the
  recorded `C.comparison`, not an independently chosen comparison.
- A completely arbitrary commutative square is `q : f ⟶ g` in the arrow
  category. `q.left` and `q.right` are a and b and arrow-category morphisms
  include precisely the commutative-square identity. There is no
  injectivity, flatness, surjectivity, or base-change-isomorphism condition.
- `BaseChange.functor` is u before taking opposites. `objects` specifies
  A'[E] with augmentation e ↦ b(ε(e)); this is the canonical polynomial
  identification of P ⊗_A A'. `insertion_formula` specifies the map p ↦ p ⊗ 1
  as coefficientwise `MvPolynomial.map a`. Naturality of this insertion and
  A'-linearity of all target morphisms determine the functor on all maps.
- `BaseChange.coefficientMap` is the b-semilinear natural transformation t.
  `formula` is precisely b₀ ⊗ dp ↦ b(b₀) ⊗ d(p ⊗ 1), the symmetric tensor
  version of the node's dp ⊗ r formula. `barCoefficientMap` changes only
  opposite-category notation.
- `sheafMap` is T from S's bar-chain map, with S's canonical model
  identifications and the existing exact scalar-restriction localization
  comparison. It is therefore the SPECIFIED bar map, not an arbitrary
  morphism. The final equation in `exists_model` is exactly
  theta_(B'/A') T = f_std_(a,b) theta_(B/A), with composition in Lean's
  diagrammatic order and target objects restricted along b.

The theorem quantifies over the already recorded coherence C and bar system S,
and asserts simultaneous existence of the specified sheaf models and base-change
constructions. These are conclusions, not hypotheses assuming the item.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Augmentation`, `IsPolynomialResolution`,
  `negativeComplex`, `Coherence`, `differentialComplex`, `complexGenerator`,
  `cotangentComplex`, `cotangentMap`. The full signatures and docstrings
  were read, including the standard-resolution and tensor-generator laws.
- `Sheaf.CategoryTheory.DerivedColimitBar`:
  `CategoryTheory.CategoryColimitBarSystem`, `CategoryColimitBarModel`,
  `CategoryColimitPoint`, and the fields `derived`, `comparison`, `model`,
  `map`, `formula`, `singleExact`. The canonical bar comparison and
  generator formulas are retained verbatim through these interfaces.
- `Mathlib.RingTheory.Kaehler.Basic` and
  `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic`:
  `KaehlerDifferential`, `KaehlerDifferential.D`, its universal-property
  equivalence, `CommRingCat.KaehlerDifferential`, and its universal d/map.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`;
  used through the bar dependency's point-to-presheaf equivalence.
- `def-weil-size-convention` is metatheoretic, as its record says; u, κ,
  small presentation categories and the derived localization universe make
  it explicit here. No private universe or derived-category copy is used.
- Proof imports: `Sheaf.AlgebraicTopology.SurjectiveQuasiIsoTrivialKan` and
  `Sheaf.Paper.TrivialKanHomotopyEquivalence`. The general simplicial
  derived-colimit-computation node has no declaration yet, so no import
  exists to add. The recorded `Sheaf.AlgebraicTopology.TrivialKanFibration`
  module is absent both locally and via `scompile.py --source`; its exact
  boundary-lifting notion is already available through the imported
  Mathlib `SSet.modelCategoryQuillen.I.rlp`. No statement uses the stale name.

Edge cases checked: the zero ring and zero coefficient module; empty variable
sets (the presentation A → B exists without a surjectivity condition); infinite
variable sets within κ; n=0 and zero positive terms; the identity ring square;
noninjective and nonflat ring maps; maps into or out of zero rings whenever a
unital square exists. The argument never requires the base-changed standard
resolution to resolve B'. Presheaves are arbitrary. Double opposites are handled
by Mathlib's `opOp`/`unopUnop`, with no alteration of arrow direction.

Searches (2026-10-22; the wrapper also records these in searches.jsonl):

- msearch leanfinder: "cotangent complex as derived colimit of Kahler
  differentials over polynomial presentations, natural comparison for arbitrary
  ring squares". Eight hits, including `Algebra.Extension.cotangentComplex`,
  `CotangentSpace.map_cotangentComplex`, `Algebra.H1Cotangent.map`, and
  presentation differential relations. Reading Extension/Cotangent/Basic
  confirms these concern the naive two-term presentation complex, not this
  full simplicial derived-colimit comparison.
- msearch loogle: "KaehlerDifferential, DerivedCategory". Zero hits.
- msearch grep: "cotangent|Cotangent" in RingTheory/Extension. Twenty-five
  returned hits, again naive cotangent constructions, not the requested theorem.
- rg on `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for CotangentSheaf and cotangent-sheaf-model:
  no existing declaration; only the downstream transitivity proof mentions
  the node. A broader polynomial-presentation search found unrelated
  presentation and blowup modules. The inherited polynomial, over-category,
  induced-category, differential, tensor and derived-category constructions
  are all Mathlib or the recorded dependencies, reused here.

No new independent definition nodes, dependency repairs, or statement corrections.
All auxiliary constructions belong to the explicitly introduced sheaf model,
resolution comparison or ring-square map in this node's own statement.

## Second reading by Q37

Single-worker rereading only; the independent maintainer review is still required.
The correspondence above was checked against the complete node and source
cotangent.tex at 08PS, 08PT, 08PU, 08QI and 08QL. In particular, arbitrary
presheaves and arbitrary ring squares are quantified, the comparison is in the
derived category, the coefficient and bar maps have their prescribed formulas,
and the comparison with C's canonical resolution maps is an explicit equation.
The small category uses redundant representatives rather than a literally
skeletal type; full morphisms and transport of resolutions preserve the specified
site and its canonical maps. No mathematical change to the node is needed.

Compilation diagnosis: the large comparison structure was expensive for Lean to
check. Naming its normalization and boundary predicates and packaging one
resolution comparison separately removes that repeated reduction. All definitions
remain in one file, with the same mathematical clauses and default time limit.
