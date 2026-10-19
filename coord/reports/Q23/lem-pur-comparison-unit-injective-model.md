## Worker report

`Sheaf.Paper.PurityComparisonUnitInjectiveModel` states
`AlgebraicGeometry.ProEtale.comparisonUnitInjectiveModel`, with `sorry` as its entire
proof. The natural-language proof in its docstring follows all five DAG proof
steps, including enough injectives, the derived Hom computation, resolution
independence, evaluation at the identity, and cancellation of the two isomorphisms.
No definition or additional theorem is introduced.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme is `T : Scheme.{u}`. The finite discrete commutative coefficient ring
  is `Λ : Type (u + 1)` with `[CommRing Λ] [Finite Λ] [TopologicalSpace Λ]
  `[DiscreteTopology Λ]`. In particular commutativity is explicit; it is not
  inferred from the more general finite-ring comparison framework.
- The etale category is `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  The pro-etale category is the recorded `FiniteCoefficientModules T Λ`.
  Its coefficient sheaf is the sheafified continuous-function ring of
  `def-weil-pbc-proetale-modules`; `finiteCoefficientRealization` identifies it
  canonically with the constant-coefficient module-sheaf encoding. Thus the
  statement uses the dependency's specified category and comparison functor.
- The ordinary adjunction is `finiteCoefficientComparisonAdjunction T Λ`, with
  inverse image `finiteCoefficientComparison T Λ` and direct image
  `finiteCoefficientDirectImage T Λ`. Its homotopy-category unit is exactly the
  homotopy class of the termwise complex unit `η⁰`.
- `M` and `J` are `CochainComplex.Plus` objects of the two categories: their
  complexes vanish in all sufficiently negative degrees, as the node requires.
  `j : (finiteCoefficientComparison T Λ).mapCochainComplexPlus.obj M ⟶ J`
  is an actual chain map in that full subcategory. `hj` says its underlying chain
  map `j.hom` is a quasi-isomorphism. `hJ` asserts injectivity of every `J.obj.X i`.
- `Q` is `DerivedCategory.Plus.Qh` after `HomotopyCategory.Plus.quotient`.
  Every occurrence of `Qj` is `Qh.map` of `quotient.map j`.
  `rightDerivedFunctorPlus` is the specified bounded-below derived direct image,
  and `rightDerivedFunctorPlusUnit.app (quotient.obj J)` is `α_J`.
- The first conjunct is invertibility of the derived direct image of `Qj`, using
  `mapDerivedCategoryPlusFactorsh.hom.app (quotient.obj M)` for the canonical
  exact-functor identification of the derived inverse image with `Q(ν* M)`.
  This factor is an isomorphism, so this is precisely the node's first asserted
  isomorphism, with the source expressed using the actual derived functor.
- The second conjunct is invertibility of `α_J`.
- The final equality is `ηᴰ ≫ Rν*(Qj) = Q(η⁰ ≫ ν*(j)) ≫ α_J` in Lean's
  left-to-right composition convention. Its right side applies `Qh` to the
  homotopy class of the ordinary composite complex map. Both sides have source
  `Q M` and target `Rν*(Q J)`. Together with the first two conjuncts it says that
  this map represents the derived unit under `α_J ≫ (Rν*(Qj))⁻¹`, exactly the
  final sentence of the node; no further hypothesis or choice of comparison is used.

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: the recorded upstream module
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` was read through
  `scompile.py --source`. Its documented encoding is
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, with Mathlib's
  `DerivedCategory.Plus` and `DerivedCategory.homologyFunctor`. The relevant
  category definitions are also available through the imported coefficient APIs;
  the torsion predicate is irrelevant to this node.
- `def-weil-pbc-proetale-modules`:
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, especially
  `FiniteCoefficientModules`, `finiteCoefficientRealization`,
  `finiteCoefficientComparison`, and their additive/exact/equivalence instances.
- `def-weil-pbc-site-comparison-morphism`:
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`. The realized module
  adjunction used here is its canonical transport through coefficient realization.
- `lem-sf-comparison-pullback-exact`: `Sheaf.Paper.ComparisonPullbackExact`,
  `AlgebraicGeometry.comparisonPullbackExact`. The finite-coefficient realization
  preserves exactness, supplying the termwise exact comparison used here.
- `lem-weil-pbc-right-derived-plus-injective` is a Mathlib leaf. Its `mathlib_match`
  already provides `CategoryTheory.Functor.rightDerivedFunctorPlus` and
  `rightDerivedFunctorPlusUnit`, their `IsRightDerivedFunctor` instance,
  `HomotopyCategory.Plus`'s injective-complex comparison-isomorphism instance in
  `DerivabilityStructureInjectives.lean`, and `Functor.rightDerivedUnique` with
  the compatibility/uniqueness laws. These signatures and docstrings were read.
  There is no need for a project `lean` record or a wrapper theorem for this leaf.
- `thm-weil-pbc-site-comparison`: the current recorded module
  `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit` is publicly imported.
  It reexports `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`, including
  `finiteCoefficientComparisonAdjunction`, `finiteCoefficientDirectImage`, and
  `finiteCoefficientDerivedComparisonAdjunction`. Its module documentation
  identifies the fixed-ring and realized-coefficient presentations; this statement
  uses the latter, as specified by `FiniteCoefficientModules`.
- The stated proof dependencies are available through the comparison imports;
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses` is explicitly
  imported for `prop-pur-kinjective-resolutions-exist`. No proof is supplied here.

Edge cases checked: the empty scheme imposes no nonemptiness requirement; the zero
ring is allowed by `CommRing`; `M = 0` and the zero injective resolution are included;
`j = 𝟙` when the inverse-image complex is already injective gives the standard
unit-normalization formula. There is no upper degree bound, no constructibility or
finite-generation condition on module sheaves, and no chosen resolution is fixed.
The coefficient and site universes are the existing dependency conventions.

Retained searches (the exact outputs remain in `searches.jsonl`):

- `msearch.py Q23 lem-pur-comparison-unit-injective-model leanfinder
  "injective resolution representative of derived adjunction unit"` returned
  eight injective-resolution/right-derived candidates, none for this comparison.
- `msearch.py ... loogle "CategoryTheory.Adjunction.derivedPlus_unit_app_fac"`
  returned no indexed hit. Direct source reading finds that declaration in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  it gives the generic unit normalization, not the full statement for arbitrary
  `j` with the two invertibility clauses.
- `msearch.py ... grep
  "comparisonUnitInjectiveModel|rightDerivedFunctorPlus_injectiveInterface"
  "Mathlib/CategoryTheory/Functor/Derived"` returned no hit.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and shared
  `lean/Sheaf` for `comparisonUnitInjectiveModel` and the node id found no existing
  declaration. Mathlib's right-derived source was read directly, confirming the
  existing exact match for the dependency instead of redeclaring it.

The node's natural statement and all its other fields are unchanged. No
`STATEMENT-DISPUTED` flag, statement correction, new node, or dependency module is
needed. `set_option autoImplicit false` is explicit. The delivered theorem has
only its named stage-2 `sorry`; its definitions all come from existing APIs.

## Second reading by Q23

Self-check in this dispatcher session; no additional agent was started. I opened
the node, the retained files, all statement-dependency records, their relevant
source declarations, and Stacks derived.tex at the two source lemmas. The saved
packet's dry run passed, but the reading found three concrete interface defects:

1. The added `rightDerivedFunctorPlus_injectiveInterface` used `True` instead of
   the compatibility equations and asserted uniqueness against unrestricted
   pairs. It did not state the dependency's universal property. The dependency
   already has a complete usable `mathlib_match`, so its redundant module, node
   copy, and import have been removed altogether. In particular the offending
   dependency-node file from the maintainer's return is absent from this packet.
2. `[Ring Λ]` silently covered noncommutative coefficients although this item's
   own statement assumes a commutative ring. It is now `[CommRing Λ]`.
3. The saved `j` was a homotopy morphism. It is now a chain map between bounded
   below complexes, with the quasi-isomorphism hypothesis on that map, and the
   formula explicitly passes it through the quotient functor.

I reread all three conclusion clauses with the revised file: the two
isomorphisms are explicit; the displayed equation has the correct orientation;
and cancellation gives the final representative identification. I expanded the
proof docstring to cover every DAG proof step and imported the current recorded
site-comparison module. The revised file passes `scompile.py` without errors or
unexpected warnings. The JSON signature is extracted verbatim from that file.

## Returned-delivery repair verification (2026-10-17)

The return on immutable head `91098ff29620` reports that the maintainer's
`--apply-fixes` directory contained the report at an unsupported nested path.
This delivery packages the retained substantive repairs directly as the worker
module, its node record, and the normal report; it requires no maintainer fix
packet. The obsolete dependency module and dependency-node copy remain absent.
The saved packet passed `deliver2.py --no-push` as commit `073f0a39f4`, including
server preflight and separate sandbox/library file compiles against the current
base. Compared with the shared main node, only `lean` changes.

The repair self-check reread the retained theorem and all six statement-dependency
records, the canonical realized adjunction definitions, the right-derived
comparison and injective-complex instance, and Stacks' two derived-adjunction
lemmas. The finite discrete commutative coefficients, bounded-below chain map,
quasi-isomorphism and termwise injectivity hypotheses match; the two IsIso
clauses and normalized unit equation match the conclusions, including the exact
left-derived-factor identification. The recorded signature agrees verbatim with
the file, every Lean line is at most 100 characters, and the sole postponed proof
is the named theorem. No further mathematical alteration was needed.
