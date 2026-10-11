## Worker report

The delivery defines finite-coefficient lisse module sheaves, integral adic systems,
rational sheaves, coefficient extension, algebraic-coefficient sheaves, their geometric
fibres, tensor products, and units in `Sheaf.Paper.LisseAdicSheaves`. It supplies the
otherwise unnamed finite-intermediate-field indexing type in a dependency module.
Definitions contain real data. Construction-law proofs are separately named theorems
with `sorry`, complete source/proof docstrings, and are listed in their owning node's
`lean.declarations`; nothing is proved in this stage.

Hypotheses and clauses:

- `l : ℕ` and `[Fact l.Prime]` express the prime. `Y : Scheme.{u}` expresses the scheme.
  `[IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]`
  express the standing source hypotheses, restored in the corrected statement.
  A geometric point is `y : Spec (.of Ω) ⟶ Y`, `[Field Ω] [IsAlgClosed Ω]`.
- `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` express a finite coefficient
  extension. `[Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]` expresses the fixed
  algebraic closure. `Padic.FiniteCoefficientFields l K` is exactly the finite
  intermediate fields; their compositum is the lattice supremum.
- The preliminary finite-ring clause is `LisseFiniteModuleSheaf Y A`, with `[Ring A]`
  and `[Finite A]`, the full subcategory defined by the source's
  `IsFiniteLocallyConstantSheaf`. Its local trivializations are constant *module*
  sheaves, not merely constant underlying sets. Over a finite ring finite generation
  of the stalk module is equivalent to finiteness of its underlying set.
- Clause 1: `AdicIntegralDiagram` is a functor from `ℕᵒᵖ`, with index `n` representing
  the paper's `n+1`. Its levels are `𝒪_E`-module sheaves killed by `ϖ_E^(n+1)`, hence
  exactly `A_{E,n+1}`-module sheaves by restriction of scalars. The first conjunct of
  `IsLisseIntegralDiagram` requires lissity at every level. The second requires the
  annihilator. The last conjunct says on every geometric stalk that each transition
  is surjective and its kernel is `ϖ_E^(n+1)` times the source module. This is exactly
  the reduction tensor isomorphism: quotient by that submodule is tensor with
  `A_{E,n+1}`. Geometric stalks are exact and conservative, so the stalk formulation
  is equivalent to the sheaf condition. `LisseIntegralSheaf` is the full subcategory,
  and its morphisms are natural transformations, exactly coefficient-linear compatible
  families. `lisseIntegralFiber` is the categorical inverse limit of the same stalks.
- Clause 2: `LisseRationalSheaf.integral` keeps the integral object as its model.
  `lisseRationalHom` is `E ⊗_{𝒪_E} Hom(F,G)` (the symmetric tensor order of the node).
  `LisseRationalComposition.comp_tmul` prescribes `(a⊗f,b⊗g) ↦ ab⊗(f≫g)`;
  its law fields give the category instance. `lisseRationalFiber` is precisely the
  tensor of the integral fibre with E. Torsion integral objects are retained as models,
  as required; they become zero objects up to rational isomorphism.
- Clause 3: `lisseIntegerInclusion` is uniquely characterized by its field inclusion.
  `lisseRamificationIndex` is the positive exponent carrying the source maximal ideal
  to a power of the target maximal ideal. `lisseScalarSourceIndex` implements the
  zero-based index `ceil((m+1)/e)-1`. `lisseIntegralScalarLevel` sheafifies balanced
  extension to `A_{L,m+1}` and restricts to `𝒪_L`. Tensoring from `𝒪_E` agrees with
  tensoring from `A_{E,n}` because both the source annihilator and its image vanish.
  `LisseIntegralScalarExtensionData.levelIso` fixes these levels. Its `transition` and
  `map` fields explicitly prescribe the source/coefficient transition maps and the
  action on morphisms on pure tensor sections, including sheafification. Thus these
  are induced maps, not arbitrary ones. The rational extension data prescribe the
  additive map by `a⊗f ↦ ι(a)⊗S(f)`, with identity and composition laws; the resulting
  functor has the specified integral-model object map.
- Clause 4: `LisseCoefficientDiagramData` specifies the pseudofunctor with precisely
  those rational categories and inclusion functors. `LisseCoefficientPairs` is its
  Grothendieck category of pairs `(E,F)`. `lisseCoefficientCocartesian` picks the arrows
  consisting of scalar extension followed by an isomorphism. `LisseAlgebraicSheaf`
  localizes at these arrows, the standard concrete 2-colimit construction. Localization
  preserves objects as type synonyms, so `lisseAlgebraicPair` recovers the actual pair,
  not a freely chosen representative. For a directed poset this localization's Hom
  is the indicated filtered colimit of common-field Hom: push the finitely many
  coefficient changes in a zigzag to a common upper field; equality is equality after
  a further extension, using the pseudofunctor constraints. `lisseAlgebraicFiber` is
  `K ⊗_E F_y`, with the chosen pair's field algebra structure.
- Clause 5: `lisseIntegralTensor` uses the pointwise monoidal product of diagrams of
  module sheaves, hence the sheaf tensor at each level with tensor transition maps.
  Because the factors are killed by the quotient ideal, tensor over `𝒪_E` is tensor
  over `A_{E,n}`. `lisseRationalTensor` rationalizes this product. The algebraic product
  in `lisseAlgebraicTensor` extends both models to their compositum and tensors there.
  `lisseIntegralUnitDiagram` is the constant sheaf of each coefficient quotient with
  quotient factor maps; `lisseIntegralUnit`, `lisseRationalUnit`, and
  `lisseAlgebraicUnit` are the units at all three stages.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Sheaf.AlgebraicGeometry.EtaleSheaves` records both supported coefficient encodings;
  the source's module-valued encoding `Sheaf Y.smallEtaleTopology (ModuleCat R)` is used,
  as its record explicitly permits. `WeilConjectures.ConstructibleSheaf.Defs` supplies
  `IsLocallyConstantSheaf`, `LocallyConstantDatum`, and `IsFiniteLocallyConstantSheaf`.
  The existing `def-constructible-locally-constant` node is added as a dependency.
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `GrothendieckTopology.Point.sheafFiber`;
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Scheme.pointSmallEtale`. Points are
  lifted to the coefficient universe using the existing source's `Point.ulift`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` / `Basic`: `IsAlgClosure`, `IsAlgClosed`.
- `Sheaf.NumberTheory.Padics.CoefficientExtension`: `coefficientExtensionIntegers`,
  `coefficientExtensionMaximalIdeal`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, `coefficientExtensionRing`, `coefficientExtensionTransition`.
- The directed-set dependency's recorded `IntermediateField.finiteDimensional_sup` is
  used to build its compositum; see the dependency-module explanation below.
- `Sheaf.Algebra.Category.ModuleCat.RingScalarExtension`: `Sheaf.ringExtendScalars`,
  `ModuleCat.ringExtendScalars`, `ModuleCat.ringExtensionTmul`; its landed node
  `def-pod-ring-scalar-extension` is added as a dependency, rather than copying it.
- The general constructions of tensor products, diagram limits, Grothendieck
  constructions, pseudofunctors and category localization are Mathlib's definitions.

Edge cases checked: positive level one is represented by index zero, with no accidental
zero-ring first level. Torsion and zero systems are included, no freeness hypothesis is
added. Ramification index is strictly positive; e=1 gives identical source/target levels,
and larger e gives a nondecreasing possibly repeating source index. Equal fields and
non-nested coefficient fields are allowed; the compositum handles the latter. An empty
scheme is not excluded by the category definitions (only fibres require a geometric
point). Disconnected schemes remain allowed; a Noetherian scheme has finitely many
connected components, so global integral models and a common finite coefficient field
agree with the source's locally-modelled lisse categories. Coefficient-module and scheme
universes are explicit, and geometric stalks use the established universe lift.

Searches: LeanFinder query “lisse l-adic sheaf integral inverse system rational coefficient
scalar extension” returned condensed/light-profinite sheaf constructions and Witt vectors,
not adic systems. Loogle `CategoryTheory.Sheaf, ModuleCat` returned sheaves-of-modules
forgetful/evaluation declarations, not this notion. Mathlib grep `Lisse|lisse|ellAdicSheaf`
in AlgebraicGeometry returned only the constant `Scheme.ellAdicSheaf` used for pro-étale
cohomology. Source and project rg searches for lisse and the item ID found constructible
finite-level predicates and Weil sheaves, no integral/rational/algebraic adic-system
category matching these clauses. Earlier worker's recorded LeanSearch request returned
“Internal Server Error”; all searches are retained in sandbox `searches.jsonl`.
The finite-field dependency was searched through its existing node's Mathlib match and
read in full: the compositum instance alone is not the whole indexing notion.

## Dependency modules

`def-weil-finite-subextension-directed-set` gets
`Sheaf.NumberTheory.Padics.FiniteCoefficientFields`. Its old match is
`IntermediateField.finiteDimensional_sup`, merely an instance proving the compositum
finite; no named type, base field, exhaustion clause or finite-inclusion assertion is
supplied by that declaration. The module defines the exact finite intermediate-field
subtype, its compositum, its base field and finiteness instance, and states the three
remaining properties with the natural-language argument in the theorem docstring.
The node changes only in `lean`, with the required explanatory note.

## Statement corrected

The old statement began “Let Y be a scheme with a geometric point” and did not include
Weil II's standing convention. Reading (0.1), p. 144 of the source PDF confirms that
schemes throughout are Noetherian and separated with ℓ invertible. These hypotheses are
now stated explicitly, not silently imposed by the Lean module. The five constructions
and all their formulas remain those of the original node. Two existing definition-node
citations are appended for the module local-constancy and balanced scalar extension
actually used in Lean. `statement_change.old_statement` preserves the old statement
verbatim, and `old_stmt_deps` preserves the former dependency list.

The sole citer is `cor-galois-lisse-representations`, marked `holds: false`: its adic part
uses the same objects and formulas but presently quantifies over an unrestricted
connected scheme. Its binder must receive the source's standing hypotheses before it
can apply this source-scoped definition. The citer is not edited in this delivery.

## Second reading by G1

I independently read the corrected node before its Lean, then read both delivery modules
in full, the eight dependency records and the relevant dependency declarations. The
source here is Deligne, Weil II, rather than a Stacks definition: I read the sandbox
PDF, printed pp. 144 and 146–147, (0.1), (0.3), (1.1.1) a)–d). The correction is
source-faithful: (0.1) explicitly fixes a prime and restricts to Noetherian separated
schemes with that prime invertible. The constructions below do not introduce another
restriction. The following is my object/hypothesis/clause checklist.

- Prime and base scheme: `l : ℕ`, `[Fact l.Prime]`, `Y : Scheme.{u}` and the three
  instance binders on `LisseIntegralSheaf` give precisely the corrected scope.
  Invertibility in each residue field means that no residue characteristic equals l;
  it is equivalent to invertibility of l on Y. Verdict: matches.
- Coefficients: `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` is the finite
  extension. Its integers, uniformizer, quotient ideal/rings and quotient transitions
  are the recorded `Padic.coefficientExtension*` declarations, whose actual definitions
  I read. `[IsAlgClosure ℚ_[l] K]` and `Padic.FiniteCoefficientFields l K` give the fixed
  closure and its finite intermediate fields in clause 4. Abstract finite E in the
  earlier constructions also covers every intermediate field, without requiring an
  unnecessary chosen embedding there. Verdict: matches.
- Geometric point: `[Field Ω] [IsAlgClosed Ω]`, `y : Spec (.of Ω) ⟶ Y` is (0.3)'s
  point. `pointSmallEtale` indexes lifts to étale neighbourhoods; `sheafFiber` takes
  their colimit. The source `Point.ulift` preserves that fibre up to its canonical
  comparison, while admitting module coefficients in `Type (u+1)`. Verdict: matches.
- Preliminary finite-ring notion: `LisseFiniteModuleSheaf Y A` is the full subcategory
  of module-valued sheaves satisfying `IsFiniteLocallyConstantSheaf`. I read
  `LocallyConstantDatum`, `IsLocallyConstantSheaf`, `IsFiniteSheaf` and that class:
  constants are constants in ModuleCat, and the finite condition is finite generation
  of geometric stalk modules. Over finite A this is finite underlying cardinality.
  The dependency record explicitly permits the module-valued encoding alongside
  modules over a constant ring sheaf. Noncommutative finite rings are allowed here.
  Verdict: matches, with no second local-constancy predicate.
- Clause 1, levels: `AdicIntegralDiagram` is indexed by `ℕᵒᵖ`; index n denotes the
  source's positive level n+1. `IsLisseIntegralDiagram` requires finite local constancy
  and sectionwise annihilation by the specified uniformizer power. This is the same
  quotient-ring module structure, via restriction of scalars. Verdict: matches.
- Clause 1, transitions: the consecutive map on every geometric stalk is surjective
  with kernel exactly the image of multiplication by that power. Thus its induced map
  from the quotient, equivalently the reduction tensor, is an isomorphism. Geometric
  stalks are exact and conservative; algebraically closed residue-field closures in
  the scheme universe suffice for this test. Consecutive comparisons imply all larger
  reductions. Natural transformations are exactly the compatible linear families.
  `lisseIntegralFiber` takes the limit of those same stalks. Verdict: matches.
- Clause 2: `LisseRationalSheaf.integral` retains exactly an integral model, and
  `lisseRationalHom` is the source Hom tensor E with the two factors exchanged by
  tensor symmetry. The composition structure specifies the pure-tensor composition,
  including identity and associativity, and the category uses that composition.
  `lisseRationalFiber` rationalizes the integral limit. Verdict: matches; no torsion
  models or nonfree modules have been discarded.
- Clause 3: `ι : E →ₐ[ℚ_[l]] L` is a field inclusion; the integer-ring restriction is
  characterized by equality after coercion into L. The positive maximal-ideal exponent
  is the ramification index. `lisseScalarSourceIndex m` equals
  ceil((m+1)/e)-1, and `lisseIntegralScalarLevel` is the prescribed balanced extension
  at that source level, sheafified and restricted to the target integer ring. Tensoring
  over the integer ring agrees with tensoring over the source quotient since its
  annihilator maps to zero. `levelIso`, `transition`, and `map` prescribe levels,
  transitions and morphisms on sheafified pure tensors. These generators determine
  the sheaf maps locally, so the functor is not unspecified scalar-extension data.
  The rational map is additive with the prescribed coefficient/pure-tensor formula.
  Verdict: matches both functoriality and the displayed object formula.
- Clause 4: the pseudofunctor values and arrows are explicitly constrained to these
  rational categories and these inclusion functors. Grothendieck objects are pairs;
  localization changes morphisms while retaining the pair objects. Inverting the
  arrows with invertible fibre map is precisely the directed 2-colimit: a finite
  zigzag can be pushed to a common finite upper field, and two such representatives
  agree exactly after a further extension. Its Hom therefore is the node's filtered
  common-field Hom colimit, rather than Hom in the unlocalized pair category.
  `lisseAlgebraicPair` retrieves the actual object pair and `lisseAlgebraicFiber` is
  K tensor its rational fibre over that pair's field. Verdict: matches.
- Clause 5: the integral tensor is the pointwise module-sheaf tensor of diagrams;
  both factors are annihilated by the quotient ideal, so this is the quotient-ring
  tensor with tensor transitions. Rational tensor uses the integral models; algebraic
  tensor extends to the compositum and tensors there. The unit diagram is the
  constant coefficient quotient at each positive level, with quotient factor maps;
  the other units use its rationalization and its base-field pair. Verdict: matches.

Dependency-module reading: there are no new definition nodes. The existing
`def-weil-finite-subextension-directed-set` gets only a `lean` change. Its module uses
exactly the subtype of finite intermediate fields, the lattice supremum for compositum,
and bottom for the base field. `finiteCoefficientFields_properties` states directedness,
exhaustion and finiteness of an inclusion, with the source's arguments in its docstring.
The old `finiteDimensional_sup` instance proves only one ingredient, not this full
notion. Its implementation was opened in Mathlib and is reused, not replaced. The
node's cited blueprint extraction is not present on this machine; Weil II (0.2) and
(1.1.1) d) were read directly and supply the same finite coefficient indexing notion.

Edge cases: index zero is positive level one, not the zero quotient; e=1 gives m itself,
and e>1 permits repeated source indices with coefficient reduction. The ramification
existence statement requires e>0. Zero and torsion systems, empty schemes and
nonconnected Noetherian schemes are allowed, with no freeness or connectedness binder.
The geometric-point-dependent fibre declarations alone require a point. The finite
coefficient index cannot be empty because bottom is included; distinct nonnested fields
have their finite compositum. The preliminary finite ring may be the zero ring. No
residue characteristic equal to l is admitted by the source's explicit convention.
The declared universe u is arbitrary, coefficient/module universes are u+1, and the
geometric stalk universe lift is the source's established one. Larger inputs can be
placed in a larger ambient scheme universe; no finite cardinality bound is imposed.

Independent searches: LeanFinder query “projective systems locally constant finite
module sheaves adic coefficients” returned adic-completion/profinite/condensed
constructions, none of these categories. Loogle `IntermediateField, FiniteDimensional`
returned general intermediate-field finiteness lemmas, not the full fixed-closure
indexing notion. I ran rg for `Lisse|lisse|AdicSheaf|adicSheaf` over Mathlib's
AlgebraicGeometry, the source and project, and for
`FiniteCoefficientFields|FiniteSubextension|FinExt|finExt|finiteDimensional_sup` over
the source, project and Mathlib intermediate fields. I opened Mathlib's `ellAdicSheaf`:
it is a pro-étale continuous-function coefficient sheaf, not this category. The project's
`LisseModuleSheaves` and `LisseTensorScalarExtension` concern the finite-level predicate
and its operations, already reused here. I also opened the source's
`AlgebraicGeometry.Scheme.FiniteEtale.FiniteSubfield` in HomotopyExactSequence: it fixes
`AlgebraicClosure K` specifically, unlike this node's arbitrary fixed closure; its
instances and adjoin lemmas do not provide that generalized notion. This is not an
exact existing match. Search calls are retained by msearch in searches.jsonl.

Correction/citers: the only actual statement/proof citer is
`cor-galois-lisse-representations`; I opened its statement and dependency arrays.
Its adic part has an unrestricted connected-scheme binder, so `holds: false` is correct.
There is no second citer to open. The correction changes no unit statement or target.

Mismatches and repairs: both module headers lacked the required main-definition lists;
I added them. The main node's stored signature flattened the line break in the source;
I replaced it with the signature's verbatim two-line text. I found no mathematical
statement mismatch requiring another correction, and left the definitions unchanged.
Every deferred law is a named theorem with a source and stepwise natural-language
proof; each theorem proof is `sorry`, while the constructions use explicit data or
witnesses of these specified construction theorems. No unbound variable or universe
remains. The two modules compiled together cleanly via scompile (13.6 seconds), before
these documentation/record-only repairs; delivery repeats the combined check.
