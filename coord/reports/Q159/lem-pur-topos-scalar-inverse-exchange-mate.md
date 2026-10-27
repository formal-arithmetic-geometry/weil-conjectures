## Worker report

Stage 2, Q159, `lem-pur-topos-scalar-inverse-exchange-mate`.
The delivery states scalar compatibility of inverse-image exchange and its specified
inverse-exchange open adjunct on arbitrary presented Grothendieck topoi. Its module is
`Sheaf.CategoryTheory.ToposScalarInverseExchangeMate`; its namespace is
`CategoryTheory.ToposScalarInverseExchange`. The only postponed proof is the theorem
`scalar_inverse_exchange_mate`. All helper definitions have complete data. No theorem
is proved. The accepted seven-step split and the mathematical statement are retained.

The inherited unchanged-item rejection was a stage-1 handoff issue. The current
`coord/brief-stage2.md` §0 explicitly distinguishes this stage-2 assignment. At the start
of this continuation the sandbox contained a draft module and search log, but no node
copy, report, or completed delivery. No push was repeated on an unverified result.

The records in this module package the actual operations named in the statement.
They do not replace module sheaves by abstract categories. Their categories reduce to
`ringedSiteModules` and Mathlib's ordinary `DerivedCategory`, through the already
published `ConstantCompletion.Mod`, `D` and `Q`. The geometric morphism record extends
the published `GeometricMorphism`, retaining its algebraic inverse-image lift.
The ordinary and derived comparison equations retain the normalization on generalized
tensor generators and flat-term K-flat representatives. In particular λ and the
inverse-image square are not unspecified natural isomorphisms of the same endpoints.
`ScalarPure`, `ScalarResolving`, `SquarePure` and `SquareResolving` merely name these
specific equations, keeping the generated record interfaces small.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Fixed small-site presentations of Grothendieck topoi | `Presentation.C : Type u`, `SmallCategory C`, `Presentation.J`; the represented topos is `Sheaf J (Type u)`. This is the witness form of `IsGrothendieckTopos`. |
| Morphism of topoi, inverse-image adjunction preserving finite limits | `Geometric` extends `GeometricMorphism`; its inherited `inverse`, `direct`, `adj`, and `leftExact` are exactly these data. `algebra : InverseImageData inverse` uses the published algebraic-lift interface. |
| Constant commutative coefficient rings and a unital map A → B | `{A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)`; `Presentation.ring` is the published constant ring sheaf; `scalarMap` applies the constant-sheaf functor to `CommRingCat.ofHom φ`. |
| Ordinary unbounded derived categories of module sheaves | `Presentation.derived X R = ConstantCompletion.D (X.ring R)`, the standard localization of `ringedSiteModules`; no boundedness or constructibility subcategory occurs. |
| S is derived extension of scalars | `Presentation.scalar X φ = extend (X.scalarMap φ)`, the published universally specified derived extension, with `extendComparison` on complexes. It comes from `nonempty_derivedChangeOfRingsCochainModel`. |
| Exact restriction of scalars U | This auxiliary functor does not occur in either asserted equation. Its existing realization is `ConstantCompletion.dres (X.scalarMap φ)`; no second restriction functor is defined. |
| L_v is inverse image and R_v is derived direct image, with actual derived adjunction/counit | `Image.left : DerivedPull ...` retains its universal cochain comparison; `exactComparison : IsIso left.comparison` records exact inverse image. `ordinaryRight`, `ordinaryAdj`, `right`, `comparison`, `universal`, `computes`, `adj`, and `counit` specify the ordinary right adjoint, its right-derived pair, computation on K-injectives, and normalization of its derived counit to the ordinary adjunction. |
| An open is the slice at a subterminal object | `Open.object`, `Open.subterminal`, `Open.presentation : Sheaf X.J (Type u) ≌ Over object`, and `Open.restriction : j.inverse ⋙ presentation.functor ≅ Over.star object`. Mathlib's `IsSubterminal` is equivalent to the monomorphism into the terminal object. |
| Open extension by zero is left adjoint to restriction and fully faithful with the actual unit | `Operations.extendB`, `extendI`, `openAdjB`, `openAdjI`, `unitB`, `unitI`. The left adjoint and unit are retained together; this universal property determines extension by zero uniquely up to the unique compatible isomorphism. Invertibility of the unit is full faithfulness. Exactness is intrinsic to these open-extension operations, not an extra assumption on φ. |
| Cartesian square pb = ir with open b and i | `Square.b`, `i`, `r`, `p`, `openB`, `openI`; `inverseSquare` is the commuting inverse-image comparison and `cartesian` identifies the upper subterminal with the inverse image of the lower one. `Operations.ordinarySquare`, `pure`, `square`, `resolving` retain the induced module and derived square with canonical normalization. |
| Canonical λ_v | `ScalarComparison.ordinary` is fixed by `ScalarPure`; `derived` is fixed by `ScalarResolving`, using the universal pullback and scalar-extension comparisons on flat-term K-flat complexes. `Scalars.atB`, `atI`, `atR`, `atP` supply it at all four arrows. |
| χ_v is the mate of λ_v, with counit transpose S(ε) λ | `ScalarComparison.chi` applies `mateEquiv a.adj b.adj` to `c.derived.hom`. This is exactly the recorded Mathlib mate operation, including functor associators. |
| β_j is the canonical balancing map for open extension | `Scalars.betaB`, `betaI`, `betaB_mate`, `betaI_mate` retain the uniquely specified open balancing isomorphisms. Their inverses are specified by their mate being λ inverse, the equivalent adjunct characterization in `lem-pur-topos-open-scalar-unit`. Thus the unit normalization is retained rather than choosing an arbitrary isomorphism. Neither asserted exchange identity is assumed by these fields. |
| E_R is exchange obtained as the mate of the inverse-image square | `Operations.exchange` is `mateEquiv o.p.adj o.r.adj ... o.square.hom`. |
| E_R I_b invertible on inputs in question | `Operations.t M` is exchange followed by `r.right.map (inv (openAdjB.unit.app M))`. Since that unit is invertible, the pointwise hypotheses `[IsIso (a.t M)]` and `[IsIso (b.t ((s.V.scalar φ).obj M))]` are equivalent to precisely the stipulated invertibility of exchange on those inputs. |
| t_R and γ_R | `Operations.t` is the node's displayed composite. `Operations.gamma` is `(o.openAdjI.homEquiv _ _).symm (inv (o.t M))`, exactly the adjunct of t inverse. It does not invert χ or γ. |
| First displayed identity, for every N | The first conjunct quantifies `N : s.T.derived A` and equates the componentwise composites λ_i, S_Y(E_A), χ_r and L_i(χ_p), E_B, R_r(λ_b). Lean's `≫` has the reverse written order from functional composition in the node. |
| Second displayed identity, for every admissible M, with B input S_V M | The second conjunct quantifies `M : s.V.derived A` and the two indicated `IsIso` instances. Its left side is S_Z(γ_A), χ_p, R_p(β_b); its right side is β_i, I_i(χ_r), γ_B at `(s.V.scalar φ).obj M`. |
| Source S_Z I_i,A R_r,A M and target R_p,B I_b,B S_V M | Those are literally the source and target of the second conjunct. Equality is in `s.Z.derived B`, hence equality of actual B-module derived morphisms, without applying a forgetful functor. |
| Normalization t_R L_i(γ_R) η_i = 1 | Third and fourth conjuncts, for A and B respectively, state `openAdjI.unit.app ... ≫ i.left.functor.map (gamma M) ≫ t M = 𝟙 _`. |
| Both identities are natural | All comparisons and exchange maps are natural transformations. The fifth and sixth conjuncts explicitly assert naturality of γ_A and γ_B on all arrows between invertible-input objects; the naturality of both displayed composites follows by their composition. |
| D+ restriction requires every displayed object and scalar extension in D+ | The unbounded equalities restrict to the full bounded-below subcategories whenever all endpoints and intermediate functor values lie there. This is a restriction of the same equality, not a replacement D+ functor or an implicit preservation assertion for arbitrary scalar maps. |
| No invertibility of χ_p, χ_r or γ; no properness, coefficient finiteness or Noetherianity | No such typeclass or binder occurs. Only the t components have pointwise `IsIso` hypotheses. There is also no flatness hypothesis on φ, no enough-points assumption, and no scheme presentation. |

### Dependency declarations read and used

- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`: `CategoryTheory.IsGrothendieckTopos`.
  The presentation record retains its small-site witness rather than introducing a new topos notion.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, used by
  `ConstantCompletion.Mod`; its definition is the existing Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`; `ConstantCompletion.D` chooses their standard localization universe.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` and its public
  `DerivedChangeOfRingsCochainModel` import:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
  The published `extend`/`extendComparison` are constructed from precisely this model.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its public interfaces specify the ordinary pure-tensor and derived representative normalization.
  This item spells out the corresponding constant-coefficient scalar/pullback comparisons.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`; its full
  signature and counit formula were read. Used directly to construct E, χ and the β normalization.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.eq_unit_comp_map_iff`, the recorded
  counit-transpose dependency; it is public through the mate module.
- `Sheaf.Paper.RingedTopoiTensorSections`: `SheafOfModules.RingedTensor.pure`.
  Imported as a proof dependency for the generator argument.
- `Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`:
  `CategoryTheory.RingedKFlatWord.word_comparison_descent`; imported as a proof dependency
  for the common flat-term K-flat diagram and descent of ordinary pasting equalities.
- `lem-pur-topos-open-scalar-unit` has no Lean record yet. Its exact equivalent adjunct
  characterization is retained in `Scalars.betaB_mate` and `betaI_mate`; the theorem's
  proof docstring records its role. No speculative import or duplicate theorem was added.

The item's statement dependencies cite `def-trf-geometric-morphism`,
`def-sfb-constant-completion-coefficient-data`,
`def-pur-strict-quotient-completion-data` and the new definition owner
`def-pur-constant-coefficient-inverse-image-data`. The theorem node
`lem-weil-pbc-constant-completion-equivalence` is removed from `stmt_deps`: the
statement does not use `ConstantCompletion.equivalence`. No dependency node is edited.
The item module and its theorem signature remain unchanged; its local helpers are
listed in `lean.declarations`.

### Edge cases

Checked the identity square and identity coefficient map: the prescribed mates include their
units and counits, so normalization cannot be replaced by an arbitrary endpoint isomorphism.
The empty open has zero extension, and the full open has the identity localization; neither
is excluded by `IsSubterminal` or the invertible-unit data. Zero modules and the zero
coefficient ring are permitted. Non-flat quotient coefficient maps are allowed because the
scalar functor is genuinely derived and its representative formula only tests K-flat models.
The first identity has no t-invertibility hypothesis at all. For the second, invertibility
is pointwise, imposed at M and at S_V M only; no global base-change theorem or properness is
silently assumed. Unbounded inputs are permitted. D+ is used only by restriction when all
stated objects remain in the full subcategory.

All objects and Hom sets of each presenting site lie in the common ambient universe `u`,
with module sheaves in that universe; this is exactly a site small relative to module sheaves.
Distinct small sites and coefficient rings can be placed in a common such universe. This
does not force the object and Hom universes of any supplied pro-etale site to be equal;
the item is about fixed small-site presentations of topoi.

### Searches

Actual search records are retained in `searches.jsonl`; the interrupted attempt's history was
not overwritten. They include:

- LeanFinder: “Scalar extension compatibility of inverse base change exchange and its normalized
  extension by zero adjunct in a Cartesian square of Grothendieck topoi”. Eight hits, mainly
  `SheafOfModules.conjugateEquiv_pullbackComp_inv`, `pullbackComp`, free-module comparisons and
  adjunction-unit formulas. None states both identities with this inverse-exchange normalization.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.homEquiv`. Zero hits for that
  combined query; `mateEquiv` was separately read in its known Mathlib source and is used.
- Mathlib grep through msearch: `scalar.*exchange|inverseExchange|inverse_exchange` in
  `CategoryTheory`. No hits.
- LeanSearch: “Extension of scalars commutes with inverse image base change exchange and its
  extension by zero adjoint mate”. Eight hits concerning ordinary module scalar adjunctions
  and presheaf pullback; no exact general-topos derived statement.
- Read-only `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, scalar/exchange
  names, `inverseExchange`, `inverse_exchange`, and the new namespace/declaration. No exact
  statement or name collision. The source pro-etale `LowerShriekBaseChange` theorem is a
  scheme/Noetherian-coefficient result with a different exchange square. The project's
  `ProperOpenCoefficientMate` specializes to schemes; `ScalarExchangeConstituents` adds finite
  coefficients; `OpenScalarExchangeMate` is abstract unit-transpose calculus. None replaces
  the present pair of identities on arbitrary Grothendieck topoi.
- Searching the site's geometric-morphism interfaces found `GeometricMorphism`, whose source
  was read and used. Searching the already published constant completion module found the
  universal scalar-extension and inverse-image interfaces used here.

No established counterexample or statement correction was found. There is no
`STATEMENT-DISPUTED` flag. The source is an explicitly agent-formulated abstraction of the
blueprint's coefficient-compatibility steps, as already recorded in the node.

### Validation

Every compilation and diagnostic probe uses the prescribed `scompile.py` wrapper, with the
module header and public-import visibility of the delivered file. The initial draft exposed
an unconstrained `CommRingCat` universe in `scalarMap`, causing expensive sheafification
search; this was repaired by `CommRingCat.{u}`. Large record normalization equations were
then named without altering their content, reducing repeated generated-projection work.
The 60-second limit is unchanged. The final clean compile and required delivery preflight
are recorded by the delivery wrapper; only the expected theorem-sorry warning is permitted.

No second worker was started: the dispatcher's instructions require direct delivery and the
maintainer's independent review. No shared source, contract, launcher script, or live Git
state was edited directly.

The final full-file scompile run exited 0, with sandbox compilation in 31.9 s and
library-module compilation in 43.4 s. It reported no errors or additional warnings.

## New nodes

`def-pur-constant-coefficient-inverse-image-data` records eight existing declarations
in `Sheaf.Paper.ConstantCompletionEquivalence`, with `existing: true` and no new module:
`ConstantCompletion.underlying`, `insertion`, `InverseImageData`, `pull`,
`pullInsertion`, `DerivedPull`, `derivedPull`, and `constantMap`.
The source is Stacks 00YV, 03D2 and 06YY, in particular the flat-term K-flat computation
in sites-cohomology.tex, lemma-derived-base-change. The definition of coherent ring
lifts is not the completion-equivalence theorem. The current DAG has no definition
node owning this package: the exact recorded-declaration scan found only the old
theorem's helper list. The new record does not redeclare any Lean data.
LeanSearch and LeanFinder returned site-induced pullback/free-module comparisons;
Mathlib grep returned only an unrelated model-theory constantMap. Project grep found
the exact published definitions reused here. The new node stores the actual search
log entries, and `searches.jsonl` retains the wrapper-generated evidence.

The new definition's clauses correspond to its existing declarations as follows:
`underlying` forgets to sheaves of sets; `insertion` is the unique sheaf map with
section formula `tensorSection φ M U 1 m`; `InverseImageData.rings` and `.algebra`
supply all ring lifts and their module generalized-section equations;
`.ring_naturality` is the stated ring-map square; `.constants` is natural in every
commutative ring. `pull` is algebraic module image followed by `change`;
`pullInsertion` is the inverse underlying-module comparison followed by insertion.
`DerivedPull.functor`, `.comparison`, `.universal`, `.computation` are exactly the
universal pair and the flat-term K-flat computation. `derivedPull` chooses that
universal pair with the geometric adjunction and finite-limit preservation;
`constantMap` is `.constants.app (CommRingCat.of A)` followed by `.hom`.
No completion-equivalence assertion, Noetherian condition, coefficient-map flatness,
or invertibility of exchange is included in this definition. The small-site universe
is the same as the item's fixed small-site presentation. Identity morphisms, zero
modules and the zero coefficient ring are allowed.

## Second reading by Q159

This is a direct worker self-check; no second agent was started, as required by the
dispatcher. The maintainer supplies independent review. I read the saved item node,
Lean module, current main's definition owners and all eight helper definitions.
The returned head 8227b6409f81 was rejected only for H2 ownership. The initial saved
packet's required dry run passed (commit 3053953be4b), but the ownership repair was
still made. The mathematical statement, proof split, Lean module and theorem signature
are retained, with the hypothesis/clause correspondence in the table above unchanged.
The current-main comparison confirms that the item changes only `lean` and authorized
`stmt_deps` additions. The completion-equivalence theorem is absent from the repaired
`stmt_deps`. The coefficient owner supplies Mod/Cx/D/Q/change/extend/extendComparison;
the strict-quotient owner supplies constant. The new definition owner supplies every
inverse-image helper requested by L, with no new Lean copy and no dependence on the
completion-equivalence theorem. Each of its clauses was checked against the full
published signatures and formulas described above. No statement correction is needed.
