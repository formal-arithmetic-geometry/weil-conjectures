## Worker report

The module `Sheaf.Paper.OrientationScalarTowerTransport`, namespace
`AlgebraicGeometry.ProEtale.OrientationTransport`, states the two transport
arguments and the general same-degree detection assertion of
`lem-sp-orientation-scalar-tower-transport`. Its four theorems have `sorry`
proofs with complete proof plans. Its six helper constructions contain real
compositions of the published canonical maps; no map or object is chosen from
an unconstrained existence statement. The source read is
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`,
paragraph (1), especially the scalar passage and the instruction to remove the
common shift before testing equality levelwise.

The item statement, source, proof and proof dependencies are unchanged. The H2
return on immutable head `bdbf541c84ad` is repaired: the additions of
`lem-sp-strict-line-heart-assembly` and
`lem-sfb-etale-proetale-scalar-mate` to statement dependencies are removed.
The only added statement dependency is the new definition node
`def-sp-proetale-scalar-pullback-iso`, which records the already published
`scalarPullbackProEtaleIso` with `existing: true`. The general-universe evaluator
is the item-local abbrev `towerEvaluation`, directly over the already cited
`det-sp-coefficient-towers-abelian`; it uses no strict-line assembly theorem.
No dependency module or statement correction is needed.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field of characteristic p | `k : FiniteFieldDatum.{u}`; the field, characteristic, finite base field and algebraic-closure structure are its recorded data. |
| Prime ell different from p | `[Fact ell.Prime]`, `hne : ell ≠ k.p` (the tower theorem has `_hne`). |
| All four schemes separated and finite type over k | `X Y X' Y' : Over (Spec (.of k.k))`, with `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on each structure morphism. Finite type is locally finite type plus quasi-compactness. |
| All morphisms over k; arbitrary base change | `f v' u' f'` are morphisms in `Over`; `sq : IsPullback u'.left f'.left f.left v'.left`. There is no flatness, smoothness or properness condition on `v'`. |
| Smooth f of pure relative dimension d ≥ 0 | `d : ℕ`, `[SmoothOfRelativeDimension d f.left]`. |
| Ordinary uncompleted finite coefficient derived categories | The published `FiniteSmoothPurity.proCategory`, `comparison`, `proPullback` and `proScalar`; these are derived module categories and functors, not completed or underived tensors. |
| L = D_X(d)[2d] | `tate A N hA T d` is the comparison image of the published `line A N hA T d`, its ordered d-fold tensor of shifted root lines; d=0 is its actual coefficient unit. |
| omega = f! D_Y | `omega A f`, the canonical etale-origin comparison of `Etale.dualizingComplex`; this is the comparison-coordinate model used by finite smooth purity. |
| Actual exceptional comparison e | `exchange A sq`, the canonical site/pullback comparison followed by comparison of `Etale.dualizingComplexBaseChangeMap`. The latter is the inverse compact-support exchange/counit transpose, not a supplied arbitrary arrow. |
| R = Z/ell^r, r ≥ 1 | `r`, `hr : 1 ≤ r`, and `coefficient ell r = FiniteReduction.Coeff ell r`, the two size lifts of `ZMod (ell^r)`. |
| A finite commutative and ell^r A = 0 | `A : Type (u+1)`, `[CommRing A]`, `[Finite A]`, `hA : ((ell^r : ℕ) : A) = 0`. The binder `φ : coefficient ell r →+* A` is its unique unital scalar map from ZMod, written explicitly for the API; it is not an additional algebra structure choice. |
| Canonical derived scalar comparisons c_f, c_f', both isomorphisms | `scalarComparison φ f.left` and its primed version, and `_hc`, `_hc' : IsIso ...`. The construction is the site/scalar comparison followed by the exceptional scalar counit mate at the unit. |
| Orientations Pi_R, Pi_R', Pi_A, Pi_A' | `piR`, `piR'`, `piA`, `piA'` are isomorphisms from the corresponding `omega` to `tate`. |
| Pi_A c = scalar Pi_R, and primed normalization | `_norm`, `_norm'`; the suppressed canonical Tate scalar identification is explicitly `proTwistMap d sX` or `sX'`. |
| Mixed scalar/exchange square | `_mixed`; its right-hand side starts with the canonical `scalarPullbackProEtaleIso φ u'.left`, then scalar extension of `exchange R sq`, then the primed scalar comparison. |
| Orientation equation at R | `_orientationR`; `tatePullback ...` displays the canonical pullback/Tate identification suppressed in the node. |
| Orientation equation and inverse equation at A | The two conjuncts of `finite_scalar_transport`, respectively `exchange A sq ≫ piA'.hom = pull.map piA.hom ≫ tatePullback.hom` and `pull.map piA.inv ≫ exchange A sq = tatePullback.hom ≫ piA'.inv`. |
| All Tate comparisons canonical, no flatness | `twR`, `twA : OrdinaryFiniteTwistTransport` include roots-in-units and pure-generator normalizations. `sX`, `sX' : CoefficientLineComparison` include the roots power map and pure scalar/root generator normalization. There is no flatness hypothesis on φ. |
| Finite extension E/Q_ell, its valuation ring | `E : Type u` (or independent `Type v` for the general assertions), `[Field E]`, `[Algebra (Padic ell) E]`, `[FiniteDimensional ...]`; the existing `Padic.coefficientExtensionIntegers` supplies O_E. |
| Varying-coefficient sheaf towers and ordinary derived category | `spCoefficientTowers`, `SpCoefficientTowersAbelian`, and their fixed ordinary derived model `B.hasDerived`. The natural-number index n denotes exponent n+1, so the first level is O_E/ell. |
| Full uniform bounded constructible finite-Tor subcategory | `SpTowerCalculus.C` and `spConstructibleTorTowers` in `tower_orientation_transport`. No normalized-tower hypothesis is imposed. |
| Actual tower functors and exceptional comparison | `b : SpTowerShriek.Base`, `o : Operations`, `q : Coordinates`; `m : SpTowerMate.Data ... sq c` supplies the actual adjoints, normalized finite comparisons and restriction certificates. `SpTowerMate.mate ... m x hb` is their actual inverse-exchange mate. `x` supplies the open exchange and `hb` its isomorphism certificate, as in the recorded exceptional-base-change interface. |
| Actual unit and Tate-line sources | `hU` puts the actual `SpTowerGamma.originalUnit` in the full subcategory. `L` with `_line` presents `SpTowerGamma.orderedLine ... w d` in the original tower coordinates. Here `w` is the published normalized root-tower data. The primed line is expressed in its canonical pullback coordinates `(SpTowerMate.U ... m).obj L`. The primed coefficient unit is likewise expressed as `V.obj originalUnit` before its canonical unit identification. |
| Tower orientations a_f, a_f' | `a : L ≅ m.right.obj unit`, `a' : U.obj L ≅ m.right'.obj (V.obj unit)` are the supplied orientation isomorphisms; the maps used throughout are these very maps. This expression retains both actual adjoints and displays the canonical pullback coordinates. |
| Their exact evaluations agree at every level | `_levels : ∀ n : ℕ, ...`, comparing the published exact derived evaluations of `U.map a.hom ≫ mate.app unit` and `a'.hom`. The `.hom` projections only forget full-subcategory membership. |
| Actual tower orientation equation | First conjunct of `tower_orientation_transport`, equality inside the full subcategory, hence also in the ambient ordinary tower derived category. |
| h = a_f'^-1 e u*a_f determined by evaluated identities | Second conjunct, `U.map a.hom ≫ mate.app unit ≫ a'.inv = 𝟙 _`. The source is the pulled-back Tate line, in its canonical coordinates. |
| General detection between two sheaf towers in the same single degree | `shifted_tower_evaluation_injective`: arbitrary `F G : spCoefficientTowers ...`, common `s : ℤ`, maps between `single 0 F` and `single 0 G` shifted by s, with equal images under every `towerEvaluation ell E T B n`, imply `a = b`. The site universe t and field universe v remain independent. This does not quantify over arbitrary derived source or target objects. |
| Ramified levels A_n = A_(E,en) | `ramified_coefficient_level` identifies `(spEllIdeal ell E)^(n+1)` with the existing uniformizer ideal at `e*(n+1)`, where e is the actual order `emultiplicity uniformizer ell |>.toNat`. Equality of ideals induces the canonical quotient identification by the identity on O_E, not a choice of an abstract ring equivalence. |
| Includes nonnormalized towers | General detection quantifies over all `spCoefficientTowers`; neither transport theorem has an `IsSpNormalizedTower` binder. |

The finite exceptional APIs take `HasCompactification` and the primed
`QuasiCompact` presentation instances; these describe the compactifiable
finite-type separated morphisms already in the geometric setting, rather than
extra properness assumptions. The tower version takes `c : Compactification`
and its mate datum to name the very actual adjunction and inverse exchange whose
transport is being asserted. Normalized twist presentations and the line
presentation serve only to spell out the canonical objects and identifications
which the node suppresses. In particular no arbitrary exceptional comparison is
accepted in place of its counit transpose.

Dependency declarations read and used (names abbreviated by namespace only
where the module fixes it):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- Mathlib `AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`;
  morphism-property and `BaseChangeConventions` dependencies supply the
  separated/finite-type and pullback conventions.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules` and its ordinary module
  interpretation; `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`;
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude`.
- `Sheaf.Paper.DerivedPullbackTensorHom` and
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  the ordinary pullback and derived tensor conventions, including `derivedTensor`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: recorded intrinsic
  twists and public finite root-line constructions.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `Etale.dualizingComplexBaseChangeMap`, with the recorded comparison-coordinate
  dualizing complex and the specified compact-support adjunction mate;
  Mathlib `CategoryTheory.Adjunction.Mates`: `mateEquiv`.
- `Sheaf.SecSmoothPurity.FiniteGeneralRing` and its public data:
  `finiteGeneralRingSmoothPurity`, `finiteGeneralRingPrimeSetting`,
  `Etale.FiniteSmoothPurity.coefficient`, `line`, `proScalar`, `proTwistMap`,
  `CoefficientLineComparison`, and `Etale.ExceptionalCoefficients.dualizingScalarMap`.
- `Sheaf.Paper.EtaleProEtaleScalarMate`: `scalarPullbackProEtaleIso`, now owned
  for this statement by `def-sp-proetale-scalar-pullback-iso` with `existing: true`.
  The theorem `etaleProEtale_scalar_mate` is not a statement dependency.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`,
  `spEllIdeal`; `SmoothPurityCoefficientTowersAbelian`:
  `SpCoefficientTowersAbelian`; `SmoothPurityNormalizedTowers`:
  `spDerivedCoefficientEvaluation` (no normalization condition is borrowed).
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `spCoefficientEvaluation`, `SpCoefficientTowersAbelian.hasDerived`,
  `.equivalenceAdditive`, `.evaluationLimits` and `.evaluationColimits`.
  The new item-local `towerEvaluation` is simply the exact evaluator's
  `.mapDerivedCategory`, with those prescribed instances; `t` and `v` remain
  independent. No `StrictLineHeartAssembly` import is used.
- `Sheaf.Paper.SmoothPurityTowerGamma`: `SpTowerGamma.tower_gamma`, with public
  `orderedLine` and `originalUnit` from `SmoothPurityTowerGammaData`.
- `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange`:
  `SpExceptionalBaseChange.tower_exceptional_base_change`, with its public
  `SpTowerMate.Data`, `U`, `V`, `beta`, `mate` definitions.
- Proof imports: `Sheaf.SecSmoothPurity.DirectImageScalarOperations`,
  `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`, and Mathlib derived
  `FullyFaithful` and `ExactFunctor`. The full faithfulness of the single
  embedding, exactness of evaluation and componentwise tower morphisms are
  used in the proof plans; no arbitrary-derived-map faithfulness is assumed.

Edge cases checked before finalizing the signatures: empty schemes and zero
sheaves; relative dimension zero (the ordered line and all comparisons use the
actual coefficient unit); ell=2; r=1; zero finite coefficient ring (no
`Nontrivial A`); nonflat quotient Z/ell^2 to Z/ell; identity and arbitrary base
changes; equal, positive and negative common shifts for single-degree towers;
the first tower level n=0 meaning exponent one; ramified E with e>1; and towers
with noninvertible derived reduction transitions. The argument never cancels a
quotient scalar functor or assumes a tower is normalized. The scalar argument
cancels only pullback of the specified isomorphism c_f.

Searches actually run through `msearch.py NM lem-sp-orientation-scalar-tower-transport`:

- `leanfinder`: “Transport of an orientation square through derived scalar
  extension and equality of maps between equally shifted single sheaf towers
  detected by level evaluation”. Eight unrelated homological hits, including
  `Abelian.Ext.hom_comp_singleFunctor_map_shift`; no exact match.
- `loogle`: `DerivedCategory.singleFunctor, CategoryTheory.Functor.Faithful`.
  Found the single-functor faithfulness instance, not this transport theorem.
- `grep`: `(orientation|dualizing).*(scalar|tower)|(scalar|tower).*(orientation|dualizing)`.
  No relevant Mathlib statement (unrelated UpperHalfPlane fixed-point material).
- Repository `rg` on orientation, scalar, tower and dualizing names in
  `lean/WeilConjectures` and `lean/Sheaf`, plus item-id grep in
  `lean/WeilConjectures`: no existing complete statement. Existing canonical
  scalar arrows, tower mate and exact evaluation helpers are reused.
  `IntegralOrientationReductionInjectivity.lean` has an analogous **private**
  `shifted_single_hom_ext` for its different completed setting; it is not an
  accessible declaration matching this node. As requested by the H2 return,
  the plain exact-evaluation expression previously abbreviated by
  `StrictLineHeartAssembly.ev` is now an item-local abbrev over the abelian
  tower node, without that theorem-node dependency.

No `STATEMENT-DISPUTED` issue or node fault was found. Compilation and delivery
validation results are recorded below once completed.

## Repair of return bdbf541c84ad

1. **H2, remove theorem-node additions.** Compared the restored delivery with
   the current read-only item node. Removed both
   `lem-sp-strict-line-heart-assembly` and
   `lem-sfb-etale-proetale-scalar-mate` from `stmt_deps`. The existing original
   statement dependencies, natural-language statement and all proof steps and
   proof dependencies are retained. The strict-line theorem import is replaced
   by the already recorded abelian coefficient-tower module. The scalar module
   import remains because it defines the unchanged map, now cited via its own
   definition node rather than its unrelated theorem.
2. **H2, inline evaluation without identifying universes.** Added
   `OrientationTransport.towerEvaluation ell E T B n` as a helper abbrev,
   with `E : Type v` and `T : Scheme.{t}`. It installs exactly `B.hasDerived`,
   `B.equivalenceAdditive`, `B.evaluationLimits n`, `B.evaluationColimits n`,
   then abbreviates `(spCoefficientEvaluation ell E T B.equivalence n).mapDerivedCategory`.
   The general shifted-single theorem now uses this expression. The abelian
   tower node is already cited. No new theorem, proof, mathematical hypothesis,
   or universe equality was introduced; the evaluated maps are the same maps.
3. **H2, definition ownership of lambda.** Added
   `def-sp-proetale-scalar-pullback-iso` as an `existing: true` definition node
   for `AlgebraicGeometry.ProEtale.scalarPullbackProEtaleIso` in
   `Sheaf.Paper.EtaleProEtaleScalarMate`. It gives the exact existing
   Type(u+1)-coefficient signature and inverse-mate construction. The item cites
   this definition node. There is no new module duplicating the comparison,
   and no change to its source, target, direction, or normalization.
4. **Advisory on scalarComparison.** Retained the reviewed
   `dualizingComplex` model for coefficients `A : Type (u+1)`.
   `scalarComparison` remains the canonical site/scalar comparison followed by
   `Etale.ExceptionalCoefficients.dualizingScalarMap`. It is not replaced by
   the Type-u-via-ULift `finiteGeneralRingReduction` API. This is only an
   explicit clarification of the model already accepted in the return.

The four theorem proofs remain `by sorry`. The finite scalar theorem and both
its equations, the tower orientation theorem and h identity, and the ramified
ideal equality are unchanged. The general detection theorem differs only by
unfolding the evaluation abbrev into this module. Its domain and codomain remain
two arbitrary sheaf towers in the same single degree.

## New nodes

`def-sp-proetale-scalar-pullback-iso` owns the exact existing comparison
`scalarPullbackProEtaleIso`, so no new Lean module or copy is introduced. For a
ring map A to B with A,B in Type(u+1), and schemes X,Y of universe u, it defines
lambda from pullback after scalar extension to scalar extension after pullback
as the inverse of the scalar-adjunction mate of the exact restriction/pullback
square. The reverse mate's invertibility is the existing
`lem-sfb-proetale-scalar-pullback-mate-invertible`, not a new assertion or a
choice of arbitrary natural isomorphism. The node imposes no finiteness,
flatness, boundedness, or normalization. Edge cases: identity ring or scheme
map, zero ring, empty scheme and nonflat coefficients. Its source is Stacks
07A4 (`lemma-pullback-tensor-product`) and 0G7E (`lemma-pullback-K-flat`), read in
`sites-cohomology.tex`, at the scalar-identification step of the current purity
base-change proof (1). Its ancestor and via path are recorded.

DAG search `rg -l scalarPullbackProEtaleIso dag/nodes` found only theorem nodes,
none owning this comparison as a standalone definition. The existing
`def-sp-constant-scalar-pullback-comparison` was also read: its ringed API takes
A,B in Type u rather than Type(u+1), so the return's authorized new-node option
is used. Blueprint search `scalar pullback` found zero nodes.
Mathlib searches, with their actual full outputs stored in the new node:

- LeanSearch, “Derived scalar extension commutes with exact geometric inverse
  image of constant coefficient pro-etale module sheaves”: eight ordinary
  module/presheaf scalar hits, not this derived pro-etale construction.
- LeanFinder, “Canonical pro-etale constant coefficient derived scalar
  extension pullback natural isomorphism, coefficients in Type (u+1) and
  schemes in universe u”: eight unrelated standard-etale/differentials hits.
- Loogle, `AlgebraicGeometry.ProEtale.scalarPullbackProEtaleIso`: unknown
  identifier, zero Mathlib hits.
- Mathlib grep, `scalarPullback.*Iso|Pullback.*Scalar.*Iso`: zero hits.
  Project grep located the exact declaration in
  `Sheaf.Paper.EtaleProEtaleScalarMate`, and no match for that declaration in
  `lean/WeilConjectures`; hence this node binds that existing declaration.

The new node has the required `import_flags: []`, empty definition proof fields,
complete searches, and no maintainer-only fields. It is directly cited by the
item. Its statement dependencies are precisely its cited constructions and the
invertibility theorem actually used to determine the inverse; no dependency
cycle is introduced.

## Author's check

I re-read the returned H2 entry, all changed signatures and records, and the
scalar comparison source. Every mathematical hypothesis and clause in the
correspondence above is preserved. There is no claimed independent worker
review: the dispatched-worker brief assigns independent review to the
maintainer and prohibits subagents.

## Validation

The repaired module passed `scompile.py NM
lem-sp-orientation-scalar-tower-transport` with no errors or warnings: sandbox
module 21.4 seconds, actual library module 11.6 seconds. All four theorem
proofs are still exactly `by sorry`, every definition has real data, all lines
are at most 100 characters, and all universes are explicitly bound. The
required `deliver2.py --no-push` dry run passed preflight and compilation,
including the server probe for the `existing: true` comparison. It staged only
the item module, item node, new definition node and report. A separate packet
consistency check confirmed that the sole added statement dependency is the
new definition and its prerequisites introduce no cycle back to the item.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
