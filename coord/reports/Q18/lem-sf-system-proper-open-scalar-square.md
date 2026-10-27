## Worker report

Module: `Sheaf.SixFunctors.SystemProperOpenScalarSquare`.
Main declaration: `AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar.systemProperOpenScalarSquare`.

This states the entire node on the actual ordinary unbounded derived categories of
strict semilinear systems. The module supplies canonical scalar operations needed to
write its formula. No statement correction or dependency-module repair is needed. The added definition
node `def-sf-diagram-system-operation-shifts` owns the already published plain shift
instances. It replaces the Models theorem in statement dependencies, while
`lem-pur-diagram-open-clopen-shift-models` stays in proof dependencies. The existing
definition owners for gamma and the compositors are also cited explicitly. All
theorems have `sorry` proofs, as required.

Hypotheses and objects, clause by clause:

- The inverse ring sequences are `A B : ℕ → CommRingCat.{u+1}` and the maps
  `a n : A (n+1) ⟶ A n`, `b n : B (n+1) ⟶ B n`. Index 0 denotes the first
  coefficient ring; this is a reindexing of the node's sequence beginning at 1.
- The unital coefficient maps are `φ n : A n ⟶ B n`, with the exact compatibility
  `hφ : ∀ n, φ (n+1) ≫ b n = a n ≫ φ n`. CommRingCat morphisms are unital.
- The rank hypothesis is `d : ℕ`, `hd : 1 ≤ d`. `Bases A B b φ d` contains a
  `Module.Basis (Fin d) (A n) (coefficientModule A B φ n)` at each n and the
  equation `(b n).hom (basis (n+1) j) = basis n j` for every n,j.
  `coefficientModule` uses the existing `ModuleCat.restrictScalars (φ n).hom`
  on `B n`, so no independent algebra action is introduced.
- The sites, constant ring sheaves, sequence-site rings, strict module systems
  and ordinary unbounded derived categories are exactly `coefficients`,
  `transition`, `ringSystem`, `Modules`, `Derived` from the recorded intrinsic
  mate dependency. Schemes live in universe u; small-site objects in u+1,
  morphisms in u; coefficients/modules in u+1; derived Hom universe in u+2.
  No universe equality or restriction on transition flatness is added.
- `calculus X` specializes the recorded `semilinearDerivedSections` to these
  coefficient sheaves and this actual compatible system map. Its `ScalarData`
  contains the actual sheafified tensor functor with prescribed object/map
  functions, the unit-normalized ordinary adjunction, the everywhere-defined
  K-flat derived extension and its universal counit. This is a universal,
  normalized construction, determined up to its counit-compatible isomorphism,
  rather than an arbitrary functor chosen from bare existence.
- `E X` is that existing ordinary tensor functor. `extension_exact` records its
  finite-free exactness on whole systems. `T X` is its exact localization on
  all complexes, hence computes the stipulated derived extension. This is
  precisely proof step 1 of the node: for every K-flat resolution Q → M,
  E(Q) → E(M) is a quasi-isomorphism, so the derived model is computed by E(M).
  Definitions contain actual data; only the named exactness proof is postponed.
- The square binders are `k : U ⟶ V`, `i : W ⟶ Z`, `r : U ⟶ W`, `p : V ⟶ Z`,
  `[IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]`,
  `[IsProper r] [IsProper p]`, `h : k ≫ p = r ≫ i`. There is no Cartesian,
  absolute separatedness, finite-type base, or nonemptiness assumption.
- P, S and J are the recorded `P`, `R`, `J`, with `adj` and `jAdj` their
  stipulated derived adjunctions. Gamma is literally the recorded `gamma`:
  the proper mate of the intrinsic clopen-projector alpha word.
- `restrictionPush_existsUnique` specifies the ordinary coefficient-restriction /
  geometric-direct-image isomorphism by identity on every section over the same
  fibre product. `ellOrdinary` is conjugation along the two composite adjunctions.
  Thus `ell` is the localized inverse-image/tensor comparison, normalized by the
  actual scalar unit, without a free choice of an isomorphism.
- `chi v` is literally `mateEquiv (adj A a v) (adj B b v) (ell v).hom`.
  Its transpose is `ell` followed by scalar extension of the A-counit, exactly
  the node's definition of chi; no invertibility of chi is asserted or assumed.
- `betaInv j` is the inverse mate of `ell j` inverted, under the two actual
  open adjunctions. `betaInv_isIso` is the named open-normalization assertion;
  `beta j` is its inverse isomorphism. This is the open-unit tensor adjunct
  normalization of the recorded open-tensor theorem with second factor B.
- Conjunct 1 is the displayed scalar square for every `M : Derived A a U`,
  in Lean's left-to-right composition order:
  `T.map (gamma_A.app M) ≫ chi_p.app (J_A k M) ≫ R_B p.map (beta_k.hom.app M)`
  equals `beta_i.hom.app (R_A r M) ≫ J_B i.map (chi_r.app M) ≫ gamma_B.app (T M)`.
  Both sides are B-linear arrows in `Derived B b Z`. Neither evaluation nor
  inverse limit nor scalar restriction is applied to this equality.
- Conjunct 2 states composition of chi with the actual `sComp A a v w` and
  `sComp B b v w`. These are exactly the canonical direct-image compositors
  defined as mates of inverse-image composition. Conjunct 3 states its identity
  normalization using the actual `sId`. Applying an outer proper R to conjunct 1
  and using conjunct 2 is the promised whiskering; the composition clause is
  stated for arbitrary composable scheme maps as the node's every-v clause says.
- Conjunct 4 is `NatTrans.CommShift ell.hom ℤ ∧ NatTrans.CommShift chi ℤ` for
  every v. Conjunct 5 is `NatTrans.CommShift beta.hom ℤ` for every open j.
  Conjunct 6 is `NatTrans.CommShift gamma_A ℤ ∧ NatTrans.CommShift gamma_B ℤ`
  for every permitted square. These imply shift compatibility of both composite
  sides and their whiskerings. `scalarShift` is the exact termwise shift on E;
  P,J,R use the landed `DiagramShift.pullShift`, `extensionShift`, `directShift`.
  The latter is the canonical K-injective shift, identified with the
  counit-normalized mate shift in that dependency's Models assertion.
- No constructibility, normalized/cartesian-system predicate, finite Tor
  amplitude, or boundedness assumption occurs anywhere on M.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.SemilinearDerivedSections` and its public calculus/model modules:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`,
  `SemilinearDerivedSectionsData.coefficientExtension`, `ScalarSystems.scalar`,
  `ScalarData.model`, `ScalarData.ordinaryAdjunction`, `systemMap`, `res`,
  and the actual `DerivedChangeOfRingsCochainModel.E`, object/map equations and
  universal K-flat counit. Their signatures and normalization docstrings were read.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`:
  `AlgebraicGeometry.ProEtale.SemilinearProperOpen.coefficients`, `transition`,
  `Modules`, `Derived`, `P`, `R`, `J`, `ordinaryAdj`, `jAdj`, `adj`, `gamma`,
  `sComp`, `sId`; `alpha` and `pi` were read to verify the exact intrinsic mate.
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.openTensorNormalization`, including its arbitrary-system clause,
  `OpenTensorNormalization.Assertion.beta_inverse`, `.gamma_inverse`, and both
  restriction identities; used for open balancing and the beta invertibility plan.
- `Sheaf.Paper.DiagramOpenClopenShiftModels`: the three public shift instances and
  `diagramOpenClopenShiftModels`; used instead of redeclaring the same shifts.
- The scheme-properties dependency is explicitly a convention collecting other
  nodes. The actual Mathlib `IsOpenImmersion`, `QuasiCompact`, `IsProper`
  declarations are used with their full existing meanings.
- Plain proof imports: `Sheaf.CategoryTheory.ExchangeMateCube`
  (`CategoryTheory.exchangeMate_cube`), Mathlib localization predicate and mates.
  The recorded Mathlib matches `mateEquiv`, `mateEquiv_hcomp`, `mateEquiv_vcomp`,
  `conjugateEquiv_id`, and `Localization.lift` supply the other proof dependencies.

Edge cases checked before writing and again against the signature: d=1 and the
identity coefficient map; zero coefficient rings (a basis of a zero module over
zero rings is allowed); arbitrary nonflat coefficient transitions; empty U or an
empty complementary clopen component; identity opens; non-Cartesian squares;
arbitrary proper maps without absolute separatedness; unbounded M and M=0;
shifts 0, positive and negative integers. No field, invertibility or coefficient
characteristic restriction was introduced. There is no equality detection by
level evaluation or by derived scalar restriction.

Searches performed for this item:

- msearch leanfinder: "Finite free scalar extension commutes with the proper open
  adjunction mate on unbounded derived semilinear sheaf systems". Generic scalar,
  module and adjunction results only; no statement of this intrinsic square.
- msearch loogle: "CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction".
  Twelve generic conjugation results, including `conjugateEquiv` and its
  identity/isomorphism laws. They are used; none states the geometric scalar square.
- msearch grep: "proper.*open.*scalar|scalar.*proper.*open|semilinear.*mate".
  Four Mathlib hits, all Presburger semilinear-set files, unrelated.
- msearch leansearch: "Scalar extension commutes with proper open interchange of
  strict sheaf module systems". Eight generic module-scalar and sheaf-module hits,
  including `ModuleCat.extendRestrictScalarsAdj`; no matching system theorem.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for proper/open/scalar, the exact
  item id, `SystemProperOpenScalarSquare`, and compatible bases. No upstream item
  or exact theorem. Existing proper/open scalar results use finite/condensed
  coefficients or constant towers, not these arbitrary varying ring systems.
  The recorded intrinsic `gamma` and scalar calculus were found and reused.
  `DerivedFiniteFreeScalarCoordinates` concerns sheaf bases on equal-universe
  sites; `OpenStarShriekScalarMateSquare` concerns condensed coefficient modules.
  Neither states this node. `grep -rn` of the exact id on WeilConjectures had no hits.
- The current blueprint unit and its proof were read in
  `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/`.
  Zheng PDF pp. 34--36 was read using pdftotext: 5.13 supplies coefficient/proper
  compatibility and 5.14--5.15 the open/proper system gluing. The node correctly
  identifies the arbitrary finite-free intrinsic naturality proof as agent-written.

Validation: scompile.py compiled the actual module, with its exact module-mode
public/private imports, both under its sandbox and library names. It compiled the
newly landed shift dependency privately as needed. No errors or warnings remained.
Only theorem proofs are postponed. No disputed statement or source discrepancy found.

## Second reading by Q18

The worker reopened the node, the final Lean signature, the ordinary scalar
adjunction and the intrinsic gamma definition for a final self-check. The two
composites have the same B-derived-system source and target; the Lean equation
is the node's equation in left-to-right order. All square hypotheses, the
finite rank/basis-transition assumptions, arbitrary-M quantification, the
canonical direct-image composition/identity equations and all integer-shift
clauses are present. The open comparison was corrected during elaboration to
use the inverse direction of the open mate bijection. The newly landed
DiagramShift instances replaced duplicate local definitions of those notions.
This is a worker self-check; the maintainer's independent review remains the
independent second reading specified in the dispatch brief. No other agent was
started, as the brief expressly forbids it.

## New nodes

`def-sf-diagram-system-operation-shifts` records the three existing instances
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift.pullShift`,
`extensionShift`, and `directShift` in
`Sheaf.Paper.DiagramOpenClopenShiftModels`, with `existing: true` and no new module.
Its only statement dependency is `def-sp-semilinear-constant-ring-operations`.
The first two instances are literally `inferInstanceAs` for the exact termwise
`mapDerivedCategory` shifts of pull and extension; the third is literally
`inferInstanceAs` for the right-derived shift of push. They contain real data and
do not use a choice from `diagramOpenClopenShiftModels`. The definition states no
adjunction-shift or comparison-shift theorem. Stacks 015F, 03DJ, 070H and 07A6
provide the exact localization and K-injective construction sources.

New searches: msearch LeanSearch for canonical integer cochain shifts on derived
semilinear operations returned eight generic complex-shift declarations. Loogle
for `CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.Functor.CommShift`
returned the generic exact-derived-functor CommShift instance. Mathlib grep for
`mapDerivedCategory.*CommShift|rightDerivedFunctor.*CommShift|instance.*commShift`
in `Algebra/Homology` returned fourteen generic shift uses/instances. The actual
query results are retained verbatim in the node's mathlib_searches and search log.
DAG rg found only the Models theorem, with no definition owner; upstream
WeilConjectures rg found no specialized instances. Project rg found the existing
module and the RationalLocalizedHom and CondensedLocalizationHom consumers.
`blueprint_refs.py search 'diagram system operation shifts'` returned zero matches;
its ancestor command returned None, recorded exactly in blueprint.from.node.

## Returned delivery repair

L H2 on immutable returned head `fe3335f14970`: replaced
`lem-pur-diagram-open-clopen-shift-models` in stmt_deps with
`def-sf-diagram-system-operation-shifts`, retaining the theorem in proof_deps.
The new definition node gives definition ownership to exactly the three instances
used by the main theorem's CommShift clauses. The Lean file is unchanged, as the
independent review requested. Its substance was accepted in that review.

The advisory is also addressed: `def-coef-semilinear-proper-open-mate` and
`def-sf-semilinear-proper-open-comparisons` are now explicit statement dependencies
for the unchanged recorded gamma, sComp and sId definitions. Their published
records and source declarations were read; no dependency records were changed.
Comparison against current main found no changes to any other existing node field.
The initial saved-packet dry run passed at `65ed260d795`; this repair makes a
substantive node-record delta from the returned packet before the final dry run.

Final worker self-check: reopened all three instance bodies and matched them with
the definition node, including arbitrary morphisms for P/R and only
IsOpenImmersion for J. Universe u and u+1 remain unchanged. No basis, properness,
quasi-compactness, or boundedness assumption is imposed on these definitions.
Identity maps, empty opens, zero rings, and positive/negative/zero integer shifts
are all included. The main theorem and its signature remain byte-identical to
the accepted mathematical statement, with all six conjuncts unchanged.

The repaired-packet dry run required `import_flags` on the new definition node;
added the empty list required by the current schema, with no mathematical change.
