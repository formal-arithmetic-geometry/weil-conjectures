## Worker report

Item: lem-a1-roos-intrinsic-unit-comparison. Stage 2 only: the sole theorem is
`WeilConjectures.RoosIntrinsicUnitComparison.roos_intrinsic_unit_comparison`, with
proof `sorry`. Both delivered modules compile without warnings on the prescribed
server compiler. All variables and the independent universes `t u` are explicitly
bound, with `autoImplicit false`. No library file or launcher script was edited.

The theorem states the signed chain comparison, actual augmentation identities,
normalized strict derived-limit identification, natural descent and completeness
and shift conclusions. Canonical chain maps are bound existentially with their
full coordinate specifications, which determine them uniquely. Their domains and
codomains are the actual existing strict towers; none is an unconstrained map.
The theorem's docstring reproduces all seven proof steps and their dependencies.

Hypothesis and clause correspondence:

- Prime ell is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Its integer
  ring and fixed uniformizer are the published Padic coefficient constructions,
  used by `PrincipalKoszulStrictReplacement.uniformizer`.
- An arbitrary scheme is `(W : AlgebraicGeometry.Scheme.{t})`. There is no
  finite-field datum, characteristic assumption, finiteness, constructibility,
  connectedness or boundedness hypothesis on W or on a complex.
- R_W and D(R_W) are `completedIntegralCoefficientSheafUnrestricted l E W` and
  `DerivedCategory (PrincipalKoszulStrictReplacement.Modules l E W)`.
  The module universe is `max u (t+1)`; the site still has object universe t+1
  and morphism universe t. The existing standard derived localization is used.
- A flat-term K-flat representative is
  `P : (integralOperationsGoodComplex l E W).FullSubcategory`; its property is
  precisely `IsKFlatIndependentCoefficients` and flatness of every term.
  Every arbitrary K is covered in the last clause; arbitrary representative
  isomorphisms `_e : DerivedCategory.Q.obj P.obj ≅ K` are allowed there.
- Positive n is encoded as `n : ℕ` with exponent n+1, consistently with the
  published principal replacement. `sourceTower` is P tensor the principal
  two-term Koszul complex with transitions (t,1); `targetTower` is P tensor
  the actual constant quotient module restricted along the specified limit
  projection. These constructions keep P in the first tensor variable.
- `tower` and `quotientTower` only assemble these exact existing towers as
  complexes in the tower category using `koszulTowerComplex`.
  `towerMap` is the assembled existing augmentation `comparison`.
- C(Z) is the existing `roosF.obj Z`, namely Cone(1-s)[-1]. `roosχ` gives the
  node's (previous degree,current degree) coordinate order and its signs.
- The intrinsic F(P) is `PrincipalIntrinsicCompletion.fiber`, the identical
  explicit mapping fiber `mappingCocone (-roosU (tower ...))`. Its coordinates
  are (x,y), with differential (dx,(1-s)x-dy). This uses the new principal definition node below, while the recorded general
  intrinsic-completion dependency keeps its full interface.
- The actual intrinsic unit is `ηI P`, constrained by `UnitFormula`: its product
  component is `Pi.lift (levelUnit ...)`, and its previous-degree component is
  zero. `levelUnit` tensors the actual degree-zero Koszul inclusion with the
  identity of P, through the standard right unitor. It is not chosen from an
  unnormalized existence statement.
- The independent quotient unit is `quotientUnit`, obtained by tensoring the
  actual `projection`, again through that standard unitor. `ηV` and `ηU` obey
  `AugmentationFormula` with `levelUnit` and `quotientUnit`, respectively.
  This writes their full (0,u) coordinates in every integer degree.
- The chain isomorphism is `j P : fiber ... ≅ roosF.obj (tower ...)`.
  Its displayed coordinate equality is exactly `(-snd,fst)`, rendering
  (x,y) mapped to (-y,x). Being a chain isomorphism includes its inverse.
  The next conjunct is `ηI P ≫ (j P).hom = ηV P` and
  `ηV P ≫ roosF.map (towerMap ...) = ηU P`, as strict chain equalities.
- Descent is represented by `FI FU : D(R_W) ⥤ D(R_W)`, natural transformations
  `unitI` and `comp`, a natural isomorphism `d : FI ≅ FU`, and the actual unit
  identity `unitI ≫ d.hom = comp`. The isomorphisms `eI P` and `eU P` identify
  these functors on every good representative with the explicit fiber and
  quotient Roos complexes. Two unit equations require their components to be
  exactly Q(ηI) and Q(ηU), and the comparison equation requires d to be exactly
  Q(j followed by C(a)). Naturality equations for eU and for eI followed by j
  use the existing targetTowerMap and sourceTowerMap for EVERY chain map,
  not only quasi-isomorphisms. Thus this is descent through localization, not
  unrelated objectwise choices. Natural transformations then transport the
  statements through any realization of P as K.
- Rlim U is computed on ANY quasi-isomorphism q from the strict quotient tower
  to ANY K-injective strict-tower complex I. The theorem gives an isomorphism
  rho to Q(lim I), with the normalization
  `rho.hom ≫ Q.map (roosι I) = Q.map (roosF.map q)`, and explicitly asserts
  that Q(roosι I) is invertible. This is exactly the normalized comparison of
  the recorded strict Roos comparison, independent of injective-term choices.
  The inverse-free normalization is equivalent to multiplication by the inverse
  of Q(roosι I), and avoids demanding an unproved typeclass while stating it.
- The map `lam` has every component `quotientUnit ... n ≫ q_n`, so ordinary-limit
  uniqueness fixes it. The equations `Q(ηU) ≫ rho = Q(lam)` and
  `Q(ηI) ≫ Q(j C(a)) ≫ rho = Q(lam)` give precisely
  d_K η_intr = rho_U η_U = comp_K. They fix the actual strict derived
  quotient-augmentation map; mere agreement after derived tower projections
  would not suffice and is not used as its definition here.
- The last conjunct quantifies over every K and assumes the exact recorded
  `IntegralOnSlice.IsComplete l E W none K`. It concludes that unitI and comp
  are isomorphisms, and, for every good representative and realization of K,
  that the actual localized ηU and ηI are isomorphisms.
- For every `r : ℤ`, the same conjunct asserts completeness of K[r],
  invertibility of both descended units at K[r], K-flatness and termwise flatness
  of P[r], and invertibility of the specified ηU(P[r]) and ηI(P[r]). The earlier
  universal comparison clauses apply to every good shifted representative too.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`,
  and the quotient construction; its positive-level finiteness theorem is
  `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the unrestricted completed
  coefficient sheaves it reexports.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory.standard`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  used through the published total-tensor model.
- `Sheaf.Paper.PrincipalKoszulStrictReplacement`: `Modules`, `sourceTower`,
  `targetTower`, `comparison`, `tensorWith`, `multiplication`, `projection`,
  `sourceTowerMap`, `targetTowerMap`. Its main replacement theorem is the first
  proof step. The new definition owner
  def-a1-principal-completed-koszul-towers records these existing declarations;
  the replacement theorem remains only a proof dependency.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosχ`, `roosU`, `roosι`;
  its node was added to stmt_deps, as the explicit cone appears in the signature.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `strictRoosComparison`, including
  the full strict-augmentation normalization, read together with its source.
- `Sheaf.Paper.IntrinsicCompletionCompleted`: `completedKoszulFiber`,
  `completedKoszulUnitComplex`, `completedIntrinsicCompletionMap`; the generic
  interface is retained and the independently sized principal interface is supplied
  by the dependency module below.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`, whose none
  branch is definitionally the original unrestricted Roos-triangle predicate.
- `Sheaf.Paper.IntegralOperationsWellDefined`: `integralOperationsGoodComplex`;
  the new definition owner def-a1-flat-term-kflat-complex records this existing
  predicate; the well-definedness theorem is not a statement dependency.
- Proof imports: `ProEt.countableProducts_exact`,
  `integralScalarExtensionWellDefined`, the localization universal-property API,
  `finiteFreeCompletedScalarComparison` at E/E,
  `canonicalIntegralReductionTower` and `unrestrictedReductionTowerWellDefined`.
  No proof import was omitted for a cycle.

Edge cases checked before and after drafting: empty W, zero complex, arbitrary
unbounded representatives, n=0 meaning the first positive quotient, r=0,
positive and negative shifts, the identity tower resolution, arbitrary K-injective
resolutions without an injective-term assumption, and independent coefficient and
scheme sizes. All formulas are meaningful in these cases. In particular the
normalization equation is not merely an equality of derived projection components.
No statement dispute or source correction is needed.

Searches (the prescribed wrapper records its raw results in searches.jsonl):

- LeanFinder: “The canonical quotient Roos cone unit agrees with the intrinsic
  Koszul completion unit via the signed fiber to cone isomorphism”. Eight generic
  cone/homotopy hits, including mappingCone coordinate lemmas; no exact statement.
- Loogle: `CochainComplex.mappingCone`. Existing cone construction and coordinate
  API, reused; no completed-coefficient unit-comparison theorem.
- Mathlib grep: `roos.*[Ii]ntrinsic|[Ii]ntrinsic.*[Rr]oos`. No hits.
- LeanSearch: “The canonical derived quotient augmentation agrees with the Koszul
  completion unit and is invertible for a derived complete complex”. Eight generic
  completion and derived localization hits; no match.
- rg over lean/WeilConjectures and lean/Sheaf for the item id and prospective full
  names: no existing item declaration and no name collision. Searches by Roos,
  intrinsic completion and units found the principal replacement, the general
  intrinsic completion, normalized strict comparison, and
  `roosIntrinsicCompletenessEquivalence`. That last theorem is an equivalence of
  five completeness predicates, not this signed canonical-map and descent statement;
  its cone-of-scalar-on-P model does not provide the ordered P-tensor-Q tower used here.
- Read the local Stacks source, proetale.tex lemma-naive-completion (099M) and
  sites-cohomology.tex lemma-derived-limit-is-ok (0941), including both proofs.

## New nodes

`def-a1-principal-completed-koszul-towers` owns the existing concrete definitions
in `Sheaf.Paper.PrincipalKoszulStrictReplacement` with `existing: true`.
Its main declaration is `comparison`; the record also lists `Modules`, `residue`,
`projection`, `koszul`, `multiplication`, `quotientComparison`, `augmentation`,
`tensorWith`, `sourceTower`, `residueStep`, `targetTower`, `sourceTowerMap`, and
`targetTowerMap`. Its statement describes each construction with the actual constant
quotient and its specified projection, positive exponent n+1, P in the first factor,
and the action of every chain map. No theorem conclusion is assumed. The existing
`def-pur-principal-koszul-quotient-towers` owns the generic cokernel-based symmetric
pair and is cited rather than duplicated. The existing
`def-sp-completed-uniformizer-section` owns the completed uniformizer and is cited.
This new node gives the remaining actual-quotient and ordered-tensor specialization
needed in the item. Source: Stacks 099M and 0A0E, item proof steps 1 and 3.

`def-a1-flat-term-kflat-complex` owns the existing
`WeilConjectures.integralOperationsGoodComplex` in
`Sheaf.Paper.IntegralOperationsWellDefined`, with `existing: true`. Its statement
is exactly the conjunction of the recorded independent-coefficient K-flat predicate
and flatness in every integer degree. All morphisms in its full subcategory are
ordinary chain maps. No boundedness is added. Source: Stacks 06YN and 03ER and item
proof steps 5 and 7. No existing definition node records this conjunction.

`def-a1-principal-intrinsic-completion` owns the delivered
`Sheaf.Paper.PrincipalIntrinsicCompletion` module and all five of its declarations:
`tower`, `fiber`, `tensorUnit`, `levelUnit`, `UnitFormula`. The tower is the exact
existing principal tower assembled degreewise; the fiber is mappingCocone(-u),
the unitor is Mathlib's standard right unitor, the level unit tensors the actual
cone inclusion, and UnitFormula pins the product component and the zero shifted
component. These are definitions with real data and no postponed theorem. The
source is Stacks 0A0E/099M and the item's explicit fiber calculation in steps 2 and 3.
It is a principal specialization with independent universes, and does not replace
the recorded general r-generator definition. The generic signed-coordinate model
`def-cbc-signed-koszul-completion-model` is a structure of coordinates, not this
concrete fiber and the predicate on its chain maps.

All three nodes have the item's chapter, unit, nearest blueprint ancestor
`lem-a1-finite-map-purity`, and its full via path prefixed by the item. The queries
actually run for each notion are the common LeanSearch and LeanFinder query
“Principal Koszul quotient tensor towers with transition maps and the mapping fiber
completion unit on flat term K flat complexes” and Mathlib grep
`PrincipalKoszulStrictReplacement|integralOperationsGoodComplex|PrincipalIntrinsicCompletion`.
The raw wrapper records are copied into each node's mathlib_searches, and remain
in searches.jsonl. LeanSearch returned eight generic flatness/tensor-unitor facts;
LeanFinder returned eight algebra-presentation/cotangent facts; Mathlib grep had
zero hits. Project rg found the existing concrete tower definitions and good
predicate, reused as existing:true, and no other ownership of these constructions.
A parsed search through all definition-node lean records found only the completed
uniformizer's existing definition owner. Blueprint searches: principal Koszul
zero hits; flat-term K-flat two unrelated compound definitions; intrinsic completion
zero hits. Generic existing tower and signed-model nodes were opened and compared.

## Return repair

H2: removed the additions `lem-a1-principal-koszul-strict-replacement` and
`lem-pur-integral-operations-well-defined` from stmt_deps. Their modules' plain
constructions now have definition nodes, as requested, and the item cites those
nodes. The principal replacement theorem remains in the unchanged proof_deps.
The good-complex module is explicitly publicly imported for its predicate.
No choose or new assumption was introduced.

H13: removed the packet's override of `def-weil-pbc-intrinsic-completion` entirely.
The live Q22 record, including IntrinsicCompletionCompleted and its 27 declarations,
remains byte-for-byte intact. Its generic module is publicly imported as before.
The five principal definitions now belong only to the new definition node
`def-a1-principal-intrinsic-completion`; all its module/declaration blueprint tags
were changed to that owner. No other node record is edited.

The saved packet's initial dry run passed at 21970b16b85; this was only mechanical
validation and did not discharge the independent return. The repairs above are
substantive DAG ownership changes over that saved packet and the returned head
adc4a78e022e, using the current live records supplied to the delivery wrapper.
The theorem statement and its mathematical objects are unchanged.

## Second reading by NJ

This is a second inspection by the same worker, not an independent reviewer:
the dispatcher explicitly forbids starting other agents, and the maintainer's
independent delivery review is still required. Re-read the node, both modules,
and the seven proof steps. Checked the exact tensor order, actual quotient
projections, zero cochains, the minus sign in j, the inverse-free rho normalization,
all naturality equations, and every completeness/shift clause against the node.
The first compile exposed the need to bind the standard monoidal and preadditive
instances explicitly inside the tensor-unitor definition; that was fixed without
adding any hypothesis. A later compile caught an attempted use of inv before its
IsIso proof was available in the statement; the normalization was written as the
equivalent composition equation. The shifted flatness clause now writes all four
universes explicitly. Both files passed the final two-file scompile run, independently
as sandbox and library modules, with no warnings. No hypothesis, conclusion or
statement text was changed; the added stmt_deps record existing canonical interfaces.


Repair self-check: re-opened both modules and all three new definition records.
Checked the existing signatures of comparison, sourceTowerMap, targetTowerMap and
integralOperationsGoodComplex against the records; the theorem signature is still
verbatim and includes all signed j, UnitFormula, AugmentationFormula, naturality,
normalization, completeness and shift clauses approved in the return. Every new
node is cited directly by the item and its statement cites exactly its stmt_deps.
The general intrinsic-completion node is absent from the delivery delta. Checked
zero P, empty W, first positive level n=0, arbitrary shifts, unbounded P, and
independent t/u again; none of these ownership repairs changes those cases.
