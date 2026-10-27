## Worker report

The module `Sheaf.CategoryTheory.FlatRoosFunctorDescent` states
`CategoryTheory.flatRoosFunctorDescent`, with its sole proof `sorry`. No new tensor,
module category, K-flatness predicate, good-representative category, cone, projection,
or inverse-limit inclusion is defined. The theorem's docstring includes all six
steps of the node's proof, including the cylinder calculation that removes the need
for additivity of Z. The source read was sites-cohomology.tex,
lemma-K-flat-resolution (Tag 06YS), definition-derived-tor (06YU), and
lemma-derived-limit-is-ok (0941), especially the injective-term normalization in
its proof. The source is the extracted agent argument, not a claim that 0941 alone
proves the functor-descent assertion.

Hypothesis and clause correspondence:

- The finite nonempty number of inputs is `k : ℕ`, `_hk : 1 ≤ k`, indexed by
  `Fin k`. There is no bound on k. `C`, `J`, `R` give the input ringed sites.
  `D`, `K`, `S` give the output ringed site. The coefficient sheaves are in
  `CommRingCat`, then canonically forgotten to `RingCat` for module sheaves.
- The sites are small relative to their module universes by `EssentiallySmall`.
  Input site objects, site arrows, coefficients, and derived morphisms have
  separate universe parameters `u,v,r,w`; the output has `uO,vO,rO,wO`.
  No equality of site-object and site-morphism universes is imposed. A finite
  family can be placed in common input universes. The sheafification and
  locally-bijective instances provide the usual abelian category on a relatively
  small site; they are the canonical structures, not extra geometric hypotheses.
- The module category is the recorded `ringedSiteModules` alias of
  `SheafOfModules`. Integer-indexed `CochainComplex` and `DerivedCategory` are
  the ordinary unbounded categories; the explicit `HasDerivedCategory` arguments
  specify the chosen localization universes. Countable products and tower limits
  are the ordinary existing limits of the module-sheaf category; the
  `HasExactLimitsOfShape (Discrete ℕ)` hypothesis is exactness of countable products.
- `ObjectProperty.FullSubcategory (TensorFlatRepresentative (J := J i) (R := R i))`
  is exactly the full cochain category on K-flat complexes with flat terms.
  `CategoryTheory.TensorFlatRepresentative` is the conjunction of the recorded
  `IsKFlatIndependentCoefficients` and `IsFlatOnSite` predicates and retains all
  chain maps through Mathlib's full subcategory. Its existing definition owner is
  `def-weil-pbc-tensor-descent-representative-comparison`. The product of the
  full-subcategory inclusions followed by `DerivedCategory.Q` is q.
- `Z` has that product cochain category as domain and complexes of strict
  `ℕᵒᵖ`-towers as codomain. `_hZ` says that if every input chain map is a
  quasi-isomorphism, each evaluated map of `Z.map f` is a quasi-isomorphism.
  No additivity of Z is assumed. Positive tower index n+1 is represented by n.
- `RF`, `eta`, `_hRF` specify the actual total right-derived inverse limit of
  `roosLimitFunctor`; this is the mathematical meaning of Rlim, not an arbitrary
  functor. `roosF` is precisely Cone(1-s)[-1], on objects and strict maps.
- `Zbar`, `Zhat` have exactly the two requested derived targets. `alpha` and
  `beta` are natural isomorphisms q⋙Zbar ≅ Z⋙Q and q⋙Zhat ≅ Z⋙roosF⋙Q.
  `rZ` is the natural isomorphism Zhat ≅ Zbar⋙RF.
- `theta` is the fixed natural representative comparison Q C → RF Q. Its first
  clause says on every K-injective tower with injective terms that `roosι` is a
  quasi-isomorphism and Q(roosι);theta equals the derived-limit unit `eta`.
  `roosι` has coordinates (0, the product of limit projections), exactly the
  required zero shifted coordinate, as read in StrictRoosModel.lean.
- The representative equation is
  rZ(qP);RF(alpha_P) = beta_P;theta_(ZP). Thus it fixes the entire normalized
  component, with orientations agreeing with the two representative identifications.
- For every resolution `a : Z.obj P ⟶ I` with `[QuasiIso a]`, `[I.IsKInjective]`,
  and injective terms, `eps.hom = Q(roosι I)` and
  `d.hom;RF(Q(a)) = eta_I`. The displayed component is
  beta_P;Q(roosF(a));eps.inv;d.hom, with no unspecified isomorphism substituted.
- `e` records the actual total-limit evaluations. The normalization after every
  resolution says d;e = Q(limit.π);ev.inv, where `ev.hom` is exactly the
  evaluated localized resolution map. The representative projection equation
  rZ;RF(alpha);e = beta;Q(roosEval) therefore preserves those projections.
- Naturality for every derived arrow, including roofs, is part of the types of
  `alpha`, `beta`, `theta`, `rZ` as natural isomorphisms of functors. The proof
  docstring describes the square for a numerator and inverse denominator.
- For any other Zbar', Zhat', alpha', beta', rZ' with these same full representative
  components (`_hcomp`), the conclusion `∃! uv` gives the pair of compatible natural
  isomorphisms. Its first two equations fix them on representatives and its third
  intertwines rZ on every derived input. Changing good resolutions gives another
  such presentation, so this universal comparison is the claimed choice
  independence and its coherence. Equality of level projections alone is never
  a uniqueness hypothesis.

Dependencies read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  Mathlib's `SheafOfModules`, `CochainComplex`, `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`; and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.SiteDerivedTensorRestriction`,
  `CategoryTheory.TensorFlatRepresentative`, recorded among the declarations of
  `def-weil-pbc-tensor-descent-representative-comparison`. This landed definition
  node's statement explicitly defines the exact K-flat/degreewise-flat conjunction.
  Its source signature has independent site-object, arrow and coefficient universes,
  the same module universe r, and the same essentially-small/sheafification context.
  It contains no choice and has the same defining body as the former representative
  predicate. The definition node is cited in place of the tensor-model theorem.
- `Sheaf.CategoryTheory.StrictRoosModel`, `roosF`, `roosι`, `roosEval`,
  `roosLimitFunctor`. Its existing definition node was added to stmt_deps.
- `Sheaf.CategoryTheory.StrictRoosComparison`, `strictRoosComparison`, supplying
  descent and normalized comparisons for all injective-term K-injective resolutions;
  Mathlib `CochainComplex.IsKInjective` gives the precise recorded resolution predicate.
- Proof imports include the recorded
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
  (`site_derived_tensor_descent_independentCoefficients`), Mathlib localization
  universal property (`Localization.lift`, `fac`, `liftNatIso`, `natTrans_ext`),
  product localization (`Functor.IsLocalization.pi`), and levelwise tower
  abelianity (`CategoryTheory.Abelian.functorCategoryAbelian`). The recorded total
  tensor proof dependency is public through the K-flat and tensor-descent modules.

Edge cases checked mathematically: k=1 uses an ordinary one-variable localization;
k=0 is excluded exactly as in the node; zero Z and zero towers impose no nonzero
or nonempty sheaf hypothesis. Constant towers, zero transitions, identity resolution
maps and arbitrarily unbounded complexes retain the same signed cone construction.
The unit equation on I and the equation for d force the right inverse orientation
in the K-injective formula. The finite-family universes may be enlarged together;
the output coefficient and localization universes remain independent of the inputs.
No statement correction or disputed mathematical clause was needed.

Searches actually run with msearch.py (2026-10-22):

- LeanFinder: "Functor on flat K-flat complexes preserving quasi-isomorphisms
  descends to derived categories with normalized Roos inverse limit comparison".
  Eight hits, headed by `Functor.mapHomologicalComplexUpToQuasiIsoFactors` and
  `mapDerivedCategoryFactors`; these assume additive functors between abelian
  categories and do not state this arbitrary-Z finite-product descent.
- Loogle: `CategoryTheory.Localization.liftNatIso`. Three hits (`liftNatIso`,
  `_hom`, `_inv`). This is used as a proof ingredient; it assumes the required
  localization and supplies none of the normalized Roos data.
- Grep: `IsLocalization.pi|liftNatIso|[Rr]oos` in `CategoryTheory/Localization`.
  Eighteen hits, including Localization.Predicate and LocalizerMorphism;
  the generic lift interfaces are not this statement.
- LeanSearch: "Descent of a functor on flat term K-flat cochain complexes to a
  product of unbounded derived categories with a natural normalized Roos comparison".
  Eight hits (`DerivedCategory.Q`, `Functor.mapDerivedCategory`,
  `rightDerivedToHomotopyCategory`, their comparisons); no complete match.
- Direct rg of lean/WeilConjectures, lean/Sheaf and the upstream declaration index
  for this item id, flatRoosFunctorDescent, Roos descent and flat representative
  predicates: no existing complete theorem. `ExactProductFunctorRoosDescent` was
  read and requires an exact additive functor on module sheaves, so does not state
  this result. The broader flat-representative search found
  `cochainTensorFlatRepresentatives`, a plain conjunction in a theorem module.
  During repair, a DAG search also found the landed definition node
  `def-weil-pbc-tensor-descent-representative-comparison`, which explicitly owns
  `CategoryTheory.TensorFlatRepresentative` and the same conjunction. This existing
  definition is reused; no new node or dependency module is needed.


Compilation uses scompile.py only. The localization universes remain explicit.
Only the single named theorem is postponed. The repaired file is compiled again,
and the final dry run and delivery repeat compilation and preflight.


## Repair of independent review at 86506601d429

H2 is repaired using an existing landed definition owner, as required by the
bottom-up rule. Current main contains
`def-weil-pbc-tensor-descent-representative-comparison`; its statement defines
`TensorFlatRepresentative` to mean K-flatness and flatness of every term, and its
lean.declarations includes `CategoryTheory.TensorFlatRepresentative`. The source
at `Sheaf/Paper/SiteDerivedTensorRestriction.lean:128-131` is a plain definition
with exactly that conjunction and real data, with no theorem choice. Its full
signature and docstring, the containing node, and the two underlying predicate
signatures were read. Its smallness and universe assumptions match the theorem.

Removed the public import of `Sheaf.Algebra.Homology.CochainTensorModelRigidity`
and removed `lem-sf-cochain-tensor-model-rigidity` from stmt_deps. Replaced all
twelve occurrences of its representative predicate with the definition-owned
`TensorFlatRepresentative`, passed explicitly to `ObjectProperty.FullSubcategory`
or `ObjectProperty.ι`. Added its landed definition owner to stmt_deps and imported
`Sheaf.Paper.SiteDerivedTensorRestriction`. This introduces no new definition,
choice, assumption, or mathematical statement change. The single sorry and six-step
proof docstring remain intact. The lean.statement record is verbatim from the file.

The saved packet's initial dry run passed at 80d3c97c490. The requested repair
was nevertheless applied. Directly inlining the conjunction incurred the prescribed
60-second limit; the final version reuses the existing definition above. This
restores the compact named-predicate interface and is checked again by scompile.py,
then the delivery dry run, then the delivery tool.

Additional searches during repair:

- `tools/blueprint_refs.py search 'flat cochain representatives'`: 0 blueprint
  nodes match. The ancestor command returned `def-weil-frobenius-coefficient-twists`.
- msearch LeanSearch, `full subcategory of K-flat cochain complexes of sheaves of
  modules with flat terms`: 8 hits, chiefly the generic `ObjectProperty.FullSubcategory`
  constructors and K-projective orthogonality; none give the specialized conjunction.
- msearch Loogle, `CategoryTheory.ObjectProperty.FullSubcategory`: 12 hits covering
  the generic full subcategory, its category, inclusion, fullness and faithfulness.
- msearch grep, `cochainTensorFlatRepresentatives|TensorFlatRepresentative|IsKFlatIndependentCoefficients`:
  0 Mathlib hits. Direct rg of `lean/WeilConjectures` and `lean/Sheaf` found the two
  representative predicates in the recorded Sheaf modules; DAG rg found the existing
  definition owner above as well as three theorem nodes mentioning the helpers.

## Second reading by NW

This is a worker self-check of the repair, without starting another agent; the
maintainer's independent review remains the independent assessment. With the node
and final Lean file open, the only change to any mathematical object is replacement
of a predicate by the identical two-predicate definition now owned by a definition
node. Each of the twelve occurrences uses the same J i, R i and module universe r.
The full subcategory still has all cochain maps, and its inclusion followed by Q is
unchanged definitionally. The new dependency's statement explicitly includes this
notion, rather than merely mentioning a theorem that uses it. No dependency file
is edited, and the item's text, proof, proof_deps and all other fields are unchanged
apart from lean and the permitted statement-dependency additions.

The k ≥ 1/Fin k input, independent universes, exact countable products, non-additive
Z with levelwise quasi-isomorphism condition, actual right-derived RF, fixed theta
normalization, full representative component, formula for every injective-term
K-injective resolution, actual projections, and unique compatible natural
isomorphisms are all preserved clause by clause as detailed in the worker report.
The node's edge cases k=1, zero functors/towers, identity resolutions, and unbounded
complexes remain covered. No new node, dependency repair or statement correction is
needed. No mathematical fault or disputed clause is asserted.

Validation: final scompile.py server confirmation passed with exit 0 in 53.9 s
(nice 19, two threads, 60 s limit). Only the expected sorry warning is permitted.
The worker self-check verified the exact recorded signature, 12 uses of the
definition-owned predicate, one sorry, and all lines at most 100 characters.
