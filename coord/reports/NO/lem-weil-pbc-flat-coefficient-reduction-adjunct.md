## Worker report

The module `Sheaf.Algebra.Homology.FlatCoefficientReductionAdjunct` states
`SheafOfModules.flat_coefficient_reduction_adjunct`. Its only theorem proof is
`sorry`. It defines three concrete canonical maps, and a structure recording all
clauses of this node. The structure introduces no second scalar-extension functor,
restriction functor, tensor product, derived category, or adjunction. No data is
chosen from the theorem. In particular the conclusion is not an unspecified
natural isomorphism: `ordinary_pure` and `representative` uniquely fix its maps on
a resolving class, and localization fixes the comparison on every derived object.

The module uses the existing `SuccessiveDerivedQuotient.Presentation` family `p`
and its `Normalization` `N`. Existence of this normalized family is the recorded
`successive_derived_quotient_normalization` theorem. These are presentations of the
canonical functors of the node, not new mathematical assumptions. `Presentation`
fixes the ordinary objects and maps as `changeOfRings` and `changeOfRingsHom`, and
its derived counit has the universal left-derived property. `Normalization` fixes
restriction on sections and under localization, and fixes adjunction units and
associators by their tensor formulas. The theorem applies to any such presentation,
so no arbitrary selected isomorphism is substituted for the canonical comparison.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small site C | `C : Type u`, `Category.{v} C`, `EssentiallySmall.{r} C`, `J : GrothendieckTopology C`. The sheafification and locally bijective/sheaf-compose instances are the existing site infrastructure; a small site relative to module universe r has these. Object, morphism and coefficient universes remain independent. |
| R to B to S, commutative ring sheaves | `R B : Sheaf J CommRingCat.{r}`, `φ : R ⟶ B`, and universally quantified `S`, `ψ : B ⟶ S` in the comparison structure. |
| Module sheaves and unbounded derived categories | Existing `Modules A` abbreviates `ringedSiteModules (derivedChangeRingIndependentCoefficients J A)`; `DerivedCategory (Modules A)` is used throughout. `hD` chooses a common derived morphism universe for these categories, without identifying site or coefficient universes. The standard localization supplies this infrastructure when needed. |
| Exact scalar restriction | Existing `restriction φ` on modules; `N.right φ` on derived categories, fixed by `N.right_factors`, `N.restrictionComp_sections` and `N.rightComp_normalization`. |
| K-flat derived scalar extension | `(p a).derived` with `(p a).counit` and universal left-derived property; `N.computed` supplies its invertible flat-term K-flat computation. |
| B flat over R, tensor with B exact | `hflat : exactFunctor (Modules R) (Modules B) (p φ).ordinary`. The ordinary functor is precisely sheafified B tensor_R minus. |
| Multiplication B tensor_R S to S is an isomorphism | `hμ : IsIso (flatCoefficientMultiplication p N φ ψ)`. This defined map is the normalized ordinary extension/restriction counit at `Res_ψ(unit S)`, hence sends b tensor s to ψ(b)s. Its source is B tensor_R S as a B-module, with the R-action on S given by ψφ. Invertibility as a B-module is equivalent to invertibility of this sheaf multiplication map. |
| Every M in D(B), natural isomorphism κ | `derived ψ hμ : N.right φ ⋙ (p (φ ≫ ψ)).derived ≅ (p ψ).derived`; a `NatIso`, hence natural for every derived morphism and invertible at every M. |
| Balanced formula x tensor s maps to x tensor s | `ordinary ψ hμ` is a `NatIso` and `ordinary_pure` states the exact sheafified pure-tensor formula. Existing `sectionTensor` uses the scalar-first convention s tensor x. |
| Represented on a K-flat B-complex with flat terms | `representative` quantifies over all such `P` using `IsKFlatIndependentCoefficients` and `∀ i, IsFlatOnSite (P.X i)`. It compares κ against the termwise ordinary comparison through the existing universal counits. `restricted_computed` makes the R-side counit invertible on the restricted representative; the B-side is already invertible by `N.computed`. |
| Canonical extension/restriction adjunctions | `N.adjunction`, normalized on K-flat models by `N.adjunction_normalization` and `N.ordinary_unit`; no freely chosen adjunction is quantified separately. |
| Every Q and p : M to Res Q; its B and R adjuncts | `adjunct` quantifies over `M`, `Q`, and arbitrary derived `f : M ⟶ (N.right ψ).obj Q`. Each `.homEquiv.symm` is precisely the indicated adjunct. The R map is `(N.right φ).map f` followed by the canonical restriction-composition identification `(N.rightComp φ ψ).hom.app Q`. |
| p_R sharp = p_B sharp composed with κ | The `adjunct` equality has the R adjunct on the left and `(derived ψ hμ).hom.app M ≫ ...B-adjunct...` on the right. Lean's composition order is the reverse of the paper's functional order. |
| Commutes with a B-algebra morphism S to S' under the same multiplication hypothesis | `coefficient_naturality` quantifies over arbitrary `τ : S ⟶ S'`, and both `hμ` and `hμ'` for ψ and ψτ. `flatCoefficientChange` is a concrete map defined using the normalized extension unit and associator; it is the class of x tensor s maps to x tensor τ(s). The equality is in D(S) after `N.right τ`, with the sole `eqToHom` accounting for associativity of ring-map composition. |
| Successive derived extensions under canonical associators | `successive` uses `(p τ).derived.map κ`, `N.derived ψ τ`, and `N.derived (φ ≫ ψ) τ`. It imposes no flatness on τ. `N.associative` makes this binary compatibility coherent under all finite iterations. |
| Equal-index comparison is canonical unit identification | `equal_index` uses `flatCoefficientUnit`, defined from the existing associator for a and the identity ring map, followed only by `a ≫ 𝟙 = a`. The associator formula is (x tensor s) tensor t maps to x tensor st. This is a composite of isomorphisms, not a newly chosen morphism. |

The multiplication, coefficient-change, and scalar-unit helpers are actual composites
of previously normalized maps, with full data and no postponed proof inside a definition.
The ordinary comparison is recorded with its pure-tensor formula, which determines
it locally on sections and hence as a sheaf map. The derived representative then
determines its localization. Thus the conclusion introduces no arbitrary map and
its existence statement leaves no hollow definition. The three helpers and the
structure are listed in `lean.declarations`, all belonging to this node's notion.

Dependencies read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`;
  the underlying universal scalar-extension interface is also the one bundled by
  `SuccessiveDerivedQuotient.Presentation`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction`; proof import only,
  specialized by the coefficient adjunction on the identity topos.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`:
  `CategoryTheory.Adjunction.exists_derived_adjunction_of_essentially_constant`;
  proof import, giving the normalized derived pair.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `SuccessiveDerivedQuotient.Modules`, `restriction`, `Presentation`,
  `Normalization`, `sectionTensor`, `successive_derived_quotient_normalization`.
  The definitions and structures are registered by the new existing-definition node
  `def-pbc-successive-derived-scalar-normalization-data` in `stmt_deps`. The existence
  theorem remains in `proof_deps` only; it is not called or chosen in the statement.
  The two recorded K-flat/flat definition nodes are also used in the signature.
- All other recorded proof dependencies are imported for the eight-step proof:
  `exists_isKFlatResolutionIndependentCoefficients`,
  `exists_changeOfRings_tensorCancellation`, `changeOfRings_isKFlat_of_flat_terms`,
  `sheafRingDerivedCoefficientAdjunction`,
  `site_derived_tensor_descent_independentCoefficients`,
  `CategoryTheory.moduleSheaves_colimits_forgetful`, and Mathlib's
  `Functor.mapDerivedCategoryFactors` and `Localization.lift`/`liftNatTrans`.
  The tensor dependency is the recorded `CochainTensorUniverses` module.

Sources opened: Stacks `sites-cohomology.tex` at `lemma-pullback-K-flat`,
`lemma-derived-pullback-composition`, `lemma-adjoint`; the current blueprint parent
`lemma-weil-pbc-completed-pullback-reduction.proof.md`; the node's eight proof steps.
The theorem docstring gives every step, including why restriction preserves K-flatness,
how the balanced maps descend, the unit argument for arbitrary derived adjuncts,
coefficient naturality and the successive and identity calculations.

Edge cases checked before drafting:

- φ = identity gives the canonical identity balanced comparison; arbitrary unbounded
  complexes and arbitrary derived maps are still quantified.
- ψ or τ the identity is allowed. `equal_index` explicitly uses the canonical unit;
  it does not discard this case or impose a strict equality of chosen functors.
- Zero complexes, zero ring sheaves, and the empty site require no nonempty or
  nontriviality binder, so are included with the same formulas.
- No flatness of S over B or S' over S is assumed. For example Z to Z[1/2] to F_3
  satisfies the hypotheses. Taking R = B = Z and S = F_p also allows nonflat S/B.
- Flatness and the multiplication-isomorphism assumption are substantive. Removing
  the latter, e.g. k to k[t] to k, produces the familiar extra derived self-Tor on
  the B side; it cannot be replaced by an unconstrained comparison map.
- Site object universe u and morphism universe v are independent, including the
  small pro-etale size pattern. Relative smallness in r is precisely the existing
  K-flat and sheaf-tensor convention, with no equality of these universes imposed.

Searches (2026-10-21):

- `msearch.py ... leanfinder "A flat ring sheaf extension with B tensor R S equal to S
  identifies derived scalar extensions and preserves adjunction transposes"`:
  eight hits about ordinary `ModuleCat` scalar adjunctions, tensor flatness and
  algebraic change of rings; none states this ring-sheaf derived comparison.
- `msearch.py ... leansearch "Derived extension restriction scalars flat ring sheaves
  compatible adjunction"`: eight hits including `ModuleCat.extendRestrictScalarsAdj`,
  its sectionwise Hom maps and `PresheafOfModules.sheafificationAdjunction`;
  underived ingredients, not this theorem.
- `msearch.py ... loogle '"SheafOfModules", "restrictScalars"'`: twelve hits for
  ordinary presheaf scalar restriction and its limit/colimit instances; no match.
  Earlier fully qualified `SheafOfModules.changeOfRings` was not a searchable
  Mathlib identifier, so the corrected quoted query above was run.
- `msearch.py ... grep 'derived.*[Ss]calar|[Ss]calar.*derived'`: one incidental
  prose hit in `Mathlib/Algebra/Ring/Submonoid/Pointwise.lean`, no theorem.
- `rg -n 'flat.coefficient|balancedComparison|reductionAdjunct|flatCoefficient|<item-id>'`
  in both project trees and `dag/lean_names_upstream.json`: no existing theorem;
  candidates inspected include `FlatExtendedCechComparison` (localized Cech
  complexes, a different statement), the pro-etale `ChangeOfCoefficients`, and
  `SuccessiveDerivedQuotientNormalization` (composition, not this restriction
  comparison). The latter is reused for all required coherent structure.
- The returned review requests a definition-node attachment for the already existing
  normalization data; this repair is described below. No mathematical statement
  correction, dependency-module repair or STATEMENT-DISPUTED flag is needed.

Validation: server compilation and delivery preflight are recorded below after completion.

Compilation diagnosis: the first source confirmation passed in 38.9 seconds, but
an initial dry run hit the fixed 60-second limit. A temporary profiler run passed
both sandbox and named-module checks (44.0 seconds for the named module) and showed
expensive automatically generated size/injectivity declarations for the large
comparison structure. The final module disables `genInjectivity`, `genSizeOf`,
`genSizeOfSpec`, and `genCtorIdx`, as existing ringed-coefficient interface modules
do. This removes unused datatype machinery without changing any mathematical
field, map, hypothesis or conclusion. The temporary profiler option was removed;
the development-only option warning is not present in the delivery source.

Final `scompile.py` validation: PASS with no errors or warnings. The private sandbox
file compiled in 16.6 seconds and the named library module compiled separately in
25.3 seconds, both under the unchanged 60-second limit. All compiles used the
prescribed wrapper; no global build, live-file edit or direct git command was run.


## New nodes

`def-pbc-successive-derived-scalar-normalization-data` registers the existing plain
`Modules`, `restriction`, `pure`, `Presentation`, `sectionTensor`, `squareComparison`
and `Normalization` declarations in
`Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`, with `existing: true`.
No source declaration is copied, renamed, changed, or selected. Its source is Stacks
03D7/03EK/06YY/0G7E/0D6D/07A6, as read in the module docstrings and source lemmas.
The statement defines data and equations; it does not assert existence of the data.
It lists the ordinary/derived universal pair, pure tensors, ordinary and derived
composition, inverse formula, K-flat computation and representative equations,
ordinary and derived adjunction units, restriction factorizations and composition,
unit composition, associativity, and coefficient-square pasting, matching every
field of the existing `Presentation` and `Normalization` structures.

Searches: LeanSearch returned ordinary `ModuleCat.extendRestrictScalarsAdj` and its
Hom/unit formulas (eight hits); LeanFinder returned presheaf derivation universal
objects and `SheafOfModules.QuasicoherentData` (eight hits); Mathlib grep for
`SuccessiveDerivedQuotient|structure Normalization|structure Presentation` in
Algebra/Homology returned zero hits. The node preserves their complete tool outputs.
Project/DAG grep finds the desired definitions only in the unchanged module, attached
as auxiliary declarations to `lem-sfb-successive-derived-quotient-normalization`,
whose main declaration asserts existence. No definition node names the general-site
normalization data. `def-sp-finite-free-direct-image-data` specializes to pro-etale
schemes and adds geometric balancing; it is not this notion. Blueprint search for
"successive derived scalar" returned only the different `thm-coef-finite-hom`.
The new node cites its underlying existing definition nodes and inherits the item's
chapter, unit and blueprint ancestor, placing the item first in `via`.

## Returned review repaired

At returned immutable head `25cfb5719a85`, L upheld the mechanical finding that
`lem-sfb-successive-derived-quotient-normalization` was added to `stmt_deps` although
the signature uses only its plain definition data. This packet replaces that added
statement edge with `def-pbc-successive-derived-scalar-normalization-data` and keeps
the theorem unchanged in `proof_deps`. `p` and `N` remain explicit parameters;
no `.choose` of the existence theorem appears. This is a new definition attachment
under stage-2 section 1(A), not a stage-2 FIX changing a landed statement dependency.
Current main has no `lean` record on this item, and its six base statement-dependency
edges are retained. Apart from the authorized `lean` and `stmt_deps`, all existing
node fields are byte-equivalent as JSON values to current main. The Lean file is
unchanged from the retained packet; the first requested saved-packet dry run passed
as `8c0266e0141` before this explicit semantic dependency repair.

## Second reading by NO

I reread the returned node, complete Lean file, and existing normalization definitions
in this repair session. No other agent was started, as the dispatcher explicitly
forbids it; this records my second reading, with the maintainer's independent reading
still required. The small site and independent universes, arbitrary ring sheaves
and maps, exactness `hflat`, multiplication isomorphism `hμ`, all derived objects and
arbitrary derived morphisms, balanced `ordinary_pure`, K-flat `representative`,
`adjunct`, `coefficient_naturality`, `successive`, and `equal_index` match the clauses
in the hypothesis/clause table above. No Lean mismatch was found; the dependency
classification identified by L is repaired by the existing-definition node.

For that new node, `Presentation` fixes the ordinary object and map data, additivity,
and the universal derived counit. `Normalization.ordinary_hom`/`ordinary_inv` give
exactly its balanced formulas; `derived`, `computed`, `intermediate_computed` and
`representative` give its derived and K-flat clauses; `ordinaryAdjunction`,
`ordinary_unit`, `right`, `right_factors`, `adjunction` and
`adjunction_normalization` give its restriction/adjunction clauses;
`restrictionComp`, `restrictionComp_sections`, `rightComp`,
`rightComp_normalization` give the normalized restriction comparisons;
`unit_comp`, `associative`, and `coefficient_naturality` give the final coherence
clauses. `squareComparison` is the specified concrete composite. There is no
existence assertion or theorem selection in the definition node. The existing
structure signature was copied verbatim, without `where`, as required by section 5.
Identity maps, zero ring sheaves/complexes, empty sites and arbitrary nonflat second
extensions are still included. No extra universe equality or hypothesis was added.


Repair validation: `scompile.py` passed cleanly for the unchanged item module
(private sandbox 16.6 s; named module 25.3 s). The first repaired-packet dry run
required each definition-node reference in its own `[id]` citation; I split the
combined K-flat/flat citation accordingly. This changes no mathematical text.

Final repaired-packet dry run: `deliver2.py ... --no-push` returned
`OK (dry run): commit 21a49ec24e9 passes the preflight and compiles`. It checked
the item and the existing normalization declaration attachment against live sources.
The packet contains exactly the item module, item node, new existing-definition node,
and this report. The prescribed delivery wrapper performs the final rebased push.
