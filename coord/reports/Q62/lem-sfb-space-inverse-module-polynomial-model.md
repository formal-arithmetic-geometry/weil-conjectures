## Worker report

Item: `lem-sfb-space-inverse-module-polynomial-model`, Q62, 2026-10-24.
Module: `Sheaf.AlgebraicGeometry.SpaceInverseModulePolynomialModel`.
Main declaration: `AlgebraicGeometry.AlgebraicSpace.inverseModulePolynomialModel`.

The module states the node with a `sorry` proof. Its auxiliary definitions give actual
chart evaluation, derived chart sections, principal localizations and scalar changes;
the named additivity obligation `inverseModuleChartSections_additive` also has `sorry`,
with its source and full elementary proof in its docstring. All definitions have real
data. The helpers are constructions belonging to this node's model, rather than new
notions or alternate definitions of quasi-coherence, flatness, derived limits or K-flatness.
All ten public declarations are recorded in `lean.declarations`.

The base is the existing `Spec (.of (ULift.{u} ℤ))`. A ring carrier and its module carriers
are in universe `u`; the algebraic-space small ringed model and independent sheaf-derived
Hom universe `w` are those of the already recorded dependency. Ordinary module derived
categories use the existing small-Hom Grothendieck-abelian instance in universe `u`.
No equality of site-object and coefficient universes is imposed. Both implicit-variable
options are disabled.

Hypothesis and clause correspondence:

| Node phrase | Lean rendering |
| --- | --- |
| Commutative inverse sequence indexed by positive integers | `A : ℕ → CommRingCat.{u}`, `r : ∀ n, A (n + 1) ⟶ A n`; Lean index `n` is paper index `n+1`. |
| Surjective transitions | `hsurj : ∀ n, Function.Surjective (r n)`. |
| Locally nilpotent kernels, explicitly elementwise | `hnil : ∀ n a, (r n) a = 0 → IsNilpotent a`; no uniform exponent is assumed. |
| A is the inverse limit | `c : Cone (Functor.ofOpSequence r)`, `hc : IsLimit c`; coefficient ring is `c.pt`, projections are `c.π.app (op n)`. |
| Algebraic space X over Spec A | `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`, `f : X ⟶ schemeSpace (inverseModuleSpec c.pt)`. |
| Separated and finitely presented | `hsep : MapIsSeparated f`, `hfp : ProperQuotFinitePresentation f`; the latter is local finite presentation, quasi-compactness and quasi-compact diagonal. |
| Actual infinitesimal fibres X_n | `properQuotFibre f (inverseModuleTest c n)`, using the ring-limit projections and actual sheaf fibre products. |
| M_n is a module on X_n | `M : ∀ n, (properQuotFibre f (inverseModuleTest c n)).Modules`. |
| Quasi-coherent, finitely presented | `hqc`, `hfin`, with existing `SheafOfModules.IsQuasicoherent` and `.IsFinitePresentation`. |
| Flat over A_n on étale scheme charts | `hflat : ∀ n U, ((schemeRestriction _ U).obj (M n)).IsFlatOver (...)`; the base map is the Yoneda preimage of the specified fibre projection. This is the dependency's affine-local predicate, equivalent to the required stalk condition. |
| Proper support through a closed immersion and finite-type QCoh module | `hsupp : ∀ n, ∃ Z i, IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left) i.hom.hom ∧ MapIsProper (i ≫ properQuotSnd ...) ∧ ∃ G, G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M n)`. |
| Specified reduction isomorphisms | `e : ∀ n, (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj (M (n+1)) ≅ M n`. |
| Modules regarded on X by direct image, with canonical quotient transition | Existing `inverseModuleDerivedTerm`, `inverseModuleQCohTerm`, `inverseModuleDerivedTransition`, unchanged from the recorded dependency; its transition is the specified adjoint/counit composite followed by `e n`. |
| K in D_QCoh is the homotopy inverse limit | `hq` certifies the pushed terms' quasi-coherence; `HasProduct`, `K : X.DerivedQCoh`, `p`, `δ`, `hK : IsDerivedLimitTriangle (...) K p δ` specify precisely the product triangle and canonical transition. Products are in `X.DerivedQCoh`. Existence and certificates are supplied by `inverseModuleDerivedLimit`, not extra mathematical assumptions on the sequence. The statement holds for every triangle so specified. |
| Affine étale scheme chart U=Spec B to X | `B : CommRingCat.{u}`, `a : schemeSpace (inverseModuleSpec B) ⟶ X`, `ha : IsEtale a.hom.hom`. |
| Its induced A-algebra structure | `β : c.pt ⟶ B`, `hβ : a.hom.hom ≫ f.hom.hom = yoneda.map (inverseModuleSpecMap β)` identifies it with the structure morphism. This is the induced action, not an independent arbitrary action. |
| Finite polynomial presentation P to B as A-algebras | `d : ℕ`, `π : MvPolynomial (Fin d) c.pt →+* B`, `hπ : Function.Surjective π`, `hπA : π.comp MvPolynomial.C = β.hom`. A ring map commuting with coefficients is exactly the stated A-algebra map. |
| Bounded-above finite-free complex E over P | Existential `E : CochainComplex (ModuleCat (MvPolynomial (Fin d) c.pt)) ℤ`, `∃ b, E.IsStrictlyLE b`, and `∀ i, Module.Free P (E.X i) ∧ Module.Finite P (E.X i)`. |
| E represents RΓ(U,K) after restriction to P | `Nonempty (DerivedCategory.Q.obj E ≅ ((ModuleCat.restrictScalars π).mapDerivedCategory).obj ((inverseModuleChartDerivedSections ...).obj K.obj))`. |
| The same E localized at every f | `∀ g : MvPolynomial (Fin d) c.pt`, `inverseModuleLocalizeComplex E g` is actual termwise extension along `P → Localization.Away g`. No replacement complex is chosen independently for different g. |
| Localized representation on Spec B_bar(f), restricted to P_f | `Nonempty (Q.obj (inverseModuleLocalizeComplex E g) ≅ inverseModuleLocalizedPolynomialSections ... g K.obj)`. The latter uses the actual localized chart `Spec (Localization.Away (π g))` and the canonical ring map `IsLocalization.Away.map ... π g : P_g → B_bar(g)`. |
| Both representations preserve the action of A | The first is an isomorphism in `D(P)` and the second in `D(P_g)`; restricting along `MvPolynomial.C` or its composite with `P → P_g` makes them A-linear. `hπA` and `hβ` fix that action to the original base. |
| E and E_f are K-flat over A in the stated sense | Two explicit quantifiers `∀ L : CochainComplex (ModuleCat c.pt) ℤ, L.Acyclic → (CochainComplex.mapBifunctor L (...) (MonoidalCategory.curriedTensor _)).Acyclic`, using the respective real scalar-restriction complexes. This is the total tensor complex, not degreewise tensor exactness alone. |
| E_f tensor_A R computes derived scalar extension for every A-algebra R | `∀ (R : CommRingCat.{u}) (ρ : c.pt ⟶ R)`, `Nonempty (Q.obj (((ModuleCat.extendScalars ρ.hom).mapHomologicalComplex ...).obj (inverseModuleLocalizedBaseComplex ...)) ≅ (ModuleCat.ordinaryDerivedExtendScalars ρ.hom).obj (...derived sections restricted to A...))`. Every ring map is allowed, with no flatness, finiteness or surjectivity condition. |

`inverseModuleChartSections` is the composite of the existing inverse small-module
restriction equivalence, `SheafOfModules.evaluation` at the actual chart, and scalar
restriction along `(Scheme.ΓSpecIso B).inv` (transported by the chart's specified spectrum
isomorphism). Its right derived functor computes unbounded sections. In particular it
uses actual sections and the actual B-action, with no arbitrary section functor supplied
as an assumption. `inverseModuleLocalizedChart` uses the canonical spectrum localization
map, whose representable étaleness follows from the existing scheme-test theorem.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`, `Scheme.ΓSpecIso`; `def-weil-size-convention` is the documented universe
  convention, without its own object declaration.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `EtaleSite`, `structureSheaf`, `Modules`, `isEtale_comp`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, used through the existing `properQuotFibre`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the unchanged
  `SheafOfModules.IsQuasicoherent` specialization (Mathlib's general predicate).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  `moduleDirectImage`, `moduleTensorAdjunction`, fixed by `ModuleDirectImageModel`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, with its affine-local/stalk equivalence explained in source.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotFinitePresentation`,
  `properQuotFibre`, `properQuotFst`, `properQuotSnd`, `properQuotFibreMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`,
  `MapIsProper` and the local finite-presentation/finite-type definitions they use.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.SpaceInverseModuleDerivedLimit`: `inverseModuleSpec`,
  `inverseModuleSpecMap`, `inverseModuleTest`, `inverseModuleTestMap`,
  `inverseModuleDerivedTerm`, `inverseModuleQCohTerm`, `inverseModuleDerivedTransition`,
  `inverseModuleDerivedLimit`; its imports supply `DerivedQCoh`, `SmallModules`,
  `smallModuleEquivalence` and `IsDerivedLimitTriangle`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.C`; the recorded
  universal-property declarations `MvPolynomial.aeval` and `algHom_ext` were read too.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`:
  `representable_etale_scheme_tests`, specifically its equivalence between representable
  étaleness of a scheme Yoneda map and étaleness of the scheme map.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.ordinaryDerivedExtendScalars`, normalized by its universal pair and K-flat
  comparison. This is already the proof-dependency node `lem-pur-derived-change-of-rings`.

The last two owners are already landed nodes with usable Lean records and are added to
`stmt_deps`, as authorized for existing landed notions. No dependency node is changed.
All recorded proof-dependency modules available locally are imported, using plain imports
when they are needed only for the proof. Proof-only nodes without a recorded declaration
have no module to import: fp-qcqs-source, inverse-module-perfect-tests,
perfect-to-pseudocoherent-tests, pseudocoherent-tests-relative,
relative-pseudocoherence-etale-locality and flat-ambient-relative-pseudocoherence.
Their proof steps remain explicitly described in the main declaration's docstring.

Edge cases checked against the statement and source:

- `d=0`: the variable set is `Fin 0`; polynomial constants still give the specified
  coefficient map. No positive-variable hypothesis appears.
- `g=0`: the principal localization and the corresponding affine scheme are zero/empty;
  the chart construction is still étale and all comparison expressions typecheck.
- `g=1`: localization at a unit is permitted without a nonunit condition; the quantified
  base-change assertion covers this case and hence the original model.
- Zero ring, empty X/chart, zero modules and zero complex: no nontriviality, nonemptiness,
  nonzero-rank or nonzero-complex assumptions are introduced. The zero complex is free
  of rank zero in every degree and bounded above.
- Elementwise nilpotence is retained; it is not replaced by a nilpotent ideal or a
  Noetherian/adic-completeness assumption.
- Arbitrary base map `ρ` is allowed, including identity, zero-target and nonflat maps.
- The derived-limit terms and transition maps are those of the dependency; there is no
  assumed exactness or boundedness of a chart-section functor and no assumed flatness of X/A.

Searches performed before writing (2026-10-24):

- `msearch.py ... leanfinder "Compatible infinitesimal flat coherent modules on algebraic
  spaces admit a bounded above finite free polynomial model on affine charts and their
  localizations"`: 8 hits on scheme/ring flatness and smoothness; no matching theorem.
- `msearch.py ... loogle "MvPolynomial, CochainComplex, Module.Free"`: 0 hits.
- `msearch.py ... grep "polynomial.*[Mm]odel|[Mm]odel.*polynomial"`: 7 hits on ring-extension
  presentations and unrelated model-theoretic/dialectica constructions; no match.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for the exact node id,
  `inverseModule.*[Pp]olynomial` and `polynomial.*[Mm]odel`: no existing declaration for
  this node; unrelated duality, nodal and representation-theory polynomial models.
- Further `rg` searches for derived sections, chart evaluation, scalar restriction,
  K-flat tensor conditions, principal localization and finite-free complexes located
  the recorded derived-module calculus, actual sheaf evaluation, small-model equivalence,
  ordinary derived change-of-rings, and Mathlib's `Localization.Away`/`IsLocalization.Away.map`.
  `SpaceAffineHomComparison` concerns global sections along a map to an affine base;
  `ModuleDerivedEvaluationSlice` concerns nonnegative derived evaluation/slice comparison.
  Neither states this polynomial model or supplies the particular spectrum-coordinate
  chart composite used here. The helpers reuse their underlying existing constructions.

Sources opened: spaces-flat.tex at `lemma-relative-pseudo-coherence` and the entire
polynomial-chart paragraph in `lemma-finitely-presented`; more-morphisms.tex at
`lemma-qcoh-relative-pseudo-coherence-characterize` and
`lemma-check-relative-pseudo-coherence-on-charts`; spaces-more-morphisms.tex at
`lemma-qcoh-relative-pseudo-coherence-characterize`.

No STATEMENT-DISPUTED issue, statement correction, new definition node or dependency
interface repair is needed. The item node changes only in `lean` and the two permitted
additions of already landed statement dependencies.

Validation: the full delivered module compiled through the prescribed `scompile.py`,
both as a sandbox module and under its final library module name, in 3.8 and 4.4 seconds.
No errors or unexpected warnings. Both theorem proofs remain `sorry` as required.

## Return repair: F, immutable head 7e3bc800d221

The complete return is: "F: reviewer did not provide a full independent review
document; please re-read and re-push." There are no other numbered findings for this
item. This repair replaces the short second-reading paragraph with the full reread
below, including all binders, all conclusion clauses, the definitions' actual data,
source checks, edge cases, and the distinction between statement and proof obligations.
The module documentation now lists all constructions and both postponed statements so
that the reviewer can locate every declaration without reconstructing the interface.

The worker has reread the retained delivery, the current item node and dependency
sources. The current node has no landed Lean record; its statement agrees verbatim
with the sandbox. Against the current node the only differences are `lean` and the
previously documented two additions to `stmt_deps`. The theorem signature and all
helper data are unchanged. This is a documentation repair, not an unchanged re-push.
The delivery wrapper refreshes the server base and builds the new commit on that base.

Review authorship: this is the dispatched worker's full reread. It is supplied as a
complete document for the maintainer's renewed independent review, not as an assertion
that the worker is an independent reviewer. The dispatcher explicitly prohibits
starting other agents and assigns independent review to the maintainer. No reviewer
identity, independent verdict, or maintainer-owned review field is fabricated here.

## Second reading by Q62

Scope: the complete retained Lean module and node, the node's source places, the
recorded derived-limit signature and transition definitions, the actual full D_QCoh
subcategory definition, finite-presentation predicate, derived-limit triangle
predicate, and normalized ordinary derived scalar extension. The correspondence table
in the Worker report is part of this reread; the checks below explain why its
nontrivial entries have the required meaning. Result of this worker reread: no
mathematical mismatch found; no statement correction or dependency repair proposed.

### Source and hypothesis audit

1. In `spaces-flat.tex`, `situation-existence` supplies the surjective inverse ring
   sequence with elementwise nilpotent kernels, separated finitely presented X,
   finitely presented quasi-coherent modules flat over the stages with proper support,
   and compatible reductions. `lemma-compute-what-it-should-be` is the derived-limit
   prerequisite; `lemma-relative-pseudo-coherence` is 0CX7. The polynomial-chart
   paragraph of `lemma-finitely-presented` (0CX9) chooses a smooth ambient presentation
   and a bounded-above finite-free resolution of its derived pushforward. A finite
   polynomial presentation is such a smooth ambient presentation. The proof's later
   replacement by a principal localization is exactly why a single model and its
   localized models are needed here. The item isolates this construction, not the
   final open-neighborhood conclusion of 0CX9.
2. `A`, `r`, `hsurj`, `hnil`, `c`, `hc`: n=0 corresponds to source index 1, so every
   transition and every module occurs and no fictitious stage 0 is required. The
   kernel condition is `r n a = 0 → IsNilpotent a`; no fixed nilpotence exponent,
   nilpotent ideal, completeness, adic structure, or Noetherian hypothesis appears.
   `IsLimit c` identifies the actual coefficient ring `c.pt` with the inverse limit,
   rather than merely assuming compatible maps into the stages.
3. `X`, the derived-category instance, `f`, `hsep`, `hfp`: the ambient base is the
   existing Spec of the universe lift of Z. The actual structural map is f.
   `ProperQuotFinitePresentation` is local finite presentation, quasi-compactness,
   and quasi-compactness of the diagonal. It does not assert properness or flatness
   of X over A. The `HasDerivedCategory.{w}` instance selects the existing unbounded
   derived category and retains its independent Hom universe; it imposes no
   cohomological boundedness on K.
4. `M`, `hqc`, `hfin`, `hflat`, `hsupp`: M lives on the actual sheaf fibre products
   through `properQuotFibre`. Both quasi-coherence and finite presentation use the
   recorded module predicates. Flatness is checked on every etale scheme chart
   over the actual stage-base projection; it is not flatness over X or over A.
   The support witness has a representable closed immersion, a proper composite
   to the stage base, a finite-type quasi-coherent G, and an isomorphism of its
   direct image with M. All four conjuncts and the isomorphism are present. The
   witness is not replaced by properness of X or an arbitrary closed subset.
5. `e`: this is tensor pullback along the specified successive fibre map, with
   orientation M_(n+1) restricted to X_n isomorphic to M_n. It uses the recorded
   `moduleTensorPullback`, not the ordinary sheaf pullback or an arbitrary arrow.
6. `hq`, the product instance, `K`, `p`, `δ`, `hK`: `DerivedQCoh` is the full
   subcategory of the unbounded module-sheaf derived category with quasi-coherent
   cohomology. It is not the derived category of the abelian category QCoh.
   The term is the degree-zero direct image of M_n along the fibre immersion.
   The transition is `inverseModuleDerivedTransition`, whose underlying map is
   the adjoint/counit quotient map followed by `e n`. The product is taken in that
   full subcategory. `IsDerivedLimitTriangle` means the triangle with this product
   and its 1-minus-shift endomorphism is distinguished. Thus hK fixes the canonical
   transition; it is not a hypothesis about an arbitrary inverse system.
   The existing `inverseModuleDerivedLimit` has exactly the preceding tower and
   module hypotheses and supplies hq, product existence and the triangle. These
   binders expose the choice of the K named by the node, rather than requiring
   another finiteness or acyclicity property of the input. The statement applies
   to every such triangle and makes no choice-dependent conclusion about p or δ.
7. `B`, `a`, `ha`, `β`, `hβ`: the chart is an actual affine scheme chart etale over X.
   The equation hβ identifies its composite to Spec A with the spectrum of β.
   Hence β is precisely the induced A-action on B, not an independently selected
   action. No surjectivity or cover condition is imposed on this individual chart.
8. `d`, `π`, `hπ`, `hπA`: `Fin d` is the finite variable set, π is surjective,
   and its restriction to constants equals β. This is exactly a surjective
   A-algebra presentation. In particular d=0 is allowed. The statement neither
   assumes a finite presentation ideal nor replaces the given presentation by a
   more convenient one.

The relative-to-affine step was checked in `spaces-more-morphisms.tex`,
`lemma-qcoh-relative-pseudo-coherence-characterize` (0CSX), including the quantifier
on all affine etale charts. In `more-morphisms.tex`,
`lemma-qcoh-relative-pseudo-coherence-characterize` identifies derived sections with
the module object underlying the affine closed pushforward, and
`lemma-check-relative-pseudo-coherence-on-charts` (09UU) assumes a closed immersion
and a flat locally finitely presented ambient scheme. Polynomial affine space has
these properties. Thus the proof route needs no unmentioned flatness of X/A.

### Construction and conclusion audit

1. `inverseModuleAffineChart` packages the supplied a and its etaleness proof as
   a site object. `inverseModuleLocalizedChart` composes a with the spectrum map
   of `B → Localization.Away b`; it is the actual principal-open chart. Its
   etaleness is the composition of the existing scheme localization instance and
   the recorded representable-etale scheme-test comparison. No arbitrary chart
   or mere existence witness is selected.
2. `inverseModuleChartSections` first transports through the inverse of the
   existing small-module equivalence, then evaluates the original ringed-site
   module at T. Its scalar restriction uses `ΓSpecIso.inv` followed by
   `e.hom.appTop`; the direction is B to the ring of sections on T. For the
   spectrum chart e is the identity. Thus this construction gives actual sections
   with their B-action. Its named additivity theorem is the only supporting sorry;
   its docstring gives the proof by composition of the additive equivalence,
   sectionwise evaluation and restriction of scalars. The derived functor uses
   the existing K-injective `rightDerivedFunctor`, not a freely assumed functor.
3. The existential E precedes every g and R. It is a Z-indexed cochain complex
   over P, bounded above by `∃ b, E.IsStrictlyLE b`. Each term is both `Module.Free`
   and `Module.Finite`, hence finite free, with no fixed rank required across
   degrees. The first comparison is an isomorphism in D(P) with RΓ(U,K)
   restricted along the specified π. It does not merely identify cohomology groups.
4. `inverseModuleLocalizeComplex E g` is termwise scalar extension along P to P_g.
   Its definition contains no existential replacement for E_g. The localized
   sections object uses the chart with coordinate ring B_(πg) and restriction
   along `IsLocalization.Away.map ... π g : P_g → B_(πg)`. The localized comparison
   is an isomorphism in D(P_g). These two category-valued comparisons retain the
   actions of A through the constants and localization maps. No compatibility
   between independently chosen isomorphisms beyond the node's stated A-linearity
   is asserted or assumed.
5. The global and localized coefficient complexes restrict scalars along A to P
   and A to P to P_g respectively. Both K-flatness clauses quantify over every
   acyclic, possibly unbounded, A-complex L. `CochainComplex.mapBifunctor` with
   `MonoidalCategory.curriedTensor` forms the total tensor complex with its usual
   signs and direct-sum totalization. The result is required to be acyclic. Thus
   these clauses state K-flatness over A, not just flatness of the terms over P,
   and not a statement restricted to bounded L.
6. The last clause quantifies over every `R : CommRingCat.{u}` and every `ρ : A ⟶ R`.
   The left side is the image under Q of termwise extension of the same localized
   coefficient complex. The right side applies the recorded normalized ordinary
   derived extension along ρ to the same localized section object restricted to A.
   The comparison is in D(R), without flatness, finite type or surjectivity of ρ.
   `ordinaryDerivedExtendScalars` is selected from a universal derived pair with
   its K-flat comparison, so this is the actual derived scalar extension rather
   than an arbitrary functor or a bare choice of a naturally isomorphic object.
7. Every definition has explicit data; neither of the two sorry proofs supplies
   arbitrary object data. All helpers are listed in `lean.declarations`, have
   source/blueprint docstrings and belong to this node's construction. There is
   no alternate QCoh, derived-limit, finite-presentation, or localization notion.
   The main docstring gives the source-based six-step proof for the future stage-3
   worker. Proof-only imports remain ordinary imports; all signature dependencies
   are publicly imported. All variables and both universes are explicitly bound.

### Edge-case findings and repair outcome

- At d=0 the constants map and polynomial presentation remain well typed; no
  positive-variable hypothesis is hidden in the result.
- At g=0, and more generally when πg is nilpotent, the localized chart may be empty.
  The real localization and its etale composite still exist; sections over the
  empty chart vanish. The statement imposes no nonzero-ring or nonempty-chart
  condition. A nonzero P_g with zero B_(πg) simply asks the model to become acyclic.
- At g=1 the last comparison is included by the universal quantifier. The identity
  coefficient map ρ, a nonflat map, and the map to the zero ring are all included.
- Empty X, zero M_n, the zero complex, and rank-zero terms are permitted. No
  strict positivity of a rank, dimension, or bound is introduced.
- Nilpotence is elementwise for every transition. No finite-index truncation,
  uniform exponent, or requirement on a kernel of A to A_n is inserted.
- R and the coefficient rings share the prescribed coefficient universe u;
  only the sheaf-derived Hom universe w is independent. No test-algebra universe
  below the base is introduced, and no equality involving w is assumed.

No mathematical defect was found by this worker reread. The concrete repairs are
this complete review-support document and the module's declaration index. The
independent reviewer must still make and record their own judgment on the new
immutable delivery head; this report does not replace that judgment.

Repair validation (2026-10-24): the revised module was compiled again with the
prescribed `scompile.py`, both under its sandbox name (12.8 seconds) and final
library module name (8.6 seconds). Both checks completed without errors or
unexpected warnings. A direct comparison also confirms the node's `lean.statement`
is exactly the unchanged theorem signature, its JSON has indent 1 and a final
newline, every Lean line is at most 100 characters, and the only two sorry tokens
are the two named theorem proofs.
