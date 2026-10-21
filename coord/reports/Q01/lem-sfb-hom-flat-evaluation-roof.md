## Worker report

The module `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof` states the node as
`CategoryTheory.SfbFlatHom.evaluationRoof`, with proof `sorry`. The structure
`EvaluationRoof` packages its clauses; the preceding definitions are actual canonical
maps used in those clauses. No definition chooses unspecified mathematical data.
There are no new DAG nodes, dependency repairs, or statement changes.

Hypothesis and clause correspondence:

- A site small in the module universe is `{C : Type c} [Category.{v} C]`, with module
  and ring universe `max c v r`. Object, arrow, coefficient, and localization universes
  remain independent. `HasSheafify`, `WEqualsLocallyBijective`, `HasSheafCompose`, and
  the chosen derived localizations are precisely the ambient construction interfaces
  of the dependency modules. `ScalarHomModels M`, `ScalarHomTensorComparison μ`, and
  `ScalarInternalHomAdjunction α` are the recorded normalized models, quantified
  universally, not replacements for them or additional mathematical hypotheses.
- An arbitrary ring-sheaf morphism is `a : R ⟶ S`. Exact ordinary scalar extension is
  `PreservesFiniteLimits (M.scalar a).extension`; scalar extension is already additive
  and a left adjoint in `ScalarDerivedPair`, hence preserves finite colimits. Thus
  finite-limit preservation is exactly the remaining exactness condition.
- `P` and the node's complex `C` are the binders `P L`. Flat-term K-flatness is
  `CochainComplex.IsKFlatIndependentCoefficients ... P` together with
  `∀ n : ℤ, IsFlatOnSite ... (P.X n)`. There is no condition on `L`.
- `Q` is `DerivedCategory.Q`; `U` is `scalarDerivedRestriction a`, whose representative
  comparison is `scalarRestrictionComparison a`. The ordinary extension is fixed on
  objects and maps by `M.scalar a`, as is its universal derived counit.
- `J = I_R(C)`, `B = Hom(P,J)`, and `F` use the actual
  `coefficientHomResolution`, `homFixed`, and `resolutionUnit` in the strict models.
  `scalarTensor a` abbreviates `tensor(S,-)` with the actual restricted regular
  S-module. `numerator a P L` is the existing `comparison` component at that module;
  `denominator a P L` is exactly the existing `roofDenominator` component, hence
  `F(S tensor eta_C)`. These abbreviations introduce no alternative tensor or Hom.
- `comparison M μ a K L` defines the node's `c` by the closed transpose of
  `μ.inv` followed by scalar extension of evaluation, in the order `(Hom,P)`.
  `restrictedComparison M μ α a K L` is literally `U.map c ≫ (α.iso a).hom`.
- `EvaluationRoof.tensorIso` is the ordinary representative identification `ν`.
  Its `tensorIso_normalized` equation specifies every degree and actual section:
  the strict generator `s tensor x` maps to sheafified scalar `s tensor x`, transported
  only by `ScalarDerivedPair.extension_obj`. It is a natural isomorphism, rather than
  an arbitrary map or a choice from mere existence. The formula determines it uniquely.
- `exact_computes` asserts invertibility of the universal counit on every complex
  under exactness, not just on K-flats. `representative` composes this canonical
  counit, termwise restriction's comparison, and `Q(ν.inv)`. `sourceMap` additionally
  uses `coefficientHomResolutionIso` on `B`; `targetMap` uses the same Hom
  localization factorization on `S tensor C`. These maps are therefore precisely
  the source and target identifications mentioned by the node. Their invertibility
  follows from `exact_computes` and the displayed isomorphisms.
- `denominator_quasiIso` is the node's assertion that `v_S` is a quasi-isomorphism.
  `equation` is `Theta U(c) ≫ targetMap ≫ Q(v_S) = sourceMap ≫ Q(a_S)`;
  composition is written in Lean's left-to-right convention.
- `roof` is its equivalent inverse-denominator form, with the same transports.
  Its `hv` argument is only a proof about the already fixed `v_S`; the preceding
  clause supplies it, and `denominatorInverse` is exactly `inv (Q.map v_S)` with
  that proof installed as a local instance. No stronger hypothesis is assumed.
- `naturality` quantifies over arbitrary `K,K',L,L'` in the derived category and
  maps `f : K' ⟶ K`, `g : L ⟶ L'`. It states the naturality square for the actual
  `Theta U(c)`, so includes derived morphisms represented by inverse quasi-isos.
  The representative identifications are natural by their constituent functors
  and natural isomorphisms; thus this is also naturality of the displayed roof.
- `coefficients` states coefficient compatibility for every tower `R → S → T`,
  with the actual unit-normalized `scalarHomExtensionComp` on the source and both
  Hom inputs. These equations apply to both paths of any commutative coefficient
  square, including change of the base coefficient ring. Combined with `α.composition`
  they are compatibility for `Theta U(c)` as well. They are valid without flatness;
  the roof identities themselves require exactness as stated in the node.
- Neither `P` nor `L` has a boundedness hypothesis. There is no finite freeness,
  filtered diagram, or continuity assumption anywhere in the statement.

Dependency declarations used (including their defining modules):

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem;
  the normalized scalar interface retains this same universal change-of-rings pair.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `WeilConjectures.CoefficientClosedStructure`, its `transpose` and `evaluation`,
  and `CoefficientTensorModels` (via `M.closed` and `M.model`).
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (inside the recorded `scalarRestriction`).
- `Sheaf.Paper.DerivedInternalHomFilteredColimitData`:
  `Modules`, `tensor`, `tensorGenerator`, `homFixed`, `resolutionUnit`,
  `Normalized`, `comparison`, `roofDenominator`, all in
  `WeilConjectures.SfbHomFilteredColimit`.
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction` and its public
  `ScalarInternalHomData`: `scalarInternalHomAdjunction_exists`, `ScalarHomModels`,
  `ScalarHomTensorComparison`, `ScalarInternalHomAdjunction`, `ScalarDerivedPair`,
  `scalarDerivedRestriction`, `scalarRestrictionComparison`, `scalarComplex`,
  `scalarPairComplexComparison`, and `scalarHomExtensionComp`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`:
  `WeilConjectures.coefficientHomResolutionIso`, which is the fixed Hom localization
  factorization, not a newly selected representative isomorphism.

The statement dependencies' signatures and docstrings were read in their recorded
source files. All are available through the three direct imports, except that the
change-of-rings cochain interface is also imported explicitly. The proof dependencies
with no Lean record are `lem-weil-pbc-exact-functor-complex-cohomology`,
`lem-sfb-hom-kflat-chain-transpose`, and `lem-sfb-hom-scalar-chain-identification`;
the module docstring retains their precise roles without inventing their statements.
All other proof dependency modules are imported transitively by the normalized
scalar and Hom model modules. The parent filtered-colimit module is deliberately
not imported: it is a consumer of this node, and its helper names are not copied.

Edge cases checked mathematically before writing: identity coefficients `R = S`
(including the arbitrary normalized scalar presentation); zero and empty-site module
categories; `S` the zero ring sheaf; `P = 0` or `C = 0`; arbitrary unbounded `C`;
and `B = Hom(P,I(C))` possibly not K-flat. The last case is the reason the source
identification uses the exact-extension counit on all complexes, and the proof
resolves `B` before using the tensor representative model. No first-variable
finiteness or product/filtered-colimit interchange has been used.

Sources opened: Stacks sites-cohomology.tex at `lemma-internal-hom` (08J9) and
`lemma-RHom-well-defined` (0A95), and the current main-20261015 blueprint
`sk-def-sfb-dc-restricted-functors/lem-sfb-dc-hom-preserves.proof.md`, final paragraph.
The node explicitly records the roof calculation as an agent refinement rather than
claiming it is a verbatim Stacks lemma. Its six proof steps are reproduced in full
mathematical detail in the theorem docstring.

Searches (2026-10-21):

- `msearch.py ... leanfinder "Flat scalar extension derived internal Hom comparison
  equals evaluation normalized resolution roof"`: eight hits, including
  `LightCondensed.ihomPoints`, `CategoryTheory.Tor'_obj_map`, `Tor'_map_app`,
  `ProjectiveResolution.leftDerived_app_eq`, `Ext`, and `Functor.leftDerived_map_eq`.
  These are condensed ordinary internal Hom, Tor, Ext, or bounded resolution maps;
  none states the ring-sheaf, unbounded evaluation-roof identity.
- `msearch.py ... loogle "ModuleCat.extendRestrictScalarsAdj, CochainComplex"`:
  zero hits.
- `msearch.py ... leansearch "Flat scalar extension derived internal Hom evaluation
  comparison resolution roof"`: eight ordinary module extension/restriction Hom
  equivalence hits, including `ModuleCat.extendRestrictScalarsAdj_homEquiv_apply`,
  `HomEquiv.evalAt`, and `HomEquiv.fromExtendScalars_hom_apply`. Their signatures
  concern module Hom-sets; none is a derived sheaf-Hom roof. The ordinary restriction
  and scalar tensor constructions in the recorded project declarations were read.
- `msearch.py ... grep "internalHom.*(baseChange|extendScalars)|evaluation.*roof"
  CategoryTheory`: zero Mathlib hits.
- `rg` of the project roots for `evaluationRoof`, `flatEvaluation`,
  `flat.*[Rr]oof`, `[Rr]oof.*flat`, and the item id found no matching theorem.
  `grep -rn` of the item id in `lean/WeilConjectures` returned no hits.
- Inspection of `DerivedInternalHomFilteredColimit.lean` found the old
  `scalarComparison_restriction` chain square and the conditional finite-free-colimit
  result. Neither is this evaluation-defined unbounded flat roof identity. Its
  strict `comparison` and `roofDenominator` are already owned by the dependency
  data module and are reused directly. No parallel scalar comparison is defined.

No STATEMENT-DISPUTED issue was found. The node is unchanged outside `lean`.

## Second reading by Q01

A separate second pass by this same worker reopened the original node and the module;
the dispatcher forbids starting other agents, so this is not represented as an
independent worker's review. The maintainer performs the independent delivery review.
The comparison above was checked against each clause again: the order of evaluation
is `(B,P)`; `ν` is characterized by actual sheafification generators; `v_S` uses the
R-resolution of the R-complex `S tensor C`; the equality includes both source and target
transports; `hv` supplies only invertibility of this same denominator; and naturality
uses all derived maps rather than only chain maps. The coefficient transport on the
contravariant Hom input is the opposite of `scalarHomExtensionComp.inv`, while the
covariant input uses its hom. The first compile exposed max-universe inference at
`scalarTensor`; explicit universe arguments repaired it without identifying universes.
A subsequent elaboration bottleneck in the proof argument of the inverse-denominator
formula was removed by quantifying over its proof; proof irrelevance makes this the
same formula. No mathematical mismatch or excluded edge case was found.
