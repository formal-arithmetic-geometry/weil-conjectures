## Worker report

Module: `Sheaf.Paper.CompletedScalarUnitAdjunction`; main declaration:
`AlgebraicGeometry.Scheme.CompletedScalar.completedScalarUnitAdjunction`.
One theorem, with `sorry`, states the item. All auxiliary declarations have real data:
they abbreviate recorded notions, assemble canonical compositions, or bundle the inputs
and conclusions of this one statement. No new node or dependency repair is needed.
The main theorem's docstring contains all nine DAG proof steps and their dependencies.
The DAG's mathematical statement and dependency lists are unchanged.

Hypotheses and notation, clause by clause:

- `A : Type (u+1)` and `[CommRing A]`, `d : AdicCoefficientDatum A`: `d.noetherian`,
  `d.finitelyGenerated`, `d.quotientTorsion`, `d.quotientPerfect`, `d.quotientFinite`
  render exactly the Noetherian, finitely generated, additive-torsion, finite and perfect
  quotient hypotheses. No completeness hypothesis on A is imposed.
- `T : Scheme.{u}`; `StrictScalarBalancing.topology T = proEtaleModelTopology T`
  is the published equivalent small model of the small pro-etale site. This uses the
  permitted size transport: no equality of the original object/morphism universes is
  imposed. Constant and completed rings are exactly `ring T d false/true`; `scalar T d`
  is the canonical limit-cone scalar map. Positive exponent n+1 is indexed by n.
- `D`, `TD`, `reduction`, `dres`, `tdres` and `rlim` are the existing actual unbounded
  derived categories, strict reductions, exact scalar restrictions and derived strict
  limits. They are not a diagram of objects in the derived category.
- `B : Balancing d` names the normalized rho and pullback comparisons supplied by the
  recorded strict balancing theorem. Its `ρ_computes`, `augmentation_equation`, and
  `PullCompatibility` retain tensor formulas, strict transitions and pullback balancing.
  This is a choice of already supplied normalized data, not a new hypothesis on a scheme
  or complex.
- `Operations d B f` contains the existing `PullCompatibility` (hence ordinary and
  diagram derived pullback and a,p,tau), the two ordinary right adjoints and adjunctions,
  and chi. `χ_normalized` fixes chi to the adjunction mate of a inverse, exactly the
  normalized flat scalar adjunction comparison. The theorem asserts these operations
  exist for every scheme morphism, and works for every choice of their presentations.

Conclusions, clause by clause:

- `CompletionFacts.criterion` identifies the published intrinsic local-completeness
  condition with invertibility of the *actual* quotient completion unit, for both rings.
  `closed` supplies completeness of completion for every ambient input. The equivalence
  conjunct `(H.restriction T).IsEquivalence` asserts restriction identifies the full
  complete subcategories, not the ambient categories.
- `lambda` is a natural isomorphism of derived strict-limit functors. `LimitNormalized`
  is its full universal-derived-unit equation, with the ordinary comparison
  `limitRestriction (scalar T d)`, characterized by the same compatible-family formula.
- `completionComparison d B T (lambda T)` is, by definition, lambda whiskered with
  reduction, followed by Rlim of rho, with functor associators. The theorem's ambient
  `L : D (ring T d true)` equation is `r(c^a_L) ≫ beta_L = c^0_(rL)`.
- `Operations.completedPull H b` is ordinary pullback then the published quotient
  completion, restricted to the full complete input category. `reconstruction b` is
  Rlim of the *recorded* strict pullback/reduction reassociation. The maps j are the
  corresponding `completionUnit.app` at ordinary pullback. Thus this uses exactly the
  quotient-completion model explicitly permitted by the node and its proof Step 4;
  it is not a second reduction or completion construction.
- `Comparison.φ`, `unit_normalized`, and `unique` assert existence and uniqueness of
  the natural isomorphism satisfying `r(j^a) ≫ phi = a ≫ j^0` on all complete inputs.
- `Comparison.reconstruction` is the displayed reconstruction equality, in Lean's
  left-to-right composition order: `r(r^a) ≫ lambda ≫ Rlim(q) = phi ≫ r^0`.
  `Operations.quotientComparison` is p followed by diagram pullback of rho, on strict
  towers before taking a limit.
- `Comparison.pushA`, `push0` assert direct-image preservation of completeness;
  `adjA`, `adj0` give the actual full-subcategory adjunctions. `homA`, `hom0` state their
  Hom bijections are precisely precomposition by j followed by the ordinary derived
  adjunction, with equality of the resulting morphisms.
- `hom_comparison` identifies these bijections under scalar restriction, phi and chi.
  `unit`, `counit` write their compatibility explicitly. `φ_complete`, `χ_complete`
  give the same comparisons as maps of full complete categories, with component
  equalities to the ambient maps. `mate` asserts the full adjunction comparison.
- `conjugation` states transport of adjunction conjugates for any other identified
  pair of adjunctions and compatible direct-image map. In particular take the other
  adjunction to be the composite-edge completed adjunction (and the composed one), or
  the identity adjunction: this is exactly preservation of the composition and identity
  maps defined as conjugates in the node. It uses Mathlib `conjugateEquiv` itself.
- Naturality in every complete-input morphism is built into all functors, natural
  transformations and natural isomorphisms. `change_input` also writes the displayed
  reconstruction equality after an arbitrary map `h : rL ⟶ L₀` to a constant complete
  object, using its induced reduction and completed-pullback maps. In particular it
  includes every isomorphism `rL ≅ L₀`, the identity and arbitrary changes of lift.
- Since `pushA` is a conclusion for every edge and complete target, take
  `L = ⟨O.rightA.obj K.obj, comparison.pushA K.obj K.property⟩` for any other edge's
  operations and complete K. All comparison assertions apply. No properness,
  boundedness, constructibility, etale origin, nonempty-site, nonzero-ring, or
  nontrivial-ideal condition occurs anywhere.

Dependency declarations read and used:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` through `ConstantCompletion.res`, `dres`, `tdres`.
- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, its actual coefficient
  sheaves and `completedReductionTower`; the equivalent small-site presentation is
  reused through the recorded strict balancing module.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `conjugateEquiv`.
- `Sheaf.Paper.PbcQbarCompletedPullback` publicly retains `CompletedPullback`:
  `AdicCoefficientDatum.completedPull`, `completionUnit`, `ordinaryToCompleted`.
  The main definition there is a further Qbar specialization; this item uses its retained
  ambient quotient-completion model, exactly as node proof Step 4 specifies.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleConstantRingDerivedPullback`, retaining the arbitrary ring-sheaf operations;
  small-site operation presentations come from strict balancing's `PullModel`.
- Size convention: explicit `u`, `A : Type (u+1)`, `Scheme.{u}`, and the published
  `proEtaleModelTopology`, never a new hypothesis equating site universes.
- `Sheaf.Paper.CompletedPullbackAdjunction`:
  `CategoryTheory.ConstantCompletion.completedPullbackAdjunction`.
- `Sheaf.Paper.ConstantCompletionEquivalence`: `equivalence`, `completion`,
  `completionUnit`, `quotientPresentation`, `derivedLimitRestriction`,
  `limitRestriction`, `koszul_quotient_reflector`; use these existing constructions.
- `Sheaf.CategoryTheory.DiagramSiteRealization`: `exists_diagramSite_realization`.
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`:
  `FlatRingedDiagramInput.flatRingedDiagramRestriction`, its normalized adjunct equation.
- `Sheaf.CategoryTheory.FlatScalarTowerLimitSquare`:
  `FlatScalarTowerLimit.flatScalarTowerLimitSquare`, its universal-unit normalization.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `proEtale_profinite_coefficient_inverse_image`, projection, identity and composition
  normalizations (retained in the strict balancing operations).
- `Sheaf.Paper.StrictQuotientScalarBalancing`: `Balancing`, `PullCompatibility`,
  `strictQuotientScalarBalancing`, and all its actual ring/site/reduction helpers.
- `Sheaf.Paper.CompletedDirectImageLimits`: `AdicCoefficientDatum.directImageRlimIso`,
  `push_complete`; `Sheaf.Paper.KoszulReconstruction`: `koszulReconstruction`;
  `Sheaf.CategoryTheory.RingedKoszulCompletionReflector`:
  `ringedKoszulCompletionReflector`, the additional stated proof dependency.

Edge cases checked by reading the formulas: I=0 (including an empty generating list),
I=A (zero quotient and completion), the zero ring, zero derived objects, empty schemes,
identity and composite edges, level n=0 representing exponent 1, all unbounded inputs,
and both identity and arbitrary isomorphisms of constant complete inputs. No dimension,
characteristic or nonemptiness constraint was introduced.

Searches (msearch.py; exact results retained in sandbox searches.jsonl):

- LeanFinder: “Restriction of scalars identifies completed pullback adjunctions preserving
  quotient completion units and strict reconstruction maps”: eight ordinary module scalar
  adjunction hits, including `ModuleCat.extendRestrictScalarsAdj`; no derived strict
  quotient-unit/reconstruction statement.
- Loogle: `CategoryTheory.Adjunction.homEquiv_unit, CategoryTheory.conjugateEquiv`:
  zero returned hits. Directly opened Mathlib's Mates source and used `conjugateEquiv`.
- Mathlib grep: `completion.*adjunction|adjunction.*completion`, CategoryTheory:
  zero hits.
- LeanSearch: “Restriction from completed adic ring sheaf coefficients to constant
  coefficients preserves completed pullback adjunction and its normalized quotient units”:
  eight ordinary sheaf pullback/sheafification/constant sheaf adjunction hits; no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for scalar/completion/restriction,
  `completion_restriction`, exact item id and proposed names: existing ordinary adic
  module results and the recorded `ConstantCompletion.completion_restriction`; the latter
  only identifies completion and units, without the normalized strict reconstruction and
  completed adjunction clauses of this item. No exact match or name collision.

Validation: scompile.py compiled the delivered module separately in sandbox and library
mode, cleanly, in approximately 11 and 10 seconds. Only the main theorem is postponed.
No statement dispute or correction.

## Second reading by NH

A fresh in-thread rereading compared the node and the final module clause by clause
(the dispatcher prohibits starting another agent; the maintainer provides the independent
review). It caught two gaps in the initial draft: the existence of ordinary operation
presentations was implicit, and composition/identity compatibility was only described
in prose. The final theorem explicitly supplies `Nonempty (Operations d B f)` for every
edge. `Comparison` now includes the full-category comparison maps with component
normalizations, the mate equation, and the explicit conjugate-transport equation.
The reconstruction order was checked from its source and target: Lean writes
`r(r^a) ≫ lambda ≫ Rlim(q) = phi ≫ r^0`. The change-of-input equation was checked with
arbitrary `h` and hence includes every isomorphism. The ordinary Hom equivalences,
unit/counit directions and all complete-subcategory lifts were read against their full
signatures; the complete theorem compiles after these changes. No new hypotheses on
schemes or complexes, and no source statement change, resulted.
