## Worker report

The module `Sheaf.Paper.ProEtaleScalarLocalModelRepresentatives` states
`AlgebraicGeometry.ProEtale.proetale_scalar_local_model_representatives` with `sorry`.
Two helpers implement the matrix codes belonging to this statement:
`sfbScalarPresentationModule` forms the actual quotient by the matrix image, and
`sfbIntegralScalarPresentationModel` applies the existing scalar-model functor.
Both contain real data, with no postponed proofs. No other theorem is introduced.

Source read: the full current blueprint file
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-integral-heart/sk-lem-int-integral-heart-triangulated.proof.md`,
especially paragraph (2), final sentence. I also read the item's five proof steps,
all statement dependency records, their recorded declarations and docstrings,
and the prescribed-local-model theorem used in proof step 4. No repair note exists
for this item in the read clone.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Bounded schemes, larger small-site/module universe | Explicit `universe u`; `T : Scheme.{u}`; `Scheme.ProEt.topology T` has site objects in `Type (u + 1)` and morphisms in `Type u`; modules use `Ab.{u + 1}`. No equality of site object and morphism universes is imposed. |
| Prime ell | `(l : ℕ) [Fact l.Prime]`. |
| Finite extension E/Q_l | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. |
| A = O_E | The recorded `Padic.coefficientExtensionIntegers l E`. |
| Condensed integral coefficients | The recorded `(integralModelCondensedCoefficients l E).X`, with its extending spectral norm. |
| R_U = p_U^* underline A | `condensedRingObj (integralModelCondensedCoefficients l E).X U`, the underlying object of the recorded `coefficientRing`. |
| Arbitrary T | `(T : Scheme.{u})`, with no scheme property instance. |
| Module sheaves or their internal equivalent | `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj ... T)`. The recorded section-module equivalence is imported. |
| Finite constant local model | The existing `HasFiniteConstantLocalModel ... T M`. Its definition uses a pro-etale cover, finitely presented point modules and the recorded module pullback. Point finite presentations are matrices over the global scalar ring. |
| Small representative set I_T | `(I : Type (u + 1))` in the first existential. |
| Actual representative modules | The function `F : I → Mod ...`. |
| Each representative has the property | `∀ t : I, HasFiniteConstantLocalModel ... T (F t)`. |
| Every member is represented | `∀ M, HasFiniteConstantLocalModel ... T M → ∃ t : I, Nonempty (M ≅ F t)`. These are coefficient-module isomorphisms. |
| Q = sum over m,n of n-by-m scalar matrices | On every cover member the second conjunct uses `∃ (m n : ℕ) (q : Matrix (Fin n) (Fin m) (Padic.coefficientExtensionIntegers l E))`. These are exactly the elements of the dependent sum Q. |
| Actual P_q = A^n/im(q) | `sfbScalarPresentationModule A m n q` is `ModuleCat.of A (ULift ((Fin n → A) ⧸ LinearMap.range q.mulVecLin))`. The lift only adjusts the carrier universe for the existing model functor. |
| Scalar extensions of these quotients | `sfbIntegralScalarPresentationModel l E U m n q` applies `FiniteConstantModel.modelFunctor A U` to that quotient. It forms the constant module sheaf, extends along the constant-function scalar map, then pulls back from the point. Its topology is precisely that of the coefficient definition. |
| These scalar labels give exactly the local condition | The second conjunct is an `↔` with a `Scheme.Cover.{u} Scheme.proetalePrecoverage T` whose module pullbacks are isomorphic to these models. |
| No arbitrary R_U-section matrices required | All matrix entries have type `Padic.coefficientExtensionIntegers l E`. |
| No Noetherian, qc, torsion-free or ell-invertible hypothesis | None occurs in the signature, predicate specialization or helper parameters. |

Recorded dependency declarations used, with their modules:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`,
  `upperStarFromPoint`; reached through public framework imports.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension` import: `Padic.coefficientExtensionIntegers`,
  `coefficientExtensionAbsoluteValue` and the finite-extension coefficient data.
- `Sheaf.Paper.IntegralModelSurjectiveClosedReflection`:
  `AlgebraicGeometry.ProEtale.integralModelCondensedCoefficients` and its
  commutative ring-object instance.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`
  and `Scheme.proetalePrecoverage`, through the public framework imports.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`, preserving
  the underlying sections and restrictions.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.IsFinitelyPresented`,
  the existing point-module finite-presentation interface used by the predicate.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar`.
- `Sheaf.Paper.FiniteConstantModelResolution`:
  `AlgebraicGeometry.ProEtale.FiniteConstantModel.modelFunctor`; its defining
  `scalarModules`, `constantFunctions` and `scalarToContinuous` were read.
  Its already landed owning definition node
  `def-sfb-finite-constant-model-data` is added to `stmt_deps` under the rule
  allowing added landed dependencies. This existing:true node explicitly records
  `FiniteConstantModel.modelFunctor` among its declarations. The two-term
  free-resolution theorem is not a statement dependency: the helper applies the
  plain definition directly and does not choose data from that theorem.
  No statement/proof field changes.
- Proof imports: `weaklyEtale_stability`, `Scheme.ProEt.weaklyEtale_localization`,
  `sfbCoefficientSectionsLocalization`, `cartesianCoefficients`, and
  `SheafOfModules.essentiallySmall_locally_prescribed`, from the five explicitly
  imported proof modules. `Limits.pullback`, `fst`, `snd` are available through
  these imports. The size-convention node has no declaration; explicit universes
  render it, as its recorded convention instructs.

Edge cases checked: m=n=0 gives the actual zero quotient; m=0 gives every finite
free scalar model; n=0 and arbitrary m still give zero. Matrices need not be
injective, square or invertible, so torsion and redundant relations are included.
T can be empty, and the existing cover interface permits the empty cover. Every
representative itself satisfies the property. No qcqs, Noetherian, characteristic
or ell-invertibility restriction occurs. The representative index uses the larger
site/section universe, rather than the smaller scalar universe.

Searches actually run:

- `msearch.py ... leanfinder`: "On a small pro etale site modules with finite
  constant scalar local models have a small family of isomorphism class
  representatives". Eight hits included smallness of finitely generated ordinary
  modules, light profinite sets, algebra categories and individual sheaf section
  sets; none states this theorem.
- `msearch.py ... loogle`: `SheafOfModules, CategoryTheory.EssentiallySmall`:
  zero hits.
- `msearch.py ... grep`: `HasFiniteConstantLocalModel|[Ee]ssentiallySmall|[Ff]inite[Pp]resentation`
  in `Algebra/Category/ModuleCat/Sheaf`: five hits, all finite-presentation
  predicates in `Quasicoherent.lean`, with no representative-family statement.
- `msearch.py ... leansearch`: "A small family of scalar finite presentations
  supplies representatives for sheaves with finite constant local models on a
  small site": eight hits, all sheaf finite-presentation interfaces.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for all three proposed declaration names:
  no hits. A node-id search of `lean/WeilConjectures` also found no declaration.
- Project keyword searches located the existing `HasFiniteConstantLocalModel`
  and `FiniteConstantModel.modelFunctor`; these are used, not copied. Searches
  for sigma matrix codes, `range.*mulVecLin` and scalar quotient constructions
  found local Smith/fibre-cokernel comparisons, not this theorem or these helpers.
- The existing `LocallyPrescribedModulesSmall` statement concerns arbitrary
  prescribed slice modules and is the proof dependency, not an existing exact
  specialization of this pro-etale scalar statement.

No new node, dependency module, correction or dispute is needed. The helpers
belong to this node's matrix-code clause and are listed in `lean.declarations`,
as permitted by the missing-helper instruction.

Validation: `scompile.py` compiled this file in sandbox and library modes,
respectively 4.2 s and 4.8 s, with no errors or unexpected warnings.

## Second reading by N5

This is a second pass by the same dispatcher worker; no sub-agent was started,
as the task prohibits that. The maintainer supplies the independent review.
I reread the source paragraph, full node and final Lean signature. The first
conjunct gives the small family, requires membership for every representative
and covers every member by a module isomorphism. The second records the scalar
matrix clause in both directions on an actual pro-etale cover. The helpers
take scalar entries and form the quotient before scalar extension. The existing
predicate and ordinary module pullback are used verbatim. The normed-field
instance in the model helper is exactly the one in the integral coefficient
definition; server compilation verifies the dependent types agree. The index
universe retains the small-site size convention. No missing/added hypothesis,
dropped zero/torsion case, hollow definition or proof was found. The only final
change from this reading was listing all three declarations in the module docs.

## Return repair (H2, 2026-10-22)

The return on immutable head `1490bc7e9445` requested replacement of the added
`lem-sfb-finite-constant-model-two-term-free-resolution` statement dependency with
`def-sfb-finite-constant-model-data`. I read the current landed definition node,
its existing:true record and the `modelFunctor` definition and docstring in
`Sheaf.Paper.FiniteConstantModelResolution`. The definition node owns that exact
functor, built by scalar realization, constant sheafification, scalar extension
and inverse image from the point. I replaced the added dependency and updated
this report and `lean.note`. The Lean module, theorem signature, helpers, natural
language statement and proof fields are unchanged. Comparing against current
main leaves only `lean` and this one added definition dependency changed.

The saved packet first passed `deliver2.py --no-push` (commit `2caadfcac64`); that
mechanical pass did not address the returned ownership error. The repaired packet
passed `scompile.py` in sandbox mode (3.5 s) and library mode (5.3 s), with no
errors or unexpected warnings. The final self-check confirmed the byte-identical
Lean module, verbatim recorded signature, definition-node ownership and exactly
the authorized node field changes. No other returned points exist.
