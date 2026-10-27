## Worker report

The module `Sheaf.Paper.ProperAlgClComparisonDomains` states
`AlgebraicGeometry.ProEtale.CondensedRing.properAlgClComparisonDomains` with proof
`sorry`. There are no new definitions, helper theorems, or new nodes. The node is
unchanged except for its `lean` record. The theorem docstring carries all six
steps of its accepted proof plan, with the cited DAG nodes.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
and the accepted extracted obligation in the assigned node. Paragraph (3) uses the
proper preservation theorem followed by a compactification; this item supplies
its separately extracted proper coefficient-change domains.

Hypotheses and objects, clause by clause:

| Node | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Field k, characteristic p > 0, p different from ell | `(p : ℕ) (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)` |
| Normed algebraic closure Omega | Existing `PadicAlgCl ℓ`, with its extended ell-adic norm; the same chosen model as both coefficient dependency interfaces. |
| Finite intermediate E with restricted topology | `(E : PadicAlgCl.FiniteIntermediateField ℓ)` and its existing subtype norm topology. |
| Z and T separated, finite type over k | The two `Scheme.{u}` binders, their `Over (Spec (.of k))` instances, and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances on both structure maps. |
| Proper k-morphism | `(f : Z ⟶ T) [f.IsOver (Spec (.of k))] [IsProper f]`. |
| A_E | `Profinite.continuousMapRingObj E`, continuous E-valued functions; the coefficient on Z is definitionally `padicSubfieldRingObj Z ℓ E`. |
| C, finite-subextension-valued continuous sections | `Profinite.padicAlgClRingObj ℓ`, whose recorded sheaf is `Profinite.padicAlgClCondensedRing ℓ`. |
| B, ALL norm-continuous sections | `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`. This is the universe-zero coefficient specialization of the recorded `continuousMapRingObjOfUniverse`. |
| Coefficients on W | Existing `condensedRingObj`, the underlying object of the recorded `coefficientRing`; no second pullback construction. |
| Ordinary unbounded derived internal modules | `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj R W))`. |
| K in Dbc(Z,A_E) | The explicit ambient `K` binder with `_hK : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) Z K`. |
| S_W, actual derived extension along a | `derivedExtendScalarsToPadicAlgCl W ℓ E`, definitionally `leftDerivedFunctor (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl W ℓ E))`. |
| J_W, actual K-flat extension along c | `algClTopologyScalarExtension ℓ W`, definitionally the total left derived functor of extension along `coefficientMap (algClTopologyInclusion ℓ) W`. |
| L | `(derivedExtendScalarsToPadicAlgCl Z ℓ E).obj K`. |
| P | `(moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) f).obj L`, expanded in the signature. |
| Q | `(moduleObjectDerivedPushforward (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).obj ((algClTopologyScalarExtension ℓ Z).obj L)`, expanded in the signature. |

The seven conjuncts are, in order: L bounded constant-model constructible over C;
P bounded constant-model constructible over C; `IsIso` of the specified chi;
J_Z L bounded constant-model constructible over B; finite Tor amplitude of J_Z L;
J_T P bounded constant-model constructible over B; Q bounded constant-model
constructible over B. Each endpoint is expanded using the terms above, with no
`let` binder or arbitrary comparison map. `DerivedCategory.finiteTorAmplitude _`
is the recorded predicate testing tensor against every module in degree zero.
No extra finite-Tor conclusion about P or Q is imposed.

The canonical chi is
`(derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app K`.
I read its construction in `ModuleObject.ChangeOfCoefficients`: it is the scalar
adjunction mate of `derivedComapLowerStarIso`. The equivalent geometric adjunct
is inverse `derivedPullIso` followed by S of the A_E-counit, exactly as specified
in the assigned node and in the recorded `QlbarDirectImageComparison` docstring.
The tensor comparisons come from the underived balanced tensor comparisons and
derived adjunctions. The imported coefficient projection cocycle supplies their
normalization. The finite-subfield flatness proofs required internally by this
published map are inferred existing facts: the theorem adds no flatness binder.
Nothing assumes flatness of C to B, equates C with B, or replaces J by an arbitrary
functor or equivalence.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the standing
  setting interface, used as explicit geometric binders rather than extra compactification data.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`, and their finite-valued
  section description.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`, `continuousMapRingObjOfUniverse`;
  specialized to the existing `continuousMapRingObj` for `PadicAlgCl ℓ : Type`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `coefficientRing_X`, `condensedRingObj`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, regular module,
  morphisms and forgetful functor.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward` (the existing total right derived
  functor of the full underived lowerStar), and the exported derived geometric adjunction.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`; the exact finite constant-model convention.
- `Sheaf.Paper.ConstantModelTorAmplitude`:
  `constantModelConstructibleFiniteTor_wellDefined`, exporting the recorded
  `DerivedCategory.finiteTorAmplitude` predicate from
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `Mod.derivedExtendMapDerivedCategoryAdjunction` and its generic actual K-flat
  `Functor.leftDerivedFunctor` construction.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.Paper.RingedCoefficientProjectionCocycle`:
  `SheafOfModules.RingedCoefficientProjection.ringedCoefficientProjectionCocycle`,
  with the publicly imported `RingedCoefficientProjectionData.comparison` normalized
  geometric counit-mate interface.
- `Sheaf.Paper.ConstructibleAlgClTopologyComparison`: `algClTopologyInclusionRing`,
  `algClTopologyInclusion`, `algClTopologyScalarExtension`, and
  `constructible_algCl_topology_comparison`. J reuses the already published helper
  belonging to this proof dependency; it is not defined again.

Proof dependencies are imported separately where not already statement imports:
`Mathlib.AlgebraicGeometry.Noetherian` (locally Noetherian and finite-type permanence),
`Mathlib.AlgebraicGeometry.AffineScheme` (affine compactness; quasi-separatedness is
also exported), `WeilConjectures.AlgebraicGeometry.ProperBasic` (`proper_basic`),
`Sheaf.Paper.FiniteCoefficientDescentTwoColimit` (`finiteCoefficientDescentTwoColimit`),
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`
(`derivedExtendScalarsToPadicAlgCl`,
`boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`),
`Sheaf.Paper.ProperBaseChangeRational`
(`properPushforward_boundedConstructible_rational`),
`Sheaf.Paper.QlbarDirectImageComparison`
(`isIso_derivedPushHom_padicAlgCl_of_boundedBelow`),
`Sheaf.Paper.ContinuousAlgClConstructibleTor` (`continuousAlgCl_bounded_finiteTor`),
and `Sheaf.Paper.ProperLocalizingContinuousAlgCl`
(`properLocalizingHypotheses_continuousAlgCl`). No dependency interface repair is needed.

Edge cases checked against the definitions: zero K and acyclic complexes are admitted;
empty Z or T is not excluded by any nonemptiness binder; finite stratifications allow
zero strata. E equal to Q_ell (the bottom intermediate field) is allowed without a
strictness condition. Identity proper maps are allowed, with the canonical mate's
unit normalization. Arbitrary finite degrees and arbitrary bounded cohomological
intervals are allowed. The coefficient and site universes are the existing framework's
`Scheme.{u}`, site object universe u+1 and morphism universe u, with abelian coefficients
in u+1; no universe equality restriction was added. Characteristic zero and p=ell are
excluded precisely as in the node. No statement dispute or correction was found.

Searches actually run (2026-10-24):

- msearch LeanFinder: `Proper pushforward preserves bounded constructible complexes under
  scalar extension of l adic coefficients`. Eight hits: condensed profinite free/solid
  objects, `CondensedMod`, `CondensedMod.IsSolid`, Chevalley constructible-spectrum
  results. None states these seven conclusions.
- msearch Loogle: `"Condensed", "rightDerived"`. Zero hits.
- msearch Mathlib grep:
  `(constructible|finiteTor).*(PadicAlgCl|continuousMapRing)|(PadicAlgCl|continuousMapRing).*(constructible|finiteTor)`.
  Zero hits.
- msearch LeanSearch: `Constructible domains for proper direct image under scalar extension
  from finite l adic fields through finite subextension valued algebraic closure to all
  continuous algebraic closure coefficients`. Eight hits, concerning
  `IntermediateField.extendScalars`, its membership/coercion lemmas and scalar tower
  instances for PadicComplex/algebraic closures. None states the item.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for proper/algebraic-closure
  comparison and constructibility found the cited endpoint and scalar comparison modules,
  including `ContinuousAlgClProperScalarComparison`. That theorem asserts invertibility
  of the A_E-to-B mate, not these seven domain conclusions, so it is not an exact match.
- Direct rg for the assigned node id in `lean/WeilConjectures` returned no match;
  rg for `properAlgClComparisonDomains`, `proper_algCl_comparison_domains`, and proper
  comparison domains in both source roots and `dag/lean_names_upstream.json` found no
  declaration. No existing declaration states the conjunction of this item.

Validation: the module is checked with the prescribed `scompile.py`; final dry-run
and delivery results are recorded below after the checks finish. No local/global
build or direct shared-repository mutation is used.

Compiler repair and final compile: the initial public import of the coefficient cocycle
exposed its general sheaf-instance caches, leaving `EssentiallySmall` universe constraints
unsolved on the pro-etale site. The cocycle is used for the proof/normalization explanation,
so its import now has ordinary proof visibility; the actual statement map is the existing
published `derivedPushHom`. Coefficient and operation universe arguments are explicit `.{u}`.
This changes no hypothesis, endpoint, chosen derived category, or comparison map. The
server then compiled the sandbox in 42.6 s and the delivered library module in 30.5 s,
both cleanly, with no diagnostics. Only the one theorem's proof remains `sorry`.

The prescribed `deliver2.py --no-push` completed successfully: the server preflight
passed and the module compiled (dry-run commit 9f0a3c3e146). Delivery contains exactly
the module, the assigned node's Lean record, and this report. Diagnostic scratch
probes are outside the delivered `lean/` tree and are not part of the packet.

## Repair of returned head 53991d78a7ca

H2 repaired: the item's `stmt_deps` now additionally names all five landed definition
nodes requested by the maintainer and the optional sixth definition node for the
coefficient inclusion appearing explicitly in chi:

- `def-sfb-algcl-topology-scalar-extension` owns
  `AlgebraicGeometry.ProEtale.algClTopologyScalarExtension`, the actual J_W.
- `def-sfb-algcl-topology-inclusion` owns
  `AlgebraicGeometry.ProEtale.algClTopologyInclusion`, the sectionwise C-to-B map.
- `def-sfb-derived-extend-to-qlbar` owns
  `AlgebraicGeometry.ProEtale.derivedExtendScalarsToPadicAlgCl`, the S_W used throughout
  the signature. Its existing proof dependency is retained as well.
- `def-sfb-derived-push-hom` owns
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom`, the canonical mate chi.
- `def-sfb-subfield-coefficient-ring` owns
  `AlgebraicGeometry.ProEtale.padicSubfieldRingObj`, the A_E coefficient on Z.
- `def-sfb-qlbar-subextension-to-qlbar` owns
  `Profinite.padicSubfieldRingObjToPadicAlgCl`, the finite-field inclusion in chi.

The records and corresponding source declarations were read. They are landed,
existing definitions; no new node, module or definition is supplied. Compared with
the current main node, the retained returned sandbox differed only in `lean` before
this repair. The accepted Lean module and its verbatim `lean.statement` are unchanged
from returned head 53991d78a7ca. Only these six additions to `stmt_deps` and this report
repair the return; no statement, proof plan, proof dependency, hypothesis or conclusion
was changed. The existing imports already expose these definitions.

The maintainer checked the mathematics and edge cases in the returned-head review;
this repair addresses the missing definition ownership citations exactly as requested.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
