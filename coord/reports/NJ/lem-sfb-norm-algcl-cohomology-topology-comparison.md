## Worker report

The module `Sheaf.Paper.NormAlgclCohomologyTopologyComparison` states
`AlgebraicGeometry.ProEtale.NormAlgclComparison.isIso_derivedGlobalSections_comparison`.
Its proof is `sorry`; all coefficient objects, inclusions and functors have real data.
The shared node's statement, dependency lists and proof are unchanged. The previous
worker's stage-1 preflight rejection is addressed by supplying an actual stage-2
module, its Lean record and this statement report; no reviewed split is redelivered.

Source read: main-20261015, six-functors basics,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), and the full agent
obligation recorded in this node. Paragraph (3) does not itself prove this coefficient
topology comparison. The obligation's exact literature proof remains WANTED; this
stage supplies its statement only. No source claim beyond the node is attributed to HRS.

Hypothesis and clause correspondence:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Field of positive characteristic p different from ell: `{k : Type u} [Field k]`,
  `(p : ℕ) [Fact p.Prime] [CharP k p]`, and `(hpℓ : p ≠ ℓ)`. Primality implies p>0.
- A separated finite-type scheme over k: `X : Scheme.{u}` and its structure morphism
  `(a : X ⟶ Spec (CommRingCat.of k))`, with `[LocallyOfFiniteType a]`, `[QuasiCompact a]`
  and `[IsSeparated a]`. The first two are precisely finite type, not properness.
- Omega with the extended norm: the fixed existing model `PadicAlgCl ℓ`, exactly the
  algebraic-closure model of the recorded coefficient definitions. This is a choice of
  model for an algebraic closure, not a completeness assumption or a completion.
- C on profinite sets: the existing `Profinite.padicAlgClCondensedRing ℓ`, with underlying
  ring object `Profinite.padicAlgClRingObj ℓ`. Its sections are lifted continuous maps
  belonging to `PadicAlgCl.finiteIntermediateFieldValued ℓ S`.
- B on the same profinite site: the existing `Profinite.continuousMapRingSheaf (PadicAlgCl ℓ)`
  and underlying `continuousMapRingObj`. These specialize the recorded arbitrary-universe
  `continuousMapRingSheafOfUniverse` to a Type-0 coefficient field, definitionally the
  upstream construction; no second continuous-function sheaf is defined here.
- Inclusion c:C to B: `coefficientInclusionRing` is the lifted Subring.subtype on every
  section, with restriction naturality by reflexivity. `coefficientInclusion` applies the
  existing `sheafCompose` forgetful functor to that ring map. Its monoid-homomorphism
  instance is inherited from that functor, not postponed.
- Pullback C_X, B_X and c_X: `condensedRingObj` and `(upperStarFromPoint X).map`, respectively.
  They retain the existing tensor monoid structures and their strong-monoidal transport.
- Finite intermediate field E with restricted norm: `E : PadicAlgCl.FiniteIntermediateField ℓ`.
  This is an intermediate field together with the finite-dimensional predicate, with its
  inherited subspace topology. `Profinite.continuousMapRingObj E` is its existing condensed
  ring and `condensedRingObj (Profinite.continuousMapRingObj E) X` is exactly A.
- Actual A to C_X: `finiteScalarMap`, the pullback of the published
  `Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E`. The A to B_X map is its composite with c_X;
  sectionwise it is exactly the same finite-subfield inclusion into Omega.
- Internal modules and ordinary unbounded categories: all module types are `Mod` in
  `Sheaf (Scheme.ProEt.topology X) Ab.{u+1}`. All ambient derived types are `DerivedCategory`,
  without Plus, bounded truncation, completion or a different coefficient category.
- Every bounded constructible V with finite constant scalar models: the binder V has
  that ambient derived A-module type; `hV` is exactly
  `constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X V` from the
  dependency module. In particular no finite Tor-amplitude or perfectness assumption is added.
- The actual comparison m_V: `finiteSubextensionModule` is C_X as an A-module,
  `normContinuousModule` is B_X as an A-module, and `coefficientModuleMap` has underlying
  map precisely c_X. The two restricted scalar extensions in the node are represented
  by C_X[0] tensor_A^L V and B_X[0] tensor_A^L V. `comparison` is the degree-zero image of
  `coefficientModuleMap`, whiskered on the right by V in the recorded derived tensor
  monoidal category. Thus its representative on a flat-term K-flat resolution P is
  exactly z tensor v mapping to c_X(z) tensor v. This is the canonical tensor description
  of restricted scalar extension, not an arbitrary arrow or a chosen isomorphism.
- Forget coefficient actions and take R Gamma on X_proet:
  `derivedGlobalSections` is `D(Mod.forget A)` followed by `(Sheaf.Γ ...).rightDerivedFunctor`.
  Forgetting is exact and the second functor is the ordinary unbounded K-injective
  construction. The additive witness is obtained from the constant-sheaf/global-sections
  adjunction and preservation of products. The target is `DerivedCategory Ab.{u+1}`.
- The conclusion is `IsIso ((derivedGlobalSections ℓ X E).map (comparison ℓ X E V))`.
  This asserts invertibility of the specified actual morphism in the derived category,
  not just existence of an unrelated isomorphism or equality on individual cohomology groups.
- The node's final negative clauses impose no hypotheses: there is no flatness of c_X,
  completeness of Omega, finite Galois cohomological dimension, internal-Hom commutation,
  or sheaf-level invertibility assumption or conclusion.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: recorded module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `CondensedRing.compactificationOverField`, including its field/Over section conventions.
  This theorem uses the setting's explicit structure-map binders; it neither chooses nor
  uses a compactification, so that unrelated module is not imported solely for the setting.
- `sk-def-sfb-qlbar-condensed`: `Profinite.padicAlgClCondensedRing`,
  `padicAlgClRingObj`, `padicAlgClRingPresheaf` and their docstrings in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
- `def-sfb-continuous-map-condensed-ring`: `Profinite.continuousMapRingSheafOfUniverse`
  and its underlying-object construction in `Sheaf.Topology.ContinuousMapCondensedRing`;
  its public upstream Type-0 specialization `continuousMapRingSheaf`/`continuousMapRingObj`
  is used for the fixed PadicAlgCl model.
- `sk-def-sfb-pulled-back-coefficients`: `condensedRingObj`, `coefficientRing`,
  `upperStarFromPoint` in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `sk-def-sfb-condensed-ring`: `Profinite.CondensedRing` in
  `Sheaf.Topology.ProfiniteCondensedRing`; the actual objects use its underlying Mon/Sheaf encoding.
- `sk-def-sfb-module-objects`: `CategoryTheory.Mod`, `Mod.regular`, `Mod.comap`,
  `Mod.Hom.mk'`, `Mod.forget` in `Mathlib.CategoryTheory.Monoidal.Mod`.
- `sk-def-sfb-derived-categories`: `DerivedCategory` and the total unbounded derived
  functor conventions, including `Functor.rightDerivedFunctorOfQuasiIsoResolutions` in
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`. For these Grothendieck
  categories the existing canonical `Functor.rightDerivedFunctor` is used.
- `sk-def-sfb-derived-tensor-hom`: the actual derived tensor instance
  `Mod.derivedMonoidalCategory`, its K-flat two-variable derived property, and
  `CondensedRing.derivedTensor` publicly provided by
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`.
- `sk-def-sfb-constructible`: `constantModelBoundedConstructible`,
  `IsConstantModelConstructible`, `HasFiniteConstantLocalModel` in
  `Sheaf.Paper.CondensedConstantConstructibility`.
- `sk-def-sfb-derived-extension-of-scalars`: `Mod.derivedExtendMapDerivedCategoryAdjunction`,
  `Mod.preservesKFlatQuasiIso`, exact restriction in
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`. The statement uses
  the equivalent relative-derived-tensor description after forgetting to A, retaining the
  actual tensor inclusion. Finite-subfield inclusion is reused from
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`.
- `def-pur-ringed-site-zeroth-hypercohomology`: read
  `ringedSiteZerothHypercohomologyOfUniverses` in its recorded module. That interface gives
  H0 of ringed-module sections, not an unbounded abelian-sheaf functor. The present node
  explicitly forgets actions first; it uses the existing `Sheaf.Γ` in
  `Mathlib.CategoryTheory.Sites.GlobalSections` and total `rightDerivedFunctor`, without
  copying a ringed-module construction or changing that dependency.

Proof-dependency imports: the already stated standard t-structure and triangulated
natural-transformation two-out-of-three modules are imported as proof dependencies.
The geometric scalar-model, profinite derived-invariants comparison and condensed Galois
descent nodes presently have no recorded Lean statement; none is needed to type this item,
and they are named in its complete four-step proof docstring rather than silently assumed
as hypotheses. No module for one of those independent proof obligations is fabricated.

Edge cases checked: empty X; V=0; E=Q_ell (bottom intermediate field); degree-zero inputs;
arbitrary shifts and bounded cohomological support; X=Spec(k); k separably closed; and
fields with no finite cohomological-dimension hypothesis. The map is still defined in all
these cases and no nonempty scheme, nonzero object, positive cohomological degree, proper
scheme, finite base field, or finite Tor interval binder excludes them. Site objects live
in u+1, arrows in u and sheaf values in u+1, as in the existing framework. Every universe
and variable is explicitly bound, with autoImplicit false. No universe equality is added.

Searches actually made using the prescribed msearch wrapper:

- leanfinder: "Derived global cohomology of finite field constructible pro etale complexes
  is invariant from finite subextension valued coefficients to norm continuous algebraic
  closure coefficients". Eight hits, led by `groupCohomology.exists_mul_galRestrict_of_norm_eq_one`
  and InfiniteGalois projection identities; none is this coefficient-topology comparison.
- loogle: `"Condensed", "cohomology"`: zero hits.
- grep over Mathlib: `(Condensed|PadicAlgCl).*(cohomology|[Gg]lobal[Ss]ections)`: zero hits.
- rg over both `lean/WeilConjectures` and `lean/Sheaf`, including exact item ID, norm/algcl/
  cohomology/topology names and `dag/lean_names_upstream.json`: no existing statement.
  The downstream SupportedFiniteStageTopologyDefect proof docstring cites the item but does
  not state it. Searches for coefficient inclusions found the published finite-subfield
  inclusion, which is reused; the C-to-B inclusion is absent and supplied sectionwise here.

No statement correction, new independent notion, dependency replacement, or
STATEMENT-DISPUTED flag is needed. The theorem remains the unproved structural input
explicitly called for in the reviewed DAG; the module's docstring preserves its proof plan.

Validation: every compilation is through scompile.py with the prescribed time limit.
The initial tensor-action/additivity elaboration failures were repaired. Final compile,
delivery dry run and delivery results follow in the tool output.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
