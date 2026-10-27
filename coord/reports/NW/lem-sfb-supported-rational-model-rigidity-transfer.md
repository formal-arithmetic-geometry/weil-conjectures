## Worker report

The module `Sheaf.Paper.SupportedRationalModelRigidityTransfer` states
`AlgebraicGeometry.ProEtale.CondensedRing.supported_rational_model_rigidity_transfer`.
Its sole proof is `sorry`. It constructs no new data and introduces no new definition.
The accepted stage-1 statement and its seven-step proof are unchanged. The proof is
included step by step in the declaration docstring, including each step's named uses.

The inherited BLOCKED ending concerned a stage-1 unchanged-item submission, not the
current stage-2 task. The live node has no `lean` record and is queued for stage 2.
This delivery supplies that record and the statement module rather than changing the
reviewed split. There is no repair note for this item in the read clone.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Fixed algebraic closure and finite subextension | The standard `PadicAlgCl ℓ` and `PadicAlgCl.FiniteIntermediateField ℓ` used by the recorded coefficient convention. Its subtype has the induced norm topology. |
| R=Z_ell, K=Q_ell | The first disjunct of `hRK`, identifying the two ring objects with `Profinite.continuousMapRingObj ℤ_[ℓ]` and `Profinite.continuousMapRingObj ℚ_[ℓ]`. |
| R=O_E, K=E for one finite E | The second disjunct of `hRK`, with the same `E` in `Profinite.padicIntegersRingObj ℓ E` and `Profinite.continuousMapRingObj E`. |
| Full continuous-function condensed coefficient rings | `continuousMapRingObj`, and `padicIntegersRingObj`, whose definition uses the same continuous-map construction on the norm valuation subring. Isomorphisms in `Mon` preserve ring-object structure; they are representation identifications, not arbitrary coefficient maps. |
| Ambient coefficient convention listing finite A and Omega | The implication selects only the two displayed integral/rational pairs from that convention. A, a general Lambda, and Omega as a coefficient are not objects in the implication B_R(t) -> B_K(t), so no unused extra parameters or assumption about them is introduced. The finite-field branch still uses the fixed algebraic closure to specify E. |
| R_V=p_V^*C(-,R) and its internal modules | `condensedRingObj R S` and `Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj R S)`, and identically for K. |
| Small sites and size convention | `Scheme.{u}`, `Scheme.ProEt.topology`, `smallEtaleTopology`, `Profinite.{u}` and `Ab.{u + 1}`; there is one explicitly declared universe `u`. Site object and morphism universes are those of these existing definitions, not equated by an additional assumption. |
| A closed immersion t:T0 -> T | `(t : T₀ ⟶ T) [IsClosedImmersion t]`. |
| Both schemes qcqs | `[CompactSpace T] [QuasiSeparatedSpace T] [CompactSpace T₀] [QuasiSeparatedSpace T₀]`. |
| Restriction bijective for every locally torsion etale abelian sheaf, all q>=0 | `ht : ∀ F, Scheme.IsTorsionAbelianSheaf F → ∀ q : ℕ, Function.Bijective (Etale.cohomologyMap t F q)`. The recorded torsion definition is the filtered union of positive-integer annihilator subsheaves, not a single common annihilator. `Etale.cohomologyMap` is the recorded actual etale restriction map. |
| Every admissible finite support chain | Both premise and conclusion quantify over `(S : Scheme.{u}) (tree : QcqsOpenClosedTree T) (p : tree.Path S)`. A path can terminate at any vertex, not just a leaf. Every chain is represented by adjoining complementary leaf siblings; conversely each such path is a chain of precisely the allowed kinds. |
| Open arrows quasi-compact, closed arrows with qc open complement | A tree split has an open immersion j with `[QuasiCompact j]`, a complementary closed immersion i, and equality of their image complements. Vertices are qcqs. Closed immersions are themselves quasi-compact, so the tree's `[QuasiCompact i]` excludes no allowed chain. Complements of qc open immersions and the given qc open complements are qcqs. |
| J uses open lower shriek and closed lower star, in order | `(p.extension R).obj L` or `(p.extension K).obj L`. The existing recursive definition composes precisely `openImmersionLowerShriek` on open branches and `lowerStar` on closed branches. |
| Identity chain r=0 | `QcqsOpenClosedTree.Path.root`; its `extension` is literally the identity functor. The root of the chain is T, distinguished from the closed-pair member T₀. |
| Finite scalar local models on arbitrary pro-etale covers | `HasFiniteConstantLocalModel R S L` and `HasFiniteConstantLocalModel K S L`. Its recorded definition chooses finite presentations over the coefficient on the point and pulls them to each member of a pro-etale cover, retaining scalar matrices rather than arbitrary coefficient-function matrices. |
| Ordinary uncompleted module-derived global sections | `Functor.rightDerivedPullback` is specialized to `condensedModuleSections`, which first forgets the internal action and evaluates at `id_T`, and then derives that full module functor. The output is in `DerivedCategory Ab`, with no completed subcategory. |
| Actual restriction rho | The ordinary natural transformation is the module pullback adjunction unit, followed by the canonical evaluation map at `pullback.lift t (𝟙 T₀) ...`. Its right-derived descent is `Functor.rightDerivedPullback (upperStar R t) ...`, and likewise for K. The map is constructed in the expression, not supplied as a parameter. |
| JL placed in degree zero | `((DerivedCategory.singleFunctor _ 0).obj ((p.extension R).obj L))`, and identically for K. |
| Additional universal integral comparison B_R(t) | `hR`, quantifying over every S, tree, path, and finite R-model L, requires `IsIso` of precisely that actual restriction. It is not an assumption only about the chain selected in the conclusion. |
| Conclusion B_K(t) for all rational finite local models | The conclusion repeats the entire universal quantification with K and asserts `IsIso` of its actual derived restriction. There is no global integral lattice parameter or hypothesis. |
| Arbitrary actual transition maps; no image/kernel/quotient comparison | The model predicate imposes only local scalar finite presentation; no condition on gluing maps is added. The conclusion concerns L itself, with no assertions about images, kernels, quotients, or completeness. |
| No complement condition on t, or extra geometry | There is no `[QuasiCompact ...]` involving the complement of t, and no regularity, Noetherianity, characteristic, or invertibility premise. The torsion hypothesis is retained even though the conditional proof does not need it. |

Dependency declarations read and used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`; its concrete
  continuous coefficient objects determine the two alternatives in `hRK`. The
  finite-subextension-valued algebraic-closure object is not used or identified with
  the full continuous-function algebraic-closure ring.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`,
  `moduleObjectDerivedPullback` and the imported `upperStarLowerStarAdjunction`.
  The actual module `upperStar` and its adjunction enter the restriction expression.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`:
  `AlgebraicGeometry.ProEtale.condensedModuleSections`, the recorded transparent
  ordinary module-section functor.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its public quasi-compactness
  import: `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`;
  only quasi-compactness is needed for the support-chain interface.
- `WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf`:
  `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`.
- `Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback`:
  `AlgebraicGeometry.Etale.abelianDerivedCohomologyPullback` and its public
  `Etale.cohomologyMap` from upstream TopologicalInvariance. The sheaf-level
  nonnegative-degree hypothesis uses that latter recorded declaration.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`; the owning node's
  `IsConstantModelConstructible` is not substituted for this stronger local-model
  premise.
- `Sheaf.Paper.QcqsOpenClosedTree`:
  `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree`, `.Path`, and `.Path.extension`.
  Its already landed definition node `def-sfb-qcqs-open-closed-tree` is added to
  `stmt_deps` as permitted by brief-stage2 section 5. There are no new nodes or
  dependency repairs.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`:
  `CategoryTheory.Functor.rightDerivedPullback`, the general canonical derived
  descent used directly rather than copying a downstream restriction definition.

The size and scheme-conventions nodes explicitly supply conventions rather than
standalone new objects; their recorded primitive scheme/site definitions are used.
All recorded proof-dependency modules, including the Mathlib matches for free vector
spaces, cohomology detecting isomorphisms, enough injectives, and triangle two-out-of-three,
are imported privately unless already public statement imports. No proof dependency
module is skipped and no downstream theorem is used to define this map.

Edge cases checked before writing:

- Root paths implement r=0 and their functor is the identity, even when the tree
  has additional vertices. Quantification does not require a nonempty chain.
- Empty schemes and zero local models are admitted by the tree and finite-model
  definitions. No `Nonempty` condition is placed on a scheme, cover, or model.
- Rank zero, different ranks on different cover members, and arbitrary finite
  presentations over the integral coefficient ring are admitted.
- t=id, an empty closed member, and a closed pair with a non-quasi-compact
  complementary open all remain syntactically admitted whenever ht and hR hold.
- No inverse of ell on the scheme, no bound on etale torsion exponents, and no
  uniform bound on the etale cohomological degree is assumed.
- The coefficient choices are simultaneous pairs: the two isomorphisms in the
  second alternative use the same E, not unrelated finite fields.
- The conclusion quantifies over K-models independently of hR and therefore cannot
  silently demand an integral lattice or globally constant rank.

Searches for an existing statement, performed with the prescribed wrapper:

1. `msearch.py ... leanfinder "Comparison for supported finite integral scalar local
   models of pro etale sheaves implies comparison for rational local models without
   a global lattice"`: eight hits, concerning etale loci and scalar algebra; no match.
2. `msearch.py ... loogle "IsLocalization, IsIso, PadicInt"`: zero hits; the service
   reports unknown identifier `IsIso`. No match was inferred from a failed name lookup.
3. `msearch.py ... grep "supported.*rational.*rigidity|rational.*model.*transfer|HasFiniteConstantLocalModel"`:
   zero Mathlib hits.
4. Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf`, using the item id and the
   patterns above: no existing declaration for the transfer. The three-term
   rigidity consumer mentions the item in its proof plan and already uses the
   exact tree-path, local-model and derived-restriction expressions used here.
5. `grep -rn` of the exact item id in `lean/WeilConjectures`: no hit.
   Searches of support-chain and scalar-model names locate the existing tree
   and finite constant model definitions, which are reused.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md`, especially
paragraph (2). The node is an agent-formulated conditional intermediate obligation,
not the unit's own statement. Its source already records that an exact general
reference is wanted; that limitation is retained in both docstrings.

Validation: `scompile.py NW lem-sfb-supported-rational-model-rigidity-transfer` compiled
this delivered file both as sandbox and at its actual library module path, cleanly
in 2.8 seconds each. Only the named theorem is postponed. No statement fault or
STATEMENT-DISPUTED finding was identified. Dry run: `deliver2.py NW lem-sfb-supported-rational-model-rigidity-transfer --no-push`
returned `OK (dry run): commit 4625daa3544 passes the preflight and compiles; nothing pushed`.

## Second reading by NW

A separate statement-to-node reading was made in this worker session, with the full
node and generated signature open. No second agent was started, as required by the
dispatcher; the maintainer's independent review remains the external second reader.
The reading checked all table entries above, especially the universal (rather than
single-chain) integral premise, all rational models without a lattice parameter,
nonnegative etale degrees and locally torsion rather than uniformly killed sheaves,
and absence of a complement restriction on t. It also expanded the root/open/closed
cases of `Path.extension` and read the full `HasFiniteConstantLocalModel` definition.
No mathematical mismatch was found. Before the final compile the direct closed/open
immersion imports were made public and explicit small-site imports were included to
match statement visibility. The UTC date was obtained from `date -u +%F`, not the
machine's local calendar date. The JSON signature is the complete verbatim theorem
signature from its keyword to `:=`, with no proof or hidden `let` binder.
