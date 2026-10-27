## Worker report

The item is a stage-2 statement, not a stage-1 resplit. The live node is split,
reviewed PASS by ND, and has no Lean record. Standing brief §0 explicitly permits
this handoff. The previous worker's stage-1 refusal is inapplicable. The accepted
natural-language statement, proof and proof dependencies are unchanged.

`Sheaf.Paper.SupportedThreeTermScalarCd` states
`AlgebraicGeometry.ProEtale.supported_three_term_scalar_cohomology_vanishes`.
Its only theorem proof is `sorry`. It reuses the landed support-path definition.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The prime is `ℓ : ℕ` with `[Fact ℓ.Prime]`. The fixed algebraic closure is
  `PadicAlgCl ℓ`; finite intermediate fields are `PadicAlgCl.FiniteIntermediateField ℓ`.
  The six disjuncts of `hΛ` describe exactly finite discrete rings killed by an
  ℓ-power, Z_l, OE, Q_l, finite E, and the all-continuous norm-topological Omega.
  Ring-object isomorphisms allow representation-independent coefficients. Finite
  rings in `Type 0` lose no finite ring isomorphism class and include the zero ring.
  The discrete topology and topological-ring structure are explicitly quantified.
  The OE and E alternatives quantify all finite intermediate E independently;
  because no later hypothesis refers to E, this is exactly the union in the node.
  There is no `Profinite.padicAlgClRingObj` alternative: that would change this item.
  The upstream `IsLocalizingAdmissibleCoefficient` was read and is intentionally
  not used as a stronger replacement: it also allows finite-subextension-valued Omega.
  The six relevant clauses reuse its exact existing constructors, publicly imported.
- `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}` with `MonObj` and
  `IsCommMonObj` is the commutative condensed ring. All topological alternatives use
  `Profinite.continuousMapRingObj`, and OE uses `Profinite.padicIntegersRingObj`.
  These are continuous-function ring objects, including all continuous functions
  for Omega. No completion is introduced.
- `X : Scheme.{u}` and `[IsAffine X]` are the arbitrary affine base. `d : ℕ`
  expresses exactly the nonnegative integer bound. `hcd` quantifies every
  `V : Scheme.{u}`, actual `v : V ⟶ X`, `[IsAffine V]`, `[Etale v]`, and requires
  `V.HasTorsionEtaleCohomologicalDimensionLE d`. Its definition was read: it uses
  `F.IsTorsion` in the local-section sense and ordinary derived étale cohomology.
  It imposes no common annihilator. That definition uses natural cohomological
  degrees; since d≥0 all integer degrees q>d are nonnegative, so this is equivalent
  to the node's integer quantification.
- `{S : Scheme.{u}} (tree : QcqsOpenClosedTree X) (p : tree.Path S)`
  retains the specified finite chain as a path in a finite complementary open/closed
  tree rooted at the affine base X, exactly as requested in the return. `Path.root`
  is the length-zero chain. Open edges are quasi-compact open immersions; closed
  edges are closed immersions with the specified quasi-compact open complement.
  There is no leaf-path requirement. Every intermediate scheme in an admissible
  chain over affine X is qcqs: quasi-compact opens and closed subschemes preserve
  qcqs. One can attach the complementary leaf at each step, so tree packaging
  excludes no chain in the node. The complementary branches do not enter J.
- `p.extension Λ` recursively composes precisely
  `CondensedRing.openImmersionLowerShriek Λ j` at open edges and
  `CondensedRing.lowerStar Λ i` at closed edges, in the order towards X.
  At the root it is `𝟭 _`. It uses the actual path; no different factorization or
  arbitrary extension functor is substituted.
- `L : ShortComplex (Mod ... (condensedRingObj Λ S))` supplies L^-1,L^0,L^1 as
  `L.X₁,L.X₂,L.X₃`, their actual module maps `L.f,L.g`, and `L.zero : L.f ≫ L.g=0`.
  The three separate `hL₁,hL₂,hL₃` use `HasFiniteConstantLocalModel Λ S` separately,
  allowing unrelated covering families and scalar finitely presented modules.
  Its existing definition chooses finite presentations on the profinite point,
  then pulls them back to each cover member: exactly the constant scalar models,
  rather than arbitrary finite matrices over local continuous functions.
- `L.homology` is Mathlib's homology in the abelian category of actual module
  objects. It represents `ker L.g / im L.f`, exactly N, with no finite local
  model or completeness assumption on N, images, or kernels.
- `U : X.ProEt` with `[IsAffine U.left]` is every affine object of the specified
  small pro-etale site, with map `U.hom`. The site uses weakly etale objects, as
  does the recorded dependency. Site objects and arrows retain their existing
  universes; abelian coefficients are in u+1. No universe equality is imposed.
- The conclusion first applies `(p.extension Λ).obj` to N, then the
  actual ordinary `(CondensedRing.upperStar Λ U.hom).obj`, then
  `DerivedCategory.singleFunctor _ 0`, and finally the ordinary total right
  derived functor of `condensedModuleSections Λ U.left`. The latter is evaluation
  of the underlying module sheaf at the terminal object, not derived abelian
  inverse image or a completed module category. `DerivedCategory.homologyFunctor
  Ab.{u+1} q` followed by `IsZero` is vanishing of the resulting abelian group.
  `q : ℤ` and `hq : (d : ℤ)+2<q` give precisely the strict asserted range.
- There is no Noetherian, base-field, ℓ-invertibility, finite-subextension-valued,
  constant-matrix, completeness, or finite-model hypothesis beyond those listed.

Dependency declarations read and used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, read to check the
  six coefficient clauses and its additional incompatible seventh clause.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: the actual composite-derived
  `CondensedRing.moduleObjectDerivedPushforward` and `moduleObjectDerivedPullback`.
  The needed underived `upperStar`, used before degree-zero embedding, is publicly
  reexported by that module; we do not apply a derived inverse image to N instead.
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`:
  `Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact` (only quasi-compactness is needed here).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek`;
  `.UpperLowerStar.Defs`: `CondensedRing.lowerStar` and `upperStar`.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`:
  `AlgebraicGeometry.ProEtale.condensedModuleSections`, whose complete definition
  and docstring were read. Its owning definition node `def-sfb-condensed-module-sections` is cited in
  stmt_deps. The continuity theorem is not a statement dependency.
- `Mathlib.Algebra.Homology.ShortComplex.Homology`: `ShortComplex.homology`.
- `Sheaf.Paper.QcqsOpenClosedTree`: `QcqsOpenClosedTree`,
  `QcqsOpenClosedTree.Path`, and `QcqsOpenClosedTree.Path.extension` supply the
  chosen path and its actual composite. Their full signatures and docstrings were
  read, together with the sibling `SupportedThreeTermScalarRigidity` usage.

All currently stated proof dependencies are imported plainly: open/closed module
functors, ringed open/closed exactness, internal-to-sectionwise module equivalence,
condensed localization comparison, rationalization, exact filtered abelian colimits,
universe-general K-injectives, Grothendieck enough injectives, universal derived
Delta functors, and bounded-below injective K-injectivity. Five coefficient-input
nodes have no Lean record and are not needed to type this statement, so no import
is fabricated: supported-image-torsion-reductions-cd,
supported-image-derived-completeness, complete-reduction-rgamma-upper-bound,
supported-rational-image-integral-approximation, and
supported-continuous-omega-image-comparison (all with prefix `lem-sfb-`).
Their full seven-step assembly is retained in the theorem's proof docstring.

Edge cases checked: `Path.root tree` gives the identity functor definitionally; zero-length
paths do not require a positive natural; empty schemes are admitted by all scheme
binders; no `Nonempty` scheme hypothesis occurs; zero modules and zero maps are
admitted by `ShortComplex`; scalar finite presentations include zero modules;
the finite A clause permits the zero coefficient ring; `d=0` means q>2, not q≥2.
There is no common covering or constant-matrix condition. No source counterexample
was found. The node itself honestly marks the exact coefficient estimates WANTED;
this delivery preserves that mathematical status and does not claim a proof.

Searches actually run with msearch.py:

- LeanFinder: “Ordinary pro etale cohomology of supported homology of three finite
  constant scalar local model sheaves bounded by torsion etale dimension plus two”:
  eight hits including `Algebra.etaleLocus_eq_compl_support` and
  `DerivedCategory.isZero_of_isLE/isGE`; none is the supported scalar bound.
- Loogle: `CategoryTheory.ShortComplex.homology`: twelve homology API hits;
  exact quotient notion found and reused, no geometric scalar estimate.
- Mathlib grep: `supported.*(homology|scalar)|SupportChain` in Condensed: zero hits.
- LeanSearch: “Cohomology bound of supported homology of finite constant scalar
  modules on the pro etale site”: eight hits (light condensed discreteness,
  locally constant modules, cochain bounds, etale locus); no matching estimate.
- LeanSearch: “A specified finite chain of quasi compact open immersions or closed
  immersions with quasi compact open complement with its module extension functor”:
  eight hits about immersion factorizations and ordinary scheme-module restriction;
  none retains the specified path and module-object extension functor.
- Loogle: `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`:
  unknown identifier in public Loogle; project source supplies the declaration.
- Mathlib grep: `SupportExtensionChain|SpecifiedSupportChain|support.*[Cc]hain`
  in AlgebraicGeometry: zero hits.
- Project rg for `HasFiniteConstantLocalModel`, support-chain names and supported
  homology found the exact scalar-model definition and the parent complex-heart
  estimate. The latter is about arbitrary finite constructible complexes over X,
  not the specified chain; it explicitly needs this item, so cannot replace it.
- Project `grep -rn` for this item id in WeilConjectures found no declaration.
  `rg` for `SpecifiedSupportChain` found no existing declaration.
- DAG definition-title scan and grep of chain/immersion/support notions found no
  definition of the specified path. `tools/blueprint_refs.py search 'support chain'`
  returned zero blueprint matches; ancestor is det-sf-comp-coherence-cocycle.

## Return repair

Compared the retained packet with current main: only `lean` and `stmt_deps`
differ; the item has not landed. The initial saved-packet dry run passed at
`e004efe1a95`, but this does not resolve the independent mathematical return.

- H2: replaced `lem-weil-pbc-condensed-qcqs-pushforward-continuity` in stmt_deps
  by the landed `def-sfb-condensed-module-sections`. Its recorded existing
  declaration is the identical `condensedModuleSections`; the Lean import remains
  the owning source module. No theorem hypothesis or conclusion is introduced.
- H12/H4: removed the duplicate `def-sfb-specified-support-chain` node and
  `SpecifiedSupportChain.lean` module from the packet. Replaced its dependency by
  `def-sfb-qcqs-open-closed-tree`, imported its recorded module, and changed the
  binders to `{S} (tree : QcqsOpenClosedTree X) (p : tree.Path S)` and J(N) to
  `(p.extension Λ).obj L.homology`, as the reviewer requested. No new node or
  dependency module is delivered. The informal statement and proof are unchanged.

The earlier searches above are retained as the original packet's search history;
the earlier conclusion that no support-path definition existed was incorrect.
The landed tree node, its full source, and the sibling rigidity signature have now
been read and reused. `autoImplicit false` and explicit universes remain in the
single delivered module. The expected `sorry` is its only postponed proof.

Validation: the repaired module compiled cleanly through scompile.py, both as
sandbox and library modules (7.0 s and 6.1 s), with no compiler diagnostics.
The repaired dry run passed preflight and per-file compilation at `9696dfaec11`.
Self-check confirmed only `lean` and the two added statement dependencies differ
from current main, the recorded signature is verbatim, the module has one `sorry`,
all variables and universes are bound, and all Lean lines are at most 100 characters.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
