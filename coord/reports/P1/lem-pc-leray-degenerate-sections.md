## Worker report

The module `Sheaf.AlgebraicGeometry.LerayDegenerateSections` states
`AlgebraicGeometry.exists_lerayEdge_isIso_of_vanishing`. Its only theorem has proof
`by sorry`. It defines no new notion and changes only the item's `lean` record.

Hypothesis and clause correspondence:

- Schemes X and Y and their morphism f: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  There is no properness, affine, Noetherian, or quasi-coherent hypothesis.
- Every O_X-module F: `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
  This is the shared ringed-space carrier required by the dependency and the project's
  module-cohomology convention, not an underlying abelian sheaf used to define cohomology.
- Cohomology on X and Y: `RingedSpace.moduleCohomology X.toRingedSpace q` and
  `RingedSpace.moduleCohomology Y.toRingedSpace p` respectively. The source's cohomology
  is computed in O-module sheaves. Forgetting scalars only turns the resulting module
  and its maps into the abelian groups in the node.
- Direct image f_*: `RingedSpace.moduleDirectImage f.toLRSHom.toShHom`. Higher direct
  image R^q f_* is its `rightDerived q`, exactly the ordinary derived-functor form
  identified in `pqf-def-cohomology`. Γ(Y,-) is the shared
  `RingedSpace.globalSectionsFunctor Y.toRingedSpace`.
- The displayed edge for all q ≥ 0: `∃ ε : ∀ q : ℕ, ... ⟶ ...`. For each degree this
  is a natural transformation into abelian groups, so every component is a well-defined
  group homomorphism and its naturality is exactly the displayed square for every φ.
- The chosen injective resolution: `I : InjectiveResolution F`. Its `cocomplex` is
  indexed by ℕ and its augmentation is a quasi-isomorphism from F in degree zero.
- The direct-image complex is `K`, with `hK : K = (f_*.mapHomologicalComplex ...).obj
  I.cocomplex`. These universally quantified binders merely name an expression;
  `eqToHom hK` transports cycles and homology to that expression. They impose no extra
  mathematical hypothesis: one always takes that expression and reflexivity.
- A cocycle representing a cohomology class is `s : (globalSectionsComplex I).cycles q`;
  its representative is `iCycles q s` and its class is `homologyπ q s`. The inverse
  `I.isoRightDerivedObj (globalSectionsFunctor X.toRingedSpace) q` identifies this class
  with H^q(X,F).
- Its corresponding global section of the cycle sheaf is
  `z : (globalSectionsFunctor Y.toRingedSpace).obj (K.cycles q)`. The premise identifies
  representatives using the canonical restriction on `I.cocomplex.X q` along the equality
  `Opens.map_top f.base`, i.e. X = f⁻¹(Y). On the right the inclusion `K.iCycles q` gives
  the same representative in f_* I^q. This is the source's termwise identification.
- The cocycle formula is the first conjunct's equality: ε on the class of s equals
  Γ of `K.homologyπ q`, followed by transport and the inverse comparison
  `I.isoRightDerivedObj f_* q`, on z. Thus it sends the cycle section to its image in
  the quotient cycle sheaf/boundaries, precisely the node's specified map. Left
  exactness of sections means every global cycle has such a z, and the cycle inclusion
  is monic, so this formula determines the map on every class. Both facts hold for
  every module and morphism here; they are not added hypotheses.
- Independence of resolution is encoded by the same ε satisfying this formula for
  **every** I. The comparisons are Mathlib's canonical comparisons, not arbitrarily
  quantified isomorphisms. Natural transformations encode the equation for every φ
  without restricting to modules satisfying the vanishing hypothesis.
- The vanishing condition is `∀ (q p : ℕ), 0 < p → IsZero ((moduleCohomology Y p).obj
  ((f_*.rightDerived q).obj F))`. It includes every q, and excludes only p = 0 as in
  the node. This is vanishing of module-valued cohomology, not `IsZero` of a bare Type.
- Clause (2) is `∀ q : ℕ, IsIso ((ε q).app F)` under this condition, on the **same** ε
  characterized by the cocycle formula, not merely existence of some unrelated iso.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `AlgebraicGeometry.Scheme.Modules`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`. The latter is explicitly
  allowed by this dependency's record for ringed-space and derived statements.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback` and
  `nonempty_tensorPullbackAdjunction`, read in full. This dependency records pullback
  with its right adjoint pushforward, not a separate higher direct image. The theorem
  does not use pullback; it uses the shared ringed-space specialization of that same
  sectionwise pushforward from the cohomology dependency, so no unused tensor-pullback
  import is added.
- `Sheaf.Paper.PQFCohomology`: `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`;
  its statement and docstring identify ordinary `rightDerived q` of moduleDirectImage
  with homology of derived direct image. The theorem here uses precisely its ordinary
  derived-functor expression and moduleCohomology, through its module import.
- Transitive shared definitions: `Sheaf.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.globalSectionsFunctor`, `moduleCohomology`, `globalSectionsComplex`;
  `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `RingedSpace.moduleDirectImage`, `moduleGrothendieckAbelian` (enough injectives).
  Their full definitions and docstrings were read.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`;
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`;
  `Mathlib.CategoryTheory.Abelian.RightDerived`: `InjectiveResolution.isoRightDerivedObj`.
  These supply the node's resolution and the canonical comparison for every resolution.

Edge cases checked: q = 0 uses the ordinary degree-zero cycle and homology maps, with no
negative index or omitted case; f = identity gives the usual comparison; F = zero and
empty schemes are permitted, and all relevant groups vanish appropriately. Arbitrary
schemes, all module sheaves, and all characteristics are included. No vanishing assumption
is imposed on ε's construction or naturality. Schemes and module sections use the shared
universe-u encoding; no index-set or field universe restriction occurs.

Source checked directly: https://stacks.math.columbia.edu/tag/01F4, Lemma 20.13.6 (2)
asserts exactly degeneration under H^p(Y,R^q f_*F)=0 for every q and p>0. Its proof refers
to collapse at E₂. The item supplies the cocycle description and functoriality; the
module docstring includes all three proof steps and their dependency names.

Searches (all service queries logged in sandbox searches.jsonl):

- msearch.py leansearch: "Leray edge map cohomology higher direct images global sections
  isomorphism vanishing": service unavailable (Internal Server Error); no verdict from it.
- msearch.py leanfinder: "Leray spectral sequence edge map isomorphism when higher
  cohomology higher direct images vanishes": eight hits on group (co)homology connecting
  maps, homology sequences, and connected cochain complexes; none is this statement.
- msearch.py loogle: `"rightDerived", "homology"`: zero hits.
- msearch.py grep: `Leray|leray|homologyComparison` in Mathlib/CategoryTheory: zero hits.
- rg over source WeilConjectures for `leray|Leray`, `higherDirectImage`, and this node id:
  affine Čech Leray, affine direct-image comparisons, étale Leray, abelian-sheaf
  pushforward comparisons, and generic Grothendieck edge constructions exist, but none
  states this canonical edge for all O_X-modules under the stated vanishing condition.
  In particular Topology/Sheaves/PushforwardCohomology uses a class of abelian sheaves
  on which direct image is exact, a different degeneration and different cohomology.
- rg over lean/Sheaf for `leray|Leray`, `moduleCohomology`, `moduleDirectImage`, and
  related edge names: the shared definitions above and étale spectral sequences;
  no existing declaration of this item. The declaration name and node id were also
  searched in WeilConjectures and dag/lean_names_upstream.json: no hit.

Validation: the final file compiled on the server in 5.2 seconds, exit code 0, with no
warnings. No statement dispute, missing notion, unusable dependency, or correction.

## Second reading by P1

I reread the node statement, its Stacks source (Cohomology, Lemma 01F4(2)), and the
module declaration item by item.

- The morphism `f : X ⟶ Y` between schemes is rendered by `{X Y : Scheme.{u}}
  (f : X ⟶ Y)`; no properness, separation, Noetherian, affine, characteristic, or
  finiteness hypothesis is added.
- The coefficient object is exactly an arbitrary
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, matching an
  `O_X`-module. Cohomology is `RingedSpace.moduleCohomology` on X and Y, and the
  direct image is `RingedSpace.moduleDirectImage f.toLRSHom.toShHom` with
  `rightDerived q`, as required by the node.
- The family of edge maps is the natural transformation
  `ε : ∀ q, H^q(X,-) ⋙ forget₂ _ AddCommGrpCat ⟶
  (R^q f_* -) ⋙ Γ(Y,-) ⋙ forget₂ _ AddCommGrpCat`. Thus the displayed maps are
  homomorphisms and naturality is quantified for every module morphism.
- For every q, injective resolution `I`, direct-image complex `K` with its
  equality `hK`, and cocycle `s`, the formula uses `iCycles`, `homologyπ`, the
  canonical `isoRightDerivedObj` maps, and the restriction along `Opens.map_top`.
  I found one mismatch: the worker's implication only quantified a `z` if one
  happened to be supplied, so it did not assert that the corresponding cycle
  section exists. I changed the declaration to `∃ z, (representative equality) ∧
  (edge-map formula)`, which states the node's “sends the class to the image”
  clause without a vacuous conditional. The node's `lean.statement` was updated
  verbatim to this compiled signature.
- Resolution independence is represented by the same ε satisfying this formula
  for every `I`; the second conjunct states that under
  `∀ q p, 0 < p → IsZero (H^p(Y,R^q f_*F))`, every `(ε q).app F` is an isomorphism.
  The quantifier order and strict positivity condition agree with the node.

Edge cases checked: q = 0, identity f, zero modules, empty schemes, and arbitrary
characteristic all remain admitted; no index set or universe is restricted beyond
the common scheme/module universe. The vanishing premise excludes only p = 0.

Searches were repeated with `msearch.py` LeanSearch, LeanFinder and Loogle queries,
`rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`, and the upstream-name index;
none contains this Leray edge statement. The recorded searches are in
`searches.jsonl`. No dependency module was needed and no existing declaration was
found.

The repaired module compiles cleanly with `scompile.py`; its only proof is `sorry`.
