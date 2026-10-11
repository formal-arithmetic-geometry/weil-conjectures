## Worker report

The module states the evaluation result for a finite locally free sheaf of modules.  The
binder `X : Scheme.{u}` is the scheme in the node, and `F : X.Modules` is the finite locally
free module, represented by `[F.IsFiniteLocallyFree]`.  The `letI` installs the sheaf-module
monoidal structure.  The family `e` assigns an isomorphism
`Scheme.Modules.tensorObj (dual F) G ≅ homObj F G` to every coefficient module `G`; `dual F`
is `homObj F (𝟙_ X.Modules)`, and `homObj` is the internal sheaf Hom.  For every morphism
`g : G ⟶ H`, the displayed equality is the naturality square, with the tensor map
`dual F ◁ g` and the postcomposition map
`SheafOfModules.homObjMap (R := X.sheaf) (𝟙 F) g`.  Thus the clauses “isomorphism” and
“natural in G” are both explicit.  The proof is `sorry` as required for stage 2.

Dependencies used are `Sheaf.AlgebraicGeometry.Modules.Dual` (`Scheme.Modules.dual`),
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
(`SheafOfModules.homObj`, `SheafOfModules.homObjMap`),
`Mathlib.AlgebraicGeometry.Modules.Sheaf` (`Scheme.Modules`), and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`
(`SheafOfModules.IsFiniteLocallyFree`).  The tensor product is the recorded
`Scheme.Modules.tensorObj` from the sheaf-module monoidal API.

Edge cases checked against the statement are rank zero (both sides are zero), rank one
(`𝒪_X ⊗ G ≅ G`), varying rank on disconnected schemes, and arbitrary (not necessarily
quasi-coherent) `G`; no nonempty, characteristic, or finiteness hypothesis on `G` was added.

Searches for an existing exact theorem: `msearch.py ... leanfinder` queried “evaluation tensor
internal Hom isomorphism for finite locally free sheaf modules” (no exact declaration);
`msearch.py ... loogle` queried “tensorObj F G -> homObj F G finite locally free” (no exact
match); `rg -n 'evaluation|tensorHomUncurry'` over Mathlib and WeilConjectures found only the
presheaf evaluation API and the invertible-module theorem `dualTensorHomIso`, which has the
stronger rank-one hypothesis and therefore is not this statement.

## Earlier second reading (a previous round; superseded)

The node and module were read together.  `X`, `F`, and finite local freeness match the first
clause; `e` gives an isomorphism for every `G`; and the final equality matches naturality in
`G` exactly.  The category, tensor, dual, and sheaf-Hom objects are the recorded dependency
notions.  No mismatch was found.

## Second reading by E1

Read the sandbox node and Lean together, all five statement dependency nodes and their
recorded declarations, and the blueprint source on the server (the literature is absent
from this machine). The source is `lem-sc-ext-locally-free.md`, Proof, first sentence:
evaluation from the dual tensor functor to internal Hom is an isomorphism for finite
locally free F. Also read Stacks `sites-modules.tex`, tensor product section 03EK
(lines 3550–3605) and internal Hom section 04TT / lemma 03EM (lines 3720–3773).
These assume a sheaf of rings on a site; the scheme structure sheaf is commutative.
There is no Noetherian, separatedness, characteristic, or quasi-coherence assumption.

Object, hypothesis, and conclusion inventory and verdicts:

- Scheme X: `X : Scheme.{u}`. Matches; no extra geometric properties.
- O_X-module F: `F : X.Modules`. Matches Mathlib's category of sheaves of modules,
  with sectionwise linear morphisms (`SheafOfModules.Hom.val`), specialized to X.
- Finite local freeness with possibly varying local ranks: `[F.IsFiniteLocallyFree]`.
  Read the source class in `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`
  (lines 150–161): locally free local generators data with finite index types on each
  cover member. This is deliberately not the constant-rank class recorded by
  `def-amb-finite-locally-free-module`: the item's statement explicitly permits varying
  ranks and only compares that dependency's constant-rank notion. Read
  `exists_restrict_iso_free_of_isFiniteLocallyFree` in Modules/FiniteDescent and
  `isFiniteLocallyFree_of_exists_over_iso_free` in Sheaf/LocallyFree: they give the
  cover/local finite-free interpretation in both directions. Matches.
- Arbitrary coefficient module G: `∀ G : X.Modules` inside the family `e`. Matches;
  G has no local freeness, coherence, invertibility, or finiteness assumption.
- Dual: `dual F`, read in Modules/Dual as `homObj F (SheafOfModules.unit _)`.
  Matches Hom(F,O_X), using the existing internal Hom of the dependency, not a copy.
- Tensor: `Scheme.Modules.tensorObj (dual F) G`, read in Modules/Invertible as the
  sheaf-module monoidal tensor. Its `tensorObjIsoSheafification` identifies it with
  sheafification of the sectionwise presheaf tensor. The recorded TensorProduct
  dependency module reuses this very source structure. Matches Stacks 03EK.
- Sheaf Hom: `homObj F G`, an abbreviation for the dependency's
  `SheafOfModules.homObj (R := X.sheaf) F G`. Read its construction and
  `homObjMap` in Sheaf/InternalHom: Hom on the localized site, restriction by
  relocalization, scalar multiplication, and the sheaf proof. Matches Stacks 04TT.
- Canonical evaluation: originally absent! An arbitrary natural family of
  isomorphisms does not assert that evaluation itself is invertible (even its
  negative can be a different natural family). Added
  `∀ G : X.Modules, (e G).hom = dualTensorHom F G` as the first conjunct.
  Read both source definitions in Modules/HomTensor: the presheaf map sends
  `φ ⊗ g` to `x ↦ φ(x) • g|_W`, explicitly verified by its
  `dualTensorHom_app_tmul_app_apply`; the scheme map is its sheafification followed
  by the counit into the existing Hom sheaf. It is precisely the node's map.
- Isomorphism of module sheaves: `e G : tensorObj (dual F) G ≅ homObj F G` together
  with that equality. Matches, including the inverse's module-linearity.
- Naturality in G: for every `g : G ⟶ H`, the final equation is the square with
  postcomposition `SheafOfModules.homObjMap (𝟙 F) g` and `dual F ◁ g`.
  Matches the same canonical maps, in the node's quantifier order.
- The dependency `def-pur-sheaf-modules-hom-module` supplies the scalar action on
  Hom groups: read its `homModule` and `homLinear` in HomModule. There is no
  additional global-sections assertion in this item's conclusion requiring that
  instance; the internal Hom and evaluation already use its prescribed scalar
  formula. No private replacement or additional assumption was introduced.

Edge cases: rank zero gives zero tensor and zero Hom; rank one includes the structure
sheaf; disconnected schemes can have distinct finite ranks on different components;
G may be zero or non-quasi-coherent. The empty scheme and empty cover are allowed:
local generators data impose no nonemptiness, and all module sheaves on it have the
required unique evaluation. No numerical degree or characteristic parameter occurs.
`universe u` is bound and arbitrary; X and its module sheaves use the established
scheme-module universe convention, with no test objects in a smaller universe and
no independent index-universe restriction. All variables in the signature are bound.

Independent searches (different phrasing from the worker):

- `msearch.py E1 lem-sc-ext-evaluation leanfinder` with
  "finite locally free module sheaf canonical dual tensor internal hom evaluation invertible"
  returned free-sheaf universal property and finite-dimensional module evaluation
  declarations, no exact theorem.
- `msearch.py ... loogle 'SheafOfModules.homObj'` returned unknown identifier on
  that service (the internal Hom is a source extension).
- `msearch.py ... leansearch` with "The canonical map dual tensor a sheaf of modules
  to internal Hom is an isomorphism for finite locally free sheaves" was recorded
  unavailable (Internal Server Error), not treated as a negative result.
- `msearch.py ... grep 'dual.*tensor.*hom|tensor.*hom.*iso|evaluation'
  Algebra/Category/ModuleCat` found evaluation functors and free-sheaf APIs.
  Independent `rg` of the source and project for `dualTensorHom`,
  `dual_tensor_hom_iso`, and finite-locally-free Hom found the canonical map in
  source Modules/HomTensor and `isIso_dualTensorHom_of_isFiniteLocallyFree` in
  project LocallyFreeExtCohomology. Opened both. The source isomorphism assumes
  invertibility of the SECOND module and is natural in the FIRST, so does not
  state this node. The project's theorem covers evaluation invertibility but
  has no naturality clause. No existing declaration states the complete node;
  the delivery keeps its single full theorem and reuses the existing map.

Other repairs: added the copyright header and moved the module docstring before
universes/namespaces to follow the example; expanded the theorem docstring with all
three proof steps and their DAG references (H8); replaced the redundant imports by
`WeilConjectures.AlgebraicGeometry.Modules.HomTensor`, which supplies the canonical
map and the same transitive dependency notions; removed unused opens. The `lean.statement`
record is the signature verbatim up to whitespace. The naturality equation and correct
binders were retained. No node statement correction, new node, dependency module,
hollow definition, or proof was added. The sole theorem proof remains `sorry`.

Validation: `scompile.py E1 lem-sc-ext-evaluation` compiled the revised module on the
server in 2.5 seconds with no errors or warnings.
