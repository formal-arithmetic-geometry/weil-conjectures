## Worker report

States `Profinite.CondensedAction.SplitCosetInduction.exists_datum` in
`Sheaf.CategoryTheory.CondensedSplitCosetInduction`. This is stage 2: the sole
postponed theorem has proof `sorry`; its docstring contains all ten DAG proof
steps. All definitions contain actual data. The live item is already split and
reviewed at stage 1, but has no Lean attachment. Its statement, dependencies,
proof and all stage-1 metadata are preserved; only `lean` is set.

Hypothesis and clause correspondence:

- Arbitrary commutative condensed ring A: `R : Profinite.CondensedRing.{u}` and
  `[IsCommMonObj R.X]`, inherited from the module variables. There is no
  topological presentation assumption on R. The existing coherent profinite
  site and its section rings/modules are reused throughout.
- Small-site size convention: explicit universe `u`, tests `Profinite.{u}`,
  groups in `Type u`, and coefficients/modules in universe `u + 1`, exactly as
  in the recorded action-module dependency. `set_option autoImplicit false`
  prevents auto-bound variables. The size node is a metatheoretic convention,
  not a missing Lean object.
- Profinite P: `[TopologicalSpace P] [Group P] [IsTopologicalGroup P]` together
  with `[CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]`.
- Closed subgroup H: `H : Subgroup P` with the inherited topology and
  `hclosed : IsClosed (H : Set P)`. No normality or finite-index assumption.
- The coset space with its quotient topology is the existing `P ⧸ H` and
  Mathlib's quotient topology. It has its inherited compact-space instance;
  `[T2Space (P ⧸ H)] [TotallyDisconnectedSpace (P ⧸ H)]` express the remaining
  profinite conditions. These exactly render the statement's assumption that
  this coset space is profinite.
- Continuous section: `s : C(P ⧸ H, P)` and
  `hs : Function.RightInverse s (QuotientGroup.mk : P → P ⧸ H)` express q s = id.
- The categories A_H(A), A_P(A) are exactly the dependency's `ActionModule R H`
  and `ActionModule R P`. Their underlying internal modules, maps, section
  modules and action are unchanged.
- P_S and H_S are `C(S, P)` and `C(S, H)`. The group algebra's finite formal
  sums with coefficients in M(S) are represented by
  `C(S, P) →₀ sectionModule R M.module S`. Its pointwise scalar structure
  already imposes coefficient balancing and additivity. `relations` is the
  scalar span of `[p h] tensor m - [p] tensor h m`; `sectionTensor` is the
  quotient by this submodule. This is the standard generators-and-relations
  presentation of A(S)[P_S] tensor over A(S)[H_S] with M(S), not a tensor over
  A(S) alone. Distributivity extends the group-element relations to all of
  A(S)[H_S]. `tensorSymbol` is the actual quotient of a single supported term.
- Presheaf and its restrictions: `TensorPresheaf.presheaf` is a
  `PresheafOfModules` over the recorded section-ring presheaf; `sections`
  identifies every section with this exact quotient. Its `restriction` field
  specifies `[p] tensor m` maps to `[p composed with f] tensor f*m` for every
  profinite arrow. Semilinearity specifies coefficient restriction; finite
  sums of these generators specify every restriction map, including collisions
  between support indices.
- Module sheafification: `Construction.comparison` identifies the underlying
  section-module sheaf of the induced object with
  `PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)` of that tensor
  presheaf. This uses the recorded sheafification, not another construction.
  `generator` is the actual abelian-sheafification unit followed by the inverse
  comparison; Mathlib's module-sheafification unit is this same underlying map.
- Induced P-action: `Datum.action` gives g([p] tensor m) = [g p] tensor m
  after this unit. Since these generators locally generate sheafification,
  their formula specifies the action on the entire induced sheaf.
- Functor: `Construction.functor` has the required source and target;
  `Datum.map` specifies tensoring u on generators, after sheafification.
  Identity and composition are part of the functor structure.
- Additive and exact: `Datum.additive` supplies the additive functor instance.
  `Datum.exact` states for every `ShortComplex` that `C.ShortExact` implies
  `(C.map functor).ShortExact`, exactly preservation of short exact sequences.
  The existing categories are abelian by the recorded product-action theorem;
  no extra abelian or exactness hypothesis is imposed on the input.
- Left adjoint to restriction: `Datum.adjunction` is to the dependency's
  `inflate` applied to the continuous inclusion H → P, which keeps underlying
  modules and precomposes the action, hence is exactly restriction.
- Forward formula: `Datum.transpose` says the transpose at m is F applied to
  `generator ... 1 m`, the image of [1] tensor m under the sheafification unit.
- Inverse formula: `Datum.untranspose` says its value on `generator ... p m`
  is `N.act S p (f(m))`. It is a morphism from the sheafification, so the formula
  expresses the specified factorization through sheafification, rather than
  an arbitrary choice of a map with an unrelated adjunction.
- No finiteness/discreteness restriction: there is no `Finite`/`Fintype` on
  P/H or `C(S,P/H)`, and M is any `ActionModule R H`. Finite support refers only
  to each formal sum, exactly as in the source tensor product.

The theorem's `Nonempty (Datum R P H)` asserts existence of the construction
with all these properties together. Neither a functor nor an object is defined
by choosing from this theorem. The sectionwise quotient is a real construction;
all presheaf, sheafification and normalization comparisons are included in the
existence statement and determine the data up to the canonical isomorphism.
These are helpers for this item's own construction, not additional notions or
new DAG nodes. There is no arbitrary-map or arbitrary-Nonempty substitute for
the canonical induction/sheafification.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, the
  arbitrary ring object in tensor abelian sheaves on the coherent profinite site.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.ActionModule`, `Modules`, `sectionModule`,
  `actionCategory`, `actionPreadditive`, and `inflate`.
- Its existing `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
  interface: `CategoryTheory.InternalAbelianSheafModule.sectionRings`,
  `sectionRingSheaf`, and `sectionModuleFunctor`, all with their full signatures.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, its unit comparison and adjunction.
  `CategoryTheory.toSheafify` is the same underlying unit.
- The metatheoretic `def-weil-size-convention` has no Lean declaration; its
  universe convention is rendered explicitly above.
- Proof imports retain `Sheaf.CategoryTheory.InternalActionSitePresentation`
  (`CategoryTheory.InternalActionSite.presentation`) and
  `Sheaf.CategoryTheory.CondensedProductActionInflation`
  (`Profinite.CondensedAction.product_action_inflation`). The module
  sheafification exactness Mathlib leaf is already provided by the public
  sheafification import, so no separate module is needed.

Edge cases checked mathematically: H=P gives one coset and ordinary restriction
identity; H=1 gives the free induced sheaf; trivial P is included; A=0 and M=0
produce zero quotients; empty S has its unique continuous-map sections and zero
module sections. Infinite P/H (for example H=1 and P an infinite profinite group)
is allowed. No chosen section enters the construction itself; it is used in the
proof of exactness only. Non-normal H is allowed: `pH` and balancing `[ph]`
use the same right-H orbits, and the quotient is not required to be a group.
Restrictions may merge support indices; the tensor presheaf clause and finite
sum convention handle this. Epimorphisms are never assumed sectionwise
surjective. No false or disputed statement was found.

Searches made for an existing exact theorem, with msearch.py:

- LeanFinder: "Exact induction of internal condensed group actions on modules
  along a subgroup with split profinite coset projection". Eight hits included
  `Condensed.profiniteFree`, `Condensed.profiniteSolid`, ordinary Rep
  coinvariants and continuous cohomology. None gives the statement over an
  arbitrary condensed ring.
- Loogle: "Rep.indFunctor, Rep.indResAdjunction,
  PresheafOfModules.sheafification". No hits for the combined query.
- Grep: "indResAdjunction|indFunctor|split.coset". Fifteen hits concerned
  ordinary `Rep` induction/coinduction and finite-index representations.
  Read `Mathlib.RepresentationTheory.Induced` in full for the relevant
  `Representation.IndV`, `ind`, `Rep.indFunctor`, and `indResAdjunction`
  signatures. They do not construct the natural restrictions and condensed
  action over changing section rings; the current result cannot be attached
  to those abstract-group declarations.
- LeanSearch: "Exact induction of sheaves of modules with internal group
  actions over a condensed ring split coset projection". Eight hits on
  ordinary sheaves of modules, their free objects, and constant-ring condensed
  abelianness; none matches.
- Direct rg of both `lean/WeilConjectures` and `lean/Sheaf` for
  `indResAdjunction|split.coset|[Ii]nduction.*[Cc]ondensed|[Cc]ondensed.*[Ii]nduction`
  found no matching declaration. A separate search for the item id in
  `lean/WeilConjectures` returned no hits. The condensed bar modules mention
  exact induction in proof docstrings but do not state it.
- Checked `SplitCosetInduction` against both library roots and the upstream
  declaration index: no collision. Checked subgroup continuous inclusion in
  Mathlib's continuous homomorphism and topological algebra sources: no
  matching bundled subtype declaration. The helper is the existing subgroup
  monoid hom equipped with `continuous_subtype_val`.

Read the source blueprint direct-images paragraph (3): it assembles proper and
open direct image, and does not assert induction. Accordingly the source's
agent-formulated/WANTED status is retained without claiming an external proof.
The theorem docstring follows the reviewed DAG's ten-step induction proof.

Validation: server-only scompile.py compiled the sandbox and its intended module
path cleanly, with no error or unexpected warning. No global or local Lean build
was run. The only writes were in this sandbox, plus the authorized wrappers'
normal bookkeeping. The earlier stage-1 preflight rejection is not addressed by
altering the reviewed split: this delivery supplies the missing stage-2 Lean
attachment while preserving it.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
