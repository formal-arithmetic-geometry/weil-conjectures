## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleAbelianZmodModule` states
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_constructible_abelian`
with a single `sorry`. It proves nothing and introduces no new definition. The
natural-language node is unchanged. Its statement dependencies gain two already
recorded nodes: `lem-weil-pbc-etale-constant-ring-module-equivalence` and
`def-constructible-stratification`.

Hypothesis and conclusion correspondence:

- An arbitrary scheme T is `(T : Scheme.{u})`, with explicitly declared universe u;
  no field, curve, Noetherian, quasi-compactness or nonemptiness condition is imposed.
- The integer n ≥ 1 is `(n : ℕ+)`. Its natural-number coercion is the modulus everywhere.
  Positive integers and positive naturals give exactly the same allowed moduli. The
  existing `NeZero.pnat` instance supplies finite cyclic coefficients without an extra
  hypothesis or a local instance.
- C is `(C : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`, and its constructibility
  hypothesis is `(hC : IsConstructibleAbelianSheaf C)`, exactly the recorded predicate.
- The annihilation hypothesis is `(hkill : (n : ℕ) • 𝟙 C = 0)`, literally the endomorphism
  equation in the node, rather than a torsion or pointwise boundedness substitute.
- The node's chosen module sheaf C-tilde is the binder G in `ringedSiteModules.{u + 1}`
  over `(constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
  (RingCat.of (ULift.{u + 1} (ZMod (n : ℕ))))`. The transparent recorded abbreviation is
  exactly Mathlib's `SheafOfModules`. The hypothesis hG says its underlying abelian
  sheaf equals C. G is not assumed constructible or endowed with an unrelated map:
  it is precisely a module structure extending C. Existence and uniqueness are the
  already recorded `sheaves_killed_by_n_zmod_modules` (2); the theorem states the result
  for any such G, hence for its unique supplied value, without choosing arbitrary data.
- The first conclusion is `IsConstructibleEtaleModuleSheaf` of
  `(etaleConstantModuleRestrictionFunctor T (ULift.{u + 1} (ZMod (n : ℕ)))).obj G`.
  This is the existing inverse of constant-ring module realization: it restricts the
  actual ring-sheaf action along the constant-presheaf sheafification unit. It keeps
  the underlying abelian presheaf and changes only the encoding. Thus the predicate
  applies to the same G and its fixed module action. ULift changes only coefficient
  size, not the ring or its action. No arbitrary equivalence or map is assumed.
- The second conclusion quantifies `∀ S : LocallyClosedStratification T`. Its two
  antecedents are the definition of a witnessing stratification of C: constructible
  parts, and on every stratum an etale `Cover` with finite `AddCommGrpCat` values and
  abelian inverse-image isomorphisms to their constant sheaves. These are copied from
  the body of `IsConstructibleAbelianSheaf`, with no change to the schemes or immersions.
- For that very S and each k, the conclusion provides `d : LocallyConstantDatum` for
  the module inverse image along `S.immersion k`, then finite `ModuleCat` values M and
  isomorphisms on `d.cover` to constant module sheaves. This is exactly the stratum
  clause of the recorded module constructibility predicate. The preexisting
  constructibility of S's parts is retained; no new stratification, refinement or
  closure-incidence condition is substituted. Trivializing covers and constant values
  may change (empty cover members may be discarded), as the node permits.
- There is no reverse implication or assertion that each originally chosen constant
  value on an empty cover member is annihilated by n. The parenthetical ingredients
  in the statement are the five-step proof in the declaration docstring.

Dependency declarations read and used:

1. `Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf`:
   `AlgebraicGeometry.Scheme.IsConstructibleAbelianSheaf`, with its full docstring/body.
2. `Sheaf.Paper.SheavesKilledByNZmodModules`:
   `AlgebraicGeometry.sheaves_killed_by_n_zmod_modules`, with all six conjuncts; (2)
   supplies the fixed module structure, and (1),(3) supply annihilation and linearity.
3. `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded general etale-sheaf
   conventions; the actual abelian and constant-ring module types are Mathlib's
   `CategoryTheory.Sheaf`, `CategoryTheory.constantSheaf`, and `SheafOfModules`.
4. `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
   transparent abbreviation for Mathlib's general ringed-site category, not a scheme
   structure-sheaf category.
5. `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
   `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`. Its current source was
   fetched using `scompile.py --source`. It uses `Scheme.Stratification`, whose parent
   `Topology.Stratification` already requires constructible parts. Its domain,
   immersion, immersion-property and image fields match the recorded
   `LocallyClosedStratification`, so it says the node's global finite-partition notion.
   The similarly named Sheaf module is deliberately not imported alongside it: both
   define the same declaration name. No dependency record needs repair.
6. `WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`:
   `AlgebraicGeometry.Scheme.etaleConstantModuleRestrictionFunctor` and its underlying
   construction. Read the current server source, including scalar restriction along
   `toSheafify`, the identity on underlying sections, unit/counit and equivalence.
   This landed node is added to statement dependencies because the signature uses
   its actual canonical inverse functor to bridge the two existing encodings.
7. `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
   `AlgebraicGeometry.Scheme.LocallyClosedStratification`, added explicitly to the
   statement dependencies since the fixed-stratification clause uses this declaration.

Available proof dependencies are imported privately: the recorded upstream
`AlgebraicGeometry.etaleInverseImageModulesExact` and
`AlgebraicGeometry.Scheme.constantSheaf_geometricStalk_isIso` (the latter's current
source was read via `scompile.py --source`); Mathlib's `AlgebraicClosure`,
`Scheme.pointSmallEtale`, `GrothendieckTopology.Point.sheafFiber`, and
`AddCommGroup.zmodModule`. The constant-module-underlying node is the exact existing
`CategoryTheory.constantCommuteCompose`; its full signature/docstring was read.
The proof docstring follows all five DAG steps and records their node references.

Sources and edge cases: read the local Stacks `etale-cohomology.tex` definitions
at 03RU (9917 onward) and 03RW (11672 onward), including the discussion that their
usual constructibility is affine-local. The DAG predicates deliberately use the
explicit global finite partition, as their statements and docstrings already say;
this delivery does not identify the two notions on arbitrary schemes. Checked n=1
(the zero coefficient ring and zero sheaf), the empty scheme, an empty stratum, and
empty etale cover members. Empty members must be discarded before identifying a
constant value with a stalk: arbitrary finite abelian values on the empty scheme
need not be killed by n. The conclusion retains only the stratification, so permits
this. n=0 is excluded exactly as the node says; no primality assumption excludes
composite n such as 4. Schemes and sites have the recorded universes; all group and
module carriers have universe u+1, and the coefficient ring is the canonical ULift.

Searches for an existing statement or missing notion:

- `msearch.py ... leanfinder "A constructible abelian sheaf annihilated by n is
  constructible as a sheaf of ZMod n modules with the same stratification"` returned
  eight condensed-module/abelian-category APIs, including
  `CompHausLike.LocallyConstantModule.functor`, with no etale constructibility result.
- `msearch.py ... loogle "CategoryTheory.Sheaf, ZMod"` returned zero hits.
- `msearch.py ... leansearch "A constructible abelian etale sheaf killed by n is
  constructible as a sheaf of ZMod n modules"` returned the ZMod module constructions,
  generic sheaf abelian instances and sheaf module constructors; no constructibility
  comparison on a general scheme.
- `msearch.py ... grep "constructible|IsConstructible" CategoryTheory/Sites` returned
  zero Mathlib hits. Read `AddCommGroup.zmodModule` directly; it only constructs the
  module structure on one abelian group.
- `rg` for `ConstructibleAbelian`, constructible ZMod/zn variants and the item id in
  the upstream source and `lean/Sheaf` found the constructible abelian definition and
  its users, and the curve-only `ConstructibleTorsionModulesAgree` comparison. Read
  that theorem's full signature: it requires an algebraically closed field and a
  curve, and uses a curve coefficient pair, so cannot bind this general-scheme item.
- Additional `rg` in the named source and side-project directories located the
  existing `EtaleConstantRingModuleEquivalence` canonical scalar restriction, already
  carried by a DAG node. Its current published declaration is used, not copied.
- Checked the proposed full declaration name against `dag/lean_names_upstream.json`,
  the upstream Lean sources and `lean/Sheaf`; no preexisting theorem has that name
  or the present general-scheme statement. The only general abelian predicate is
  reused. No new definition node is needed.

No statement correction, disputed statement, or new node is required. A single-file
`scompile.py` run compiled both the sandbox check and the module check cleanly, each
in 2.4 seconds, with no error or warning. All variables and universes are explicit;
there are no theorem-local lets, local instances, private helpers or definitions.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
