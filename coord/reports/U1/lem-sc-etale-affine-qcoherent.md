## Worker report

The module states `AlgebraicGeometry.Etale.etale_affine_qcoherent`: for an affine
scheme `X` and a quasi-coherent module `F : X.Modules`, every positive-degree
cohomology group of the associated étale sheaf is subsingleton. The affine
hypothesis is the typeclass `[IsAffine X]`; quasi-coherence is `[F.IsQuasicoherent]`.
The conclusion binds every `q : ℕ`, assumes `0 < q`, and asserts
`Subsingleton (Sheaf.H (AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf F) q)`.
The associated sheaf declaration used is
`AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf` from
`Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`.

Edge cases checked: `q = 0` is excluded by `0 < q`; all positive natural degrees are
included; the zero module is allowed; no nonempty or characteristic assumption is
introduced; arbitrary affine schemes (including the empty affine scheme) are allowed.

Searches: `msearch.py U1 lem-sc-etale-affine-qcoherent leanfinder` for affine étale
quasi-coherent cohomology (no exact declaration); `msearch.py ... loogle` for
`Sheaf.H`, `smallEtaleTopology`, and quasi-coherent cohomology (no exact result);
`msearch.py ... grep` and `rg` over Mathlib and `WeilConjectures` for étale
quasi-coherent cohomology (no matching theorem). The project declaration
`AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf` is used for the
associated sheaf notion.

## Earlier second reading (a previous round; superseded)

The file and node were read together. `X : Scheme.{u}` with `[IsAffine X]` renders
“X affine scheme”; `F : X.Modules` with `[F.IsQuasicoherent]` renders a
quasi-coherent module; `∀ q, 0 < q → Subsingleton (...)` renders exactly vanishing
for every positive cohomological degree. No clause or hypothesis is added or
omitted.

## Second reading by U1

I independently opened the item node, its sole statement dependency
`def-sc-etale-qcoherent-module`, the recorded module
`Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`, and its underlying sections
presheaf and descent theorem. I read Stacks `etale-cohomology.tex`, label
`theorem-zariski-fpqc-quasi-coherent` (03P2), including the affine part of its proof
and the following remark on derived global sections. The source assumes only a
scheme and a quasi-coherent module; its affine case assumes that the object is
affine. There is no standing field, Noetherian, finite type, or characteristic
assumption. The node is precisely this affine small-étale case.

Item-by-item list of objects, hypotheses, and conclusion:

- Scheme X: `(X : Scheme.{u})`; verdict: exactly the node's arbitrary scheme,
  at an arbitrary universe u.
- X affine: `[IsAffine X]`; verdict: exactly affine, no stronger auxiliary
  finiteness or nonemptiness hypothesis.
- O_X-module F: `(F : X.Modules)`; verdict: Mathlib `Scheme.Modules` is
  `SheafOfModules.{u} X.ringCatSheaf`, the required Zariski module sheaf.
- Quasi-coherence: `[F.IsQuasicoherent]`; verdict: the existing
  `SheafOfModules.IsQuasicoherent` instance, with no coherence/finiteness added.
- Associated étale abelian sheaf F_et: `Scheme.Modules.etaleTensorSectionsSheaf F`;
  verdict: exactly the dependency's recorded declaration, with underlying presheaf
  `etaleTensorSectionsPresheaf F`, not sheafification or a Hom-valued replacement.
  I opened `EtaleTensorSections.lean`: its object is
  `Γ((tensorPullback U.unop.hom).obj F, ⊤)`, and its restriction is the canonical
  tensor-pullback unit followed by `tensorSectionsComp` and structure-map transport.
  This is precisely Γ(U,u^*F) and c_{g,u}(g^*s). The sheaf-condition proof is the
  separate `isSheaf_etaleTensorSectionsPresheaf` theorem; no data is hollow.
- Degree and quantifier: `∀ (q : ℕ), 0 < q →`; verdict: all positive degrees,
  after X and F are fixed, as in the node.
- Cohomology: `Sheaf.H (Scheme.Modules.etaleTensorSectionsSheaf F) q`;
  verdict: Mathlib's abelian sheaf cohomology on `X.smallEtaleTopology`. I opened
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: H is Ext from the constant
  integer sheaf, the usual derived-global-sections cohomology. It is not Zariski
  module cohomology. No additional typeclass assumptions are generalized into the
  theorem: printing the elaborated signature shows only IsAffine and
  IsQuasicoherent, with `Sheaf.H.{u, u, u, u + 1}`.
- Vanishing: `Subsingleton (...)`; verdict: exactly zero as an abelian group,
  whose zero element exists. The assertion is neither stronger nor weaker.

Edge cases: q=0 is intentionally outside the conclusion; q=1 and every higher
natural degree are included. The zero module and the empty affine scheme are
allowed. There is no index set in the signature, hence no nonempty-cover assumption
or empty-index exclusion. No characteristic or field restriction appears.
Universe u is explicitly bound and arbitrary, the module's sections live in u,
and its cohomology lives in u+1. The printed signature has no hidden variable,
universe, sheafification, Ext, or injectivity binder. `set_option autoImplicit false`
also enforces binding. No new definition node or dependency module is needed.
There is no statement correction in this delivery.

Independent searches (2026-10-12):

- LeanSearch via msearch: “Higher cohomology of quasi coherent sheaves vanishes on
  affine schemes in the etale topology”; unavailable (Internal Server Error),
  recorded as unavailable, without a mathematical search verdict.
- LeanFinder via msearch: “Vanishing of positive degree cohomology on the small
  etale site of an affine scheme for a quasi coherent module”; eight hits,
  including Sheaf.H and cotangent-complex facts, no matching vanishing statement.
- Loogle via msearch: `"Sheaf.H", "IsAffine"`; zero hits.
- rg across Mathlib, WeilConjectures and lean/Sheaf for `03P2`,
  `etale_affine_qcoherent`, associated-sheaf names, and both word orders of
  quasi-coherent/étale/cohomology; only the dependency's associated-sheaf module.
  Broader rg for affine, acyclic, vanish and subsingleton in Sites and Cohomology
  found the upstream `Scheme.Modules.subsingleton_H_succ_of_isAffine`. I opened
  its signature in `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`:
  it concerns `F.H` on the Zariski space, not F_et on the small étale site, so is
  not this statement. The cohomological-dimension and direct-sum results also do
  not assert quasi-coherent affine étale vanishing. No existing exact statement
  or duplicate notion was found.

Mismatches repaired: the module docstring had the item name but lacked the literal
`(blueprint: lem-sc-etale-affine-qcoherent)` marker. Added that marker. The theorem
proof docstring compressed all three node steps and omitted their dependency
identifiers. Expanded it to follow the affine-cover criterion, pullback/descent
and Amitsur calculation, and final-object/K-injective comparison step by step,
with the node's cited identifiers. The mathematical signature was already right
and is unchanged; the node's lean.statement remains verbatim its signature.
There are no definitions or proved assertions in the delivery; the sole theorem
still has proof `by sorry`.

Validation: lcompile passed on the final module. A separate scratch compilation
printed the elaborated theorem with universes to verify all binders and instances.
The delivery dry run and final delivery perform the required server compilation
and preflight checks.
