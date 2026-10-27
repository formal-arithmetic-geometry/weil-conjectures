## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGroupQuotientAtlasTorsor` states
`AlgebraicGeometry.ConstantGroupSheafQuotient.finiteGroupQuotientAtlasTorsor`.
Every theorem proof is `sorry`; every definition has explicit data. There is no
statement correction and no mathematical dispute.

Clause correspondence:

- The base scheme is `S : Scheme.{u}`. The finite abstract group is
  `H : Type (u+1)` with `Group H` and `Finite H`. This finite type can be shrunk
  into any smaller universe when forming finite scheme coproducts; the binder
  imposes no restriction on the isomorphism type of a finite abstract group.
- The S-scheme with its action by S-automorphisms is `Z : Action (Over S) H`.
  Mathlib's `Action.ρAut` identifies the group action with automorphisms.
- A test S-scheme is `T : Over S`. `schemeActionSheaf Z T` is the lifted
  represented sheaf of maps to Z, restricted along `Over.map T.hom` to the big
  fppf site of T. There is no affineness, finite-type, freeness or invertibility
  assumption anywhere in the signature.
- `xi : Over (schemeActionSheaf Z T)` comprises a sheaf with an H-action and
  an equivariant map to Z. `hxi : IsLocallyRegular ... xi.left` is precisely
  local equivariant triviality on fppf covering sieves. Acting by constant
  labels on a sheaf is equivalent to acting by the constant group sheaf:
  the action extends uniquely from the constant presheaf by sheafification.
- `regular` is the sheafification of H with its left regular action. Thus it
  is the sheaf represented by the disjoint union of H copies of the base,
  including on disconnected test schemes (not the constant presheaf H).
- The arrows of `quotient` are the core of the full subcategory of equivariant
  arrows with locally regular source: equivariant sheaf isomorphisms preserving v.
- `orbitMap`, `trivial` and `atlas` implement q. The orbit map is built using
  `constantSheafAdj`, sending the constant label h to h acting on z. The sole
  postponed helper law `orbitMap_equivariant` is explicitly stated in the new
  definition node and has its action-law proof in its docstring.
- `fiberAt` uses the recorded `GroupoidTwoFiberProduct`, which is `Core (Comma ...)`.
  Objects retain z and the specified eta; taking a core does not discard any
  arrow here, because the outer groupoids are discrete. The ambient core
  of all equivariant maps computes exactly the same isomorphisms as the full
  quotient subgroupoid between a trivial torsor and xi.
- `X : Over T.left` and `Nonempty (xi.left.V.obj.RepresentableBy X)` assert
  representation of precisely the original torsor sheaf. `RepresentableBy`
  includes the natural bijection for every test object, hence also the
  representing-scheme identification after arbitrary scheme base change.
- `IsFinite X.hom`, `Etale X.hom`, and `Surjective X.hom` are all three
  geometric properties in the node, not assumptions on the input torsor.
- The family `E U` identifies the 2-fibre groupoid with the discrete groupoid
  of P(U) for every U. The first formula fixes the forward functor to
  `evaluateAt`, evaluation of eta at the identity label. The second formula
  says z=v(p). For U=T this is exactly the asserted section correspondence.
- The final formula fixes the inverse eta at every object V over U and every
  label h to `h • P(b)(p)`. Constant labels generate the constant sheaf locally,
  so this specifies the entire inverse sheaf map. Together with evaluation
  it implies compatibility with every base change, including identity arrows
  and composites: both sides are the same restricted action and sheaf map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and its morphisms, used via `Over`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`: topology `.over`,
  `overPullback`, and the continuous `Over.map` restriction functor.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite` (affine + finite
  ring maps); `Morphisms.Integral`: `IsIntegralHom` read, not needed here.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` (affine ring-map criterion).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective` (point surjectivity).
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.GroupoidTwoFiberProduct`, with its full signature and docstring.
- `Mathlib.CategoryTheory.Action.Concrete`: `Action`, `Action.ofMulAction`,
  and `Functor.mapAction`; `Sites.ConstantSheaf`: `constantSheaf` and its adjunction;
  `Sites.SubcanonicalOver`: the subcanonical slice needed for lifted Yoneda.
- Proof imports retain `FppfSheafRepresentabilityDescentData`,
  `SiteCoveringAxioms`, scheme `Limits` (coproducts, `sigmaSpec`, `ι_sigmaSpec`),
  `Morphisms.Basic` (`IsZariskiLocalAtSource.sigmaDesc`) and pullback vocabulary.
  The proof dependency `lem-sfb-finite-etale-fppf-descent` currently has no Lean
  record or source module, so there is no module to import for it; no part of the
  statement requires that theorem as data, and no replacement proof is asserted.

Edge cases checked before writing: empty T (all section/fibre assertions still
make sense), empty Z (only objects actually carrying a map to Z are quantified),
trivial H, nonabelian H (the inverse uses right translation, not left translation),
characteristic dividing the group order, disconnected T and U (constant sheaves,
not constant presheaves), nontrivial torsors with no global sections, arbitrary
non-Noetherian T and non-finite-type Z. No global torsor section is assumed.

Searches run with msearch.py:

- leanfinder: "The pullback of a quotient stack atlas by a finite group is
  represented by the defining torsor": 8 hits, topology/Galois theory, no match.
- loogle: `"Torsor", "Etale"`: 0 hits.
- grep: `quotientStack|QuotientStack|FppfTorsor|fppfTorsor`: 0 Mathlib hits.
- leansearch: "Noncommutative constant group torsors on the big fppf site and
  equivariant quotient objects": 8 hits, cocycles and abstract group actions,
  no quotient sheaf-torsor interface.
- rg in lean/WeilConjectures and lean/Sheaf found `SchemeActionTorsorGroupoids`
  and `AffineActionQuotientStack`; both assume representing schemes, so cannot
  replace this pre-representability sheaf construction. Upstream `Sheaf.Torsor`
  takes AddCommGrpCat coefficients, excluding arbitrary noncommutative H.
- Searched DAG nodes and ran blueprint_refs.py search "constant group torsor":
  no matching definition node; blueprint ancestor is None. No exact existing
  statement found. Search receipts are included verbatim in the new node.

Validation: both modules compiled separately through scompile.py, with only the
expected sorry declarations. The exact files are also checked by deliver2 preflight.

## New nodes

`def-sfb-constant-group-sheaf-quotient` supplies the missing sheaf-torsor quotient
interface over a general site: regular sheaf, local triviality, quotient core,
trivial orbit map, atlas iso-comma fibre, and slice restriction/evaluation.
Source: Stacks 0371/04WM/04M9, read in examples-stacks.tex and spaces-groupoids.tex.
It differs from the existing scheme-torsor definition by allowing the input sheaf
to be unrepresented. The three search kinds and DAG/blueprint search are above
and in its mathlib_searches. Its postponed equivariance law is the displayed
orbit-map law in this same node, not an additional mathematical hypothesis.

## Second reading by Q64

A separate pass reopened the node and both final modules. Under the dispatcher's
explicit prohibition on starting other agents, this is a self-review, not a claim
of an independent agent's review. The maintainer's independent review remains due.

I checked every hypothesis against the signature, specifically that `hxi` is
local triviality and does not assert representability. I checked the finite,
étale and surjective clauses separately. I checked that arrows are actual
isomorphisms rather than isomorphism classes; that the displayed evaluation is
eta(1); that the next equation fixes z=v(p); and that the last equation applies
to all V→U and all h, including h=1. I removed a redundant equivalence inverse
identity conjunct. I fixed the lifted Yoneda universe explicitly at u+1 and
kept slice sheafification assumptions only in the general helper definitions,
where the actual fppf instantiation supplies them. Nonabelian order and the
empty base both remain covered. No statement correction was needed.
