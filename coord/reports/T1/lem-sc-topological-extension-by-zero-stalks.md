## Worker report

The item is stated in `Sheaf.Topology.AbelianOpenExtensionByZeroStalks`, declaration
`TopCat.Sheaf.abelianOpenExtensionByZero_stalks`. No statement correction is needed.
Source checked directly: https://stacks.math.columbia.edu/tag/00A4 and
https://stacks.math.columbia.edu/tag/00A5. The original citation's numbering is slightly
imprecise (the inside and outside formulas are both part (3)); the stated mathematics agrees.

Hypotheses and clauses:
- A topological space is `X : TopCat`, the open subset is `U : Opens X`, its inclusion is
  `U.inclusion'`, and its induced topological space is `(Opens.toTopCat X).obj U`.
- Every abelian sheaf G on U is a `TopCat.Sheaf AddCommGrpCat` on this subspace. There is no
  Noetherian, connectedness, finiteness, separation or nonemptiness assumption.
- The presheaf and sheaf constructions are `abelianOpenExtensionPresheaf U` and
  `abelianOpenExtensionByZero U`. The former uses the already landed slice-site direct sum.
  An inclusion V into U is unique exactly when V is contained in U, and absent otherwise:
  hence this is G(V) or zero, with precisely the induced restriction maps. Preimage and
  image identify an open contained in U with the same open in the subspace.
- `e` is a family of abelian-group isomorphisms from `G.obj`'s stalk at `x : U` to the
  extended sheaf's stalk at `x.val`. The first conjunct specifies its action on every germ
  over V contained in U, using `abelianOpenExtensionSection`, the summand injection followed
  by the sheafification unit. This characterizes the canonical map: these neighborhoods
  are cofinal and their germs exhaust the stalk. No arbitrary abstract isomorphism is used.
- The second conjunct is the naturality square for every sheaf morphism alpha, using the
  stalk functor and the extension functor's action on alpha.
- The third conjunct states `IsZero` of the stalk at every x outside U. The stalk is a bundled
  AddCommGrpCat object, so categorical IsZero means the zero abelian group.
- The last conjunct handles every sheaf F on X. Literal restriction is
  `abelianOpenRestriction U F`; the counit is `abelianOpenCounit U F`, obtained by the
  universal sheafification lift of `abelianOpenPresheafCounit`. Its component is the
  identity (up to equality of image-preimage opens) on each unique summand and zero on
  the empty sum. The existential r identifies the restricted stalk with F_x and is itself
  characterized on germs. The final equation says e.hom followed by the stalk counit equals
  r.hom: after the canonical identifications the stalk map is identity on F_x.

Dependencies used:
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf`,
  `CategoryTheory.siteExtensionByZeroPresheaf`, `siteExtensionByZeroSection`, and its
  direct-sum restriction and morphism constructions: reused for the new specialization.
- `Mathlib.CategoryTheory.Sites.Sheafification`, `presheafToSheaf`, `toSheafify`,
  `sheafifyLift`: exactly the recorded sheafification notion.
- `Mathlib.Topology.Sheaves.Stalks`, `TopCat.Presheaf.stalk`, `germ`, `stalkFunctor`:
  the underlying abelian-group colimit from def-weil-pbc-module-stalk's mathlib_match.
  The recorded moduleStalkFunctor bundles a module structure and is unnecessary for
  these abelian stalks; no private colimit or germ is introduced.
- `def-sc-topological-abelian-cohomology` records `CategoryTheory.Sheaf.H'` in
  Mathlib.CategoryTheory.Sites.SheafCohomology.Basic. Its signature and docstring were read;
  only its category of abelian sheaves is needed here, not cohomology H'.
- The proof docstring cites the recorded stalk-sheafification input
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, whose signature was inspected.

Edge cases: empty X leaves all point clauses vacuous; empty U has no inside points and
all outside stalks zero; U=top gives the original stalk everywhere and the identity counit.
An empty open V is contained in every U and has the original empty-open section group;
for a sheaf this is zero. Opens meeting both U and its complement have zero presheaf
sections but may acquire sections after sheafification, as required. The zero sheaf is
allowed. All variables and universes are explicitly bound. Sheaf and space may be placed
in any common universe; no fixed small universe is imposed.

Searches: msearch leanfinder "stalks of extension by zero of an abelian sheaf on an open
subset" returned eight stalk/skyscraper/tilde results, none the item. Loogle
"TopCat.Presheaf.stalkFunctor, CategoryTheory.presheafToSheaf" returned no hits.
msearch grep "extensionByZero|extendByZero|lowerShriek|extension by zero" in
Topology/Sheaves returned no hits. LeanSearch "extension by zero abelian presheaf on open
topological subset" was unavailable (Internal Server Error), recorded as such.
Source and project rg for these expressions and the item id found no existing item
statement; module and etale extensions have different domains. DAG and blueprint_refs
searches for extension by zero found the generic slice-site definition, which is reused.

Local compilation of both modules together passed without errors or warnings.
All theorem proofs are sorry, including named obligations used in definitions;
all definition data is explicit. The final server compile is run by the dry run.

## New nodes

`def-sc-abelian-open-extension-by-zero` packages the ordinary topological specialization
of the existing slice-site extension (source: Stacks 00A4 and 00A5), literal restriction,
the presheaf counit and its sheafification lift, and the canonical summand-to-sheaf section
map. The general slice-site functor is imported, never copied. No DAG node or source/Mathlib
module supplies this topological specialization and its maps. Searches above are recorded
in its mathlib_searches. The helper theorems are the named gluing, image-preimage equality,
and counit naturality obligations, with natural-language proofs in their docstrings; their
DAG owner is this definition node, as for the existing slice-site construction's obligations.

## Second reading by T1

I independently read the item and both delivered modules, and checked the source
`sheaves.tex`, labels `definition-j-shriek-structures` and `lemma-j-shriek-abelian`
(Stacks 00A4/00A5), including the surrounding discussion distinguishing abelian
extension from extension by the empty set. The local literature file was absent;
I fetched the Stacks repository's TeX into this item's scratchpad. I also read
[02UT](https://stacks.math.columbia.edu/tag/02UT) for the adjunction-map use.
The source assumes only a topological space and an open subset. The inside and
outside formulas are both 00A5(3); the node's proof-step reference to part (2)
is an imprecise citation, not a different mathematical assertion.

Objects, hypotheses and conclusion clauses, matched individually:

1. Arbitrary topological space X: `(X : TopCat.{w})`. PASS; no separation,
   Noetherian, finiteness or nonemptiness assumptions.
2. Open U and its inclusion j: `(U : Opens X)`, the subspace
   `(Opens.toTopCat X).obj U`, and `U.inclusion'` in the definitions and germs.
   PASS; this is the actual inclusion, not an arbitrary continuous map.
3. Every abelian sheaf G on U: `TopCat.Sheaf AddCommGrpCat.{w}` on that subspace.
   PASS. I opened `def-sc-topological-abelian-cohomology` and its recorded
   `CategoryTheory.Sheaf.H'` declaration in `SheafCohomology.Basic`: the ambient
   category is exactly sheaves of abelian groups; cohomology is not used here.
4. Presheaf j_p!G, its sections and restrictions: `abelianOpenExtensionPresheaf U`
   uses `openSlicePresheaf` and the recorded `siteExtensionByZeroPresheaf U`.
   I read the latter's section, restriction and morphism definitions. In the
   opens poset an arrow V to U exists precisely when V is contained in U, and
   is then unique. Its direct sum therefore has exactly the prescribed single
   summand, or is zero; restrictions use precomposition and G's restriction.
   PASS, including maps from a zero section group to a nonzero one.
5. Sheafification j_!G: `abelianOpenExtensionByZero U` is the above presheaf
   functor followed by the recorded `presheafToSheaf`. I read its signature and
   adjunction in `Sites.Sheafification`. PASS, no alternate sheafification.
6. Inside canonical isomorphism: the family `e x G` has source G's stalk at
   `x : U` and target the extended stalk at `x.val`. The first conjunct fixes
   its hom on every germ over `V ≤ U` to `abelianOpenExtensionSection` followed
   by the target germ. This section map is explicitly the sole direct-sum
   injection followed by `toSheafify`. Every subspace neighborhood arises from
   an open contained in U, so this fixes the canonical map on all germs. PASS;
   existential packaging does not allow an unrelated isomorphism.
7. Naturality in G: the second conjunct is exactly the stalk square for every
   `α : G ⟶ H`, with the extension functor's map on the right. PASS. Outside U
   both stalks are zero, so the outside identifications are uniquely natural.
8. Outside vanishing: the third conjunct quantifies over every G and `x : X`
   with `x ∉ U`, and concludes `IsZero` of its bundled abelian-group stalk.
   PASS; categorical zero here means the zero abelian group, not a bare type.
9. Every sheaf F on X, its literal restriction and adjunction map: the final
   conjunct uses `abelianOpenRestriction U F` and `abelianOpenCounit U F`.
   Restriction evaluates F on the image of a subspace open. The presheaf counit
   is `DirectSum.toAddMonoid` of the equality transport identifying image of
   preimage with V; hence identity on the sole summand, zero on the empty sum.
   `sheafifyLift` extends exactly this map. PASS.
10. Counit stalk is identity at every inside point: `r` is the restricted-stalk
    isomorphism to F's stalk, fixed by its displayed germ equation and the
    `openImage_preimage_eq` equality transport. The final equality says
    `(e x (abelianOpenRestriction U F)).hom` followed by the counit stalk map
    equals `r.hom`. PASS: precisely identity after the canonical identifications.

Dependency and new-node review: I opened the stalk node and Mathlib's `stalk`,
`germ`, `stalkFunctor`, and `stalkFunctor_map_unit_toSheafify_isIso` signatures.
The first three are the recorded abelian-group colimit and coprojections, without
an irrelevant module structure. The last is the stated sheafification-unit stalk
isomorphism. The new node `def-sc-abelian-open-extension-by-zero` correctly
specializes 00A4(1),(2) and 00A5(1),(2); it cites the existing generic slice-site
construction instead of repeating it. Its module explicitly constructs all data.
The three postponed obligations are named theorems, each with a source and a
natural-language proof: restriction gluing, image-preimage equality, and counit
naturality. Each has proof `sorry`, owned by this definition node. No dependency
module is needed. I checked its new-node fields, source, dependency references,
search records and blueprint ownership; final preflight also checks their shape.

Edge cases: empty X has no point clauses; empty U has no inside points and all
outside stalks vanish; U = top gives all original stalks and the identity counit.
The empty open V is contained in U; G's sections there are zero by the sheaf
condition. Opens meeting U and its complement have zero presheaf sections, while
sheafification may create sections, as required. The zero sheaf is allowed.
There is no index, scheme, n or characteristic parameter, and no field or ring
hypothesis. Universe w is explicitly declared and arbitrary. Any space and sheaf
can be placed in a common enlarged universe, so the common-universe encoding does
not impose a fixed size bound. I checked all binders by eye; no variable is free.

Independent searches: LeanFinder query `open inclusion sheaf of abelian groups
lower shriek stalk isomorphism` returned eight restriction-stalk declarations,
including `PresheafedSpace.restrictStalkIso`; these concern restriction, not
extension by zero, and do not give this statement. Loogle query
`TopCat.Presheaf.stalk, CategoryTheory.Limits.IsZero` returned no hits (an earlier
query using bare IsZero reported an unknown identifier). msearch grep
`jShriek|shriek|extendByZero|extensionByZero` returned only five unrelated
function-extension hits. Independent rg in Mathlib topology sheaves, upstream
WeilConjectures topology sheaves, project topology modules and the DAG found no
existing ordinary abelian extension functor or this theorem. Module extensions
use ringed-space module sheaves; pro-etale lower shriek uses another site. Neither
is the present category. The generic direct-sum extension is already reused.
Thus no module should be dropped and no existing declaration replaces the item.

Mismatches and repairs: none in the Lean statements or definition data. I left
both modules and both node signatures unchanged. There is no statement correction
and hence no corrected-statement citer verdict to audit. This reading adds only
this report section. All declaration docstrings name their source and blueprint;
the theorem docstring follows the node's four proof steps. Every theorem remains
sorry, no definition data is hollow, and no local notation or instance is used.

Validation: local compilation of both modules together succeeded in 2.6 seconds
with exit code 0 and no warnings. Server compilation and complete delivery
preflight are run by deliver2.py below.
