## Worker report

Item: `lem-trf-etale-relation-restriction-quotient`. Module:
`Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient`. The main declaration is
`AlgebraicGeometry.AlgebraicSpace.etale_relation_restriction_quotient`; its proof is
`sorry`. No theorem is proved. The three helper definitions have real data:
`restrictedEtaleRelation`, `restrictedEtaleRelationSource`, and
`restrictedEtaleRelationTarget` use Mathlib's chosen pullbacks and projections.
They belong to the restricted-relation notion in this item and are listed in
`lean.declarations`, with source and blueprint docstrings. There are no new nodes,
dependency repairs, statement corrections, or statement disputes.

I read the target and every statement dependency, including the `mathlib_match` of
the Mathlib leaf `def-pc-fppf-site` (which correctly has no `lean` field). I read the
recorded source declarations and their docstrings, the existing project module
`EtaleRelationQuotient.lean`, and Stacks `spaces.tex`, lemma
`lemma-pullback-etale-equivalence-relation` (02WT), and `groupoids.tex`, lemma
`lemma-quotient-pre-equivalence-relation-restrict` (045Z). The latter explicitly
gives injectivity for any restriction and an isomorphism for a covering restriction;
an étale surjection is an fppf covering. No repair note exists for this item.

Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node text | Lean rendering |
| --- | --- |
| A scheme S | `{S : Scheme.{u}}`, with `universe u` explicitly declared. |
| Schemes U and R over S | `{R U : Over S}`. The two arrows are `s t : R ⟶ U`; being arrows in `Over S` includes compatibility with S. |
| `(s,t)` is a relation, rather than a multivalued collection of arrows | `[Mono (prod.lift s t)]`. Products in `Over S` are fibre products over S. This is precisely uniqueness of a relation arrow with given endpoints. |
| R(T) is an equivalence relation on U(T), for every S-scheme T | `hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦ ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b)`. |
| Both projections are étale | `[Etale s.left] [Etale t.left]`, applied to the underlying scheme morphisms. |
| Any étale g from U' to U | `{U' : Over S}`, `(g : U' ⟶ U) [Etale g.left]`. No surjectivity or monicity of g is assumed here. |
| R' is U' ×[g,U,s] R ×[t,U,g] U' | `restrictedEtaleRelation s t g = pullback (pullback.snd g s ≫ t) g`. The first pullback is `pullback g s`; its R projection followed by t is the map used in the second pullback. |
| The two induced arrows to U' | `restrictedEtaleRelationSource` is the first projection of the second pullback followed by the first projection of the first; `restrictedEtaleRelationTarget` is the second projection of the second pullback. |
| The restricted relation is an equivalence relation | The first conjunct is monicity of the pair of restricted projections. The second is `∀ T : Over S, Equivalence ...` with a witness `r : T ⟶ restrictedEtaleRelation s t g` and both endpoint equations. |
| It is an étale relation | The third and fourth conjuncts are `Etale` of the underlying source and target projections. |
| F and F' are the fppf sheaf quotients | `F F' : Sheaf (Scheme.fppfTopology.over S) (Type u)`. The presheaf quotients are `coequalizer (yoneda.map s) (yoneda.map t)` and its restricted counterpart. The maps `η`, `η'` and universal properties `hη`, `hη'` specify their sheafifications. |
| The canonical map of quotient sheaves | `∃ α : F'.obj ⟶ F.obj` with `q' ≫ α = yoneda.map g ≫ q`, where q and q' are the displayed `coequalizer.π ... ≫ η` and `coequalizer.π ... ≫ η'`. This equality specifies its value on every representative. |
| The map is injective | `Mono α`, for a natural transformation between set-valued presheaves, is equivalent to `Function.Injective (α.app (op T))` at every test scheme. |
| If g is surjective, the canonical map is an isomorphism | `Surjective g.left → IsIso α`. The predicate is the actual underlying topological surjectivity class. An isomorphism of underlying presheaves between sheaves is exactly an isomorphism of sheaves. |

The quotient encoding is the same as the already landed parent
`AlgebraicGeometry.AlgebraicSpace.etale_relation_quotient`, but this module does not
import that downstream theorem. The coequalizer of the two Yoneda maps is the
pointwise quotient of the given equivalence relation. For each sheaf G, `hη`
states that precomposition with η is bijective on morphisms, exactly the
sheafification universal property; the same applies to `hη'`. These binders
specify the quotient objects already named in the node, rather than impose an
extra global sheafification assumption. In particular we do not impose
`HasWeakSheafify` at the value universe of all presheaves on the big site.

The map α is not arbitrary: if α and β satisfy its displayed equation, epimorphy
of the presheaf coequalizer projection gives `η' ≫ α = η' ≫ β`. Injectivity in
`hη' F` gives α = β. Thus the existential conclusion has exactly the canonical
map specified by the source. No `Nonempty` choice or undefined map replaces it.

Dependency declarations used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its morphisms, from
  `Mathlib.AlgebraicGeometry.Scheme` (available through the public geometry imports).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`, and
  `pullback.snd`, from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  scheme pullbacks are supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`, from
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-pc-fppf-site`: `AlgebraicGeometry.Scheme.fppfPrecoverage` and `fppfTopology`,
  from `Mathlib.AlgebraicGeometry.Sites.Fpqc`, and
  `CategoryTheory.GrothendieckTopology.over`, from
  `Mathlib.CategoryTheory.Sites.Over`. This is the induced over-site used by the
  recorded `Scheme.overGrothendieckTopology` construction.
- `def-weil-pbc-sheafification`: the universal property of
  `CategoryTheory.presheafToSheaf`, `toSheafify`, and `sheafificationAdjunction`,
  from `Mathlib.CategoryTheory.Sites.Sheafification`, rendered at the two
  quotient presheaves by `hη` and `hη'`.
- Proof dependencies: the public étale module supplies composition/cancellation
  and stability under base change; the public fppf module supplies covering base
  change. The stated project proof modules are imported without `public`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms` (`Precoverage.IsSiteForCoverings`) and
  `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
  (`CategoryTheory.sheafification_sections_local`). The latter was read with
  `scompile.py --source` because the recorded module is absent locally. Its
  general large-value sheafification theorem can be used after the usual size
  transport; this statement keeps the same quotient interface as the parent.

Edge cases checked:

- Empty S, U, U', and empty test schemes are included. In particular an empty
  U' may give only an injective map; no unconditional isomorphism is claimed.
  A surjection from empty U' forces U empty, so the final clause remains valid.
- For `g = 𝟙 U`, the restricted relation identifies with the original relation
  and the quotient map is the identity under the canonical identifications.
- For a nonmonic étale surjection, for example the fold from two copies of U,
  the pullback relation includes the cross-copy arrows. The theorem therefore
  recovers the same quotient and never mistakenly assumes g is an immersion.
- For the diagonal relation, the restricted relation is the kernel pair of g;
  its quotient maps injectively to U and is U when g is surjective.
- An empty relation over a nonempty U fails `hrel` at reflexivity, as required.
  No separation, finite type, quasi-compactness, nonemptiness, or restriction on
  characteristic is added. `u` is arbitrary; `Over S` has object universe u+1
  and morphism universe u, and the Yoneda presheaves use their actual Type u
  Hom sets. No equality of distinct site universes is imposed.

Searches made (2026-10-17 UTC):

- `msearch.py ... leanfinder`: “An etale equivalence relation restricted along an
  etale morphism has an injective map on fppf quotient sheaves, which is an
  isomorphism when the morphism is surjective”. Eight hits: étale forgetful
  functors, `IsEtale` ingredients and `StandardEtalePresentation.lift_bijective`;
  no relation-quotient restriction theorem.
- `msearch.py ... loogle`: `"AlgebraicGeometry.IsEtale", "quotient"`.
  Successful search, zero hits. The pinned source calls the predicate `Etale`;
  `IsEtale` is its deprecated alias, not the name used in this module.
- `msearch.py ... leansearch`: “Restriction of an etale equivalence relation
  induces an injective map of fppf quotient sheaves and an isomorphism when the
  restriction map is surjective”. Eight hits including `Relation.map_equivalence`,
  `InverseSystem.PEquivOn.restrict` and sheaf local injectivity; none states this.
- `msearch.py ... grep`: `etale.*quotient|quotient.*etale|equivalence.relation`
  in `AlgebraicGeometry`. One hit, `Mathlib/AlgebraicGeometry/Gluing.lean:239`,
  the point equivalence relation for open gluing, not this statement.
- `rg` of the upstream `WeilConjectures/`, project `lean/Sheaf/`, and upstream
  declaration-name index for the item id and proposed names: no duplicate.
  Concept searches `quotient.*relation|relation.*quotient` found the distinct
  parent `EtaleRelationQuotient` and its polarized descent consumer; the parent
  has this item as a proof dependency and cannot supply the item itself.

Validation: `scompile.py N0 lem-trf-etale-relation-restriction-quotient <module>`
compiled the sandbox and library-named file cleanly, including both proof-only
imports. Initial missing-import errors for `GrothendieckTopology.over` were fixed
by importing `Mathlib.CategoryTheory.Sites.Over`. All lines are at most 100
characters; every universe and variable is explicitly bound.

## Second reading by N0

This is a second self-audit by the same dispatched worker, not a claim that a
separate agent reviewed the file. The brief forbids starting other agents and
assigns the independent delivery review to the maintainer.

I reopened the node and the complete final module and checked the table above
in both directions. The iterated pullback's middle map uses t after the R
projection; its source uses the U' projection from the first pullback, while
its target uses the second U' projection. Both endpoint equations therefore
have the correct orientation. The relation includes monicity as well as
equivalence on test points. The four hypotheses concerning étaleness and
relation data are not accidentally inferred or weakened. The two quotient
universal properties specify precisely the sheaf quotients and the displayed
equation uniquely pins down the canonical map. Monicity gives injectivity on
every test scheme, and surjectivity of g is used only in the final implication.
No mathematical mismatch was found, so the node statement is unchanged. The
only compiler repair was the over-topology import; the proof-only source
imports were then added and the final file recompiled cleanly.
