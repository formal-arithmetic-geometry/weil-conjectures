## Worker report

The module `Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion` states
`AlgebraicGeometry.gabber_h0_etale_criterion`, with a single `sorry` proof and no new
mathematical definition. Its docstring carries every step (0–10) of the node's proof,
including the final check that the descended section restricts to the original section.
The source is Stacks Project, Lemma 59.82.2, Tag 09ZF:
https://stacks.math.columbia.edu/tag/09ZF . The local literature checkout lacks the TeX
file, so the full statement and proof were read on that official page.

Hypotheses and clauses:

- A scheme X: `{X Z : Scheme.{u}}`, with explicit universe `u`.
- X quasi-compact: `[CompactSpace X]`, the topological meaning of quasi-compactness.
- X quasi-separated: `[QuasiSeparatedSpace X]`, as in the scheme-conventions node.
- A closed immersion i: `(i : Z ⟶ X) [IsClosedImmersion i]`.
- Every sheaf G of sets on the Zariski space: `∀ G : TopCat.Sheaf (Type (u + 1))
  X.toTopCat` in `hZar`. These are genuine sheaves, not arbitrary presheaves.
- The canonical restriction on global sections is bijective: `Function.Bijective`
  applied to the `.unit.app G` of
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map i.base) ...`,
  on underlying presheaves (`.hom.app`), evaluated at `op (⊤ : X.Opens)`.
  The target is the sheaf inverse image evaluated at the inverse image of the top open,
  which is the top open of Z. This is precisely the unit of the prescribed
  left-Kan-extension followed by sheafification construction.
- Every finite morphism: `∀ (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h]` in `hFinite`.
- The base-changed closed subscheme: `(pullback i h : Scheme.{u})` is Z times_X X',
  and `pullback.snd i h` is its projection to X'. The local functor `b` is `Opens.map`
  of that projection's underlying continuous map. No surjectivity, presentation,
  affineness, connectedness or additional condition on h is imposed.
- The same assertion for every Zariski set sheaf on X': `∀ G : TopCat.Sheaf
  (Type (u + 1)) X'.toTopCat` and the corresponding constructed-adjunction unit at
  `op (⊤ : X'.Opens)` in `hFinite`.
- Every sheaf F of sets on the small etale site of X: `(F : Sheaf
  X.smallEtaleTopology (Type (u + 1)))`.
- Canonical etale restriction is bijective: `Function.Bijective ((adj.unit.app F).hom.app
  (op (Scheme.Etale.mk (𝟙 X))))`. The local `adj` has left adjoint the existing
  `Scheme.etaleSetPullback i` and right adjoint sheaf pushforward along etale base change.
  It is exactly the recorded construction's `sheafAdjunctionContinuous`. Its target
  is inverse-image sections on the base change of the terminal etale object, which is
  terminal over Z and canonically isomorphic to Z. Thus bijectivity is equivalent to
  bijectivity of the canonical map to global sections on Z, without a choice of sections
  or an arbitrary comparison bijection.

The `letI` expressions in the two Zariski assumptions introduce no hypotheses: they
supply Mathlib's `Types.hasColimit` for the pointwise Kan-extension diagrams. Their
index categories have objects and homs in universe u and therefore are small in u+1
by `small_succ`. The explicit category and universe annotations prevent unresolved
universe parameters in typeclass inference. The coefficient universe u+1 accommodates
sheaves on the large small etale site and arbitrary sets at that level; u is arbitrary,
as in the existing project convention for set-valued etale sheaves. No auto-implicit
variables or universes are used.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` fixes no private declaration. The Mathlib notions
  `Scheme`, `CompactSpace`, `QuasiSeparatedSpace` render its applicable conventions.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; its signature and docstring
  specify the closed embedding and surjective stalk maps.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`; its signature and docstring specify
  affine inverse images and finite ring maps. The integral part is not used by this item.
- `def-weil-pbc-topological-inverse-image`:
  `CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `Mathlib.CategoryTheory.Sites.Pullback`, specialized to opens and sets.
  Read its full definition and that of its left adjoint; use the constructed adjunction,
  not the abstract chosen `TopCat.Sheaf.pullback` adjunction.
- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.smallEtaleTopology` and
  `AlgebraicGeometry.Scheme.Etale`, `Mathlib.AlgebraicGeometry.Sites.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; signatures and docstrings read.
- `def-weil-pbc-inverse-image`: the recorded `AlgebraicGeometry.Etale.upperStar` and
  `Etale.upperStarLowerStarAdjunction` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` were read in full. They require
  abelian/Grothendieck abelian coefficients and therefore are not applicable to sets.
  Their left-Kan-extension/sheafification construction and unit are reused directly
  through Mathlib's general construction. The source module also provides the
  continuity instance `Etale.isContinuous_overPullback` used here.
- The already-landed node `def-weil-pbc-etale-sheaves` is added to `stmt_deps`:
  `AlgebraicGeometry.Scheme.etaleSetPullback`, in
  `Sheaf.AlgebraicGeometry.EtaleSheaves`, already gives the needed set-valued inverse
  image with exactly that construction. Its signature and docstring were read.
  No dependency module or new definition node is needed: the original inverse-image
  dependency correctly states its own abelian notion and the sets specialization is
  already available from this landed node.

Edge cases checked before writing: X and Z may be empty; no nonemptiness is imposed.
If X is empty, so is Z, and both global-section sets of any sheaf are singletons.
If Z is empty and X is not, hZar fails for the constant two-element sheaf, as it should.
The identity immersion and identity finite map are permitted. Finite maps with empty
source and finite non-surjective maps are included, with no hidden surjectivity
assumption. Arbitrary disconnected schemes and arbitrary sheaves (including those
with no global sections) are included. There is no characteristic, base field,
coefficient torsion, or Noetherian hypothesis. Hypothesis (1) is retained although
hypothesis (2) includes the identity finite morphism, exactly as in the source.
No statement correction, hollow definitions, or STATEMENT-DISPUTED issues.

Searches for the existing statement (all real service queries logged in searches.jsonl):

- `msearch.py leansearch`: "Gabber criterion bijective global sections etale sheaves
  closed immersion Zariski finite base change". Service returned Internal Server Error;
  unavailable, no verdict assigned.
- `msearch.py leanfinder`: "Gabber degree zero etale cohomology restriction bijective
  Zariski sheaves finite morphisms". Eight hits, including
  `StandardEtalePresentation.lift_bijective` and `RingHom.Etale.of_bijective`; all concern
  ring maps rather than the sheaf statement and do not match.
- `msearch.py loogle`: "Functor.sheafPullback, Function.Bijective". No hits;
  unknown identifier reported by the service.
- `msearch.py grep`: "gabber|bijective.*[Ss]heaf" over Mathlib. Twenty-one hits,
  chiefly Gabber bibliographical references and stalkwise criteria for topological
  sheaf morphisms; none is this criterion.
- `rg` over the source WeilConjectures for "gabber|Gabber" and the exact item id:
  found affine Gabber cohomological comparison/effacement and perverse operations,
  no degree-zero criterion; exact id absent.
- `rg` over project lean/Sheaf for "sheafPullback|gabber|Gabber" and
  "gabber_h0_etale_criterion|Gabber.*criterion|degree-zero criterion": no existing
  statement. The former search found `Scheme.etaleSetPullback`, which is reused.
- `rg` over `dag/lean_names_upstream.json`: no declaration for this item or chosen
  declaration name. The existing etale-sheaves node was inspected to verify its
  recorded `etaleSetPullback` declaration.

Validation: server `scompile.py` succeeded with exit code 0, no errors or warnings;
only one theorem with a `sorry` proof is delivered. The delivery dry run is the final
mechanical check; the independent second reader supplies their own section later.


## Second reading by E1

I independently opened the item node, its delivered Lean module, every statement-dependency
node, and the relevant dependency declarations. The local Stacks checkout is absent;
I read both the official [Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF) page and
`lemma-gabber-h0` with its complete proof in the upstream
[etale-cohomology.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex).
The source introduces exactly the qcqs scheme and closed immersion in the node, and
has no standing Noetherian, base-field, torsion, separatedness or characteristic assumption.
No statement correction is present or needed.

The objects, hypotheses and conclusion, matched individually:

| Node item | Lean rendering | Verdict |
|---|---|---|
| Schemes X and Z | `{X Z : Scheme.{u}}` | Same arbitrary schemes. |
| X quasi-compact | `[CompactSpace X]` | Correct topological quasi-compactness; no Hausdorff condition. |
| X quasi-separated | `[QuasiSeparatedSpace X]` | Correct: Mathlib's `quasiSeparatedSpace_iff_quasiSeparated` identifies this with quasi-compact diagonal. |
| A closed immersion i: Z to X | `(i : Z ⟶ X) [IsClosedImmersion i]` | Correct closed embedding and surjective stalk maps, by the opened `ClosedImmersion.lean` signature. |
| Every Zariski sheaf G of sets on X | `∀ G : TopCat.Sheaf (Type (u + 1)) X.toTopCat` in `hZar` | Genuine arbitrary set-valued sheaves; no local constancy or finiteness restriction. |
| Canonical restriction on Zariski global sections is bijective | `Function.Bijective` of the constructed `sheafAdjunctionContinuous` unit at `op (⊤ : X.Opens)` | Correct canonical map: Kan-extension unit followed by sheafification, with target evaluated at the inverse image of the top open, namely the top open of Z. |
| Every finite h: X' to X | `∀ (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h]` in `hFinite` | Correct: opened `Finite.lean` defines affine inverse images and finite affine-local ring maps. No surjectivity or finite presentation added. |
| The base-changed immersion Z times_X X' to X' | `pullback i h`, `pullback.snd i h`, and `b = Opens.map (pullback.snd i h).base` | Correct fibre product and projection; reversing the source's product order only uses the canonical symmetry. |
| Same assertion for every Zariski set sheaf on X' | `∀ G : TopCat.Sheaf (Type (u + 1)) X'.toTopCat`, followed by unit bijectivity at `op (⊤ : X'.Opens)` | Correct, with the quantifiers in the source's order: finite morphism first, then all sheaves. |
| Every sheaf F of sets on the small etale site of X | `(F : Sheaf X.smallEtaleTopology (Type (u + 1)))` | Correct: opened `Scheme.Etale` and `smallEtaleTopology` use etale X-schemes and jointly surjective etale covers. |
| Canonical etale global-section restriction is bijective | `Function.Bijective ((adj.unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 X))))` | Correct canonical inverse-image unit; the base change of the terminal X-object is terminal over Z, canonically isomorphic to its identity object. Composing with this isomorphism gives exactly the source's global-section map. |

I read `Functor.sheafPullbackConstruction.sheafPullback` and
`sheafAdjunctionContinuous` in `Mathlib/CategoryTheory/Sites/Pullback.lean`: the left
adjoint is inclusion into presheaves, left Kan extension, then sheafification, and
the adjunction is the composite restricted along the fully faithful inclusion.
Thus the maps here are the specified construction's units, not arbitrary bijections
or an independently chosen inverse image. The `letI` binders give actual
`Types.hasColimit` constructions; they are not extra hypotheses or hollow definitions.

I also opened `Etale.upperStar` and `Etale.upperStarLowerStarAdjunction` in the source
`UpperLowerStar/Defs.lean`. Their section requires an abelian Grothendieck coefficient
category, so they cannot be used for sets. The delivered module instead uses the
already-landed `Scheme.etaleSetPullback` from `def-weil-pbc-etale-sheaves`, whose full
signature and body I opened in `EtaleSheaves.lean`: exactly the same Kan-extension
and sheafification construction at `Type (u + 1)`. Adding this landed node to
`stmt_deps` is justified. The older inverse-image node states an abelian notion and
needs no replacement. There are no new nodes or dependency modules in this delivery,
and no missing notion, private copy, or hollow definition.

Edge cases: empty X and Z are permitted, as are empty finite sources, identity maps,
non-surjective finite maps and disconnected schemes. When X is empty the sheaf
condition makes its global-section sets singleton; when Z is empty and X nonempty,
the constant two-element Zariski sheaf contradicts `hZar`, as required. Arbitrary
set sheaves, including initial sheaves and sheaves without global sections, are
included. There is no coefficient group, ring, positive degree or n parameter, so
zero objects, n = 0 and characteristic impose no omitted case. Universe `u` is
explicit and arbitrary; coefficients use the established `u + 1` convention of
the dependency. This supports both the etale site and all the opens indexing
categories, and smaller sets can be lifted to that universe. There is no independent
smaller test universe making either universal hypothesis vacuous. No unbound
variable or universe appears.

Independent searches (different queries from the worker's; service calls logged):

- LeanFinder: "closed subscheme restriction global sections sheaves finite morphisms
  Zariski etale bijection" returned eight affine/immersion structure-sheaf results,
  none this theorem.
- Loogle: `Function.Bijective, CategoryTheory.Sheaf` returned
  `SheafOfModules.bijective_pushforwardSections`; I opened its signature, which
  assumes a final functor and concerns module-sheaf pushforward sections, not this
  etale/Zariski criterion. The initial unqualified `Sheaf` query was rejected as
  an unknown identifier.
- LeanSearch: "Bijective restriction from etale sheaf global sections to a closed
  subscheme assuming Zariski restriction for every finite base change" was unavailable
  (Internal Server Error); no mathematical verdict inferred from that failure.
- `rg` over Mathlib's algebraic-geometry and topological-sheaf trees, project
  `lean/Sheaf`, and source `WeilConjectures` for `09ZF`, Gabber, and both orders of
  sheaf/bijectivity found no exact statement. I opened the apparent source match
  `SixFunctors/Etale/BaseChangeTheorems/DegreeZero.lean`: it treats module sheaves
  on proper schemes over henselian rings, a different specialization, not this
  arbitrary closed-immersion criterion. The source `Gabber.lean` results concern
  henselian affine cohomological comparison, not this statement. The chosen full
  declaration name is absent from `dag/lean_names_upstream.json` and those trees.

The theorem docstring matches all eleven node proof steps (0–10): notation and
base-change permanence; injectivity; meeting closed subsets; local section
representatives; shrinking to obtain equality; surjective etale cover; finite
refinement; compatibility of pulled-back sections; Zariski gluing and lifting;
equality on the double fibre product; finite descent and the final restriction
check. Both module and theorem docstrings give Tag 09ZF and the blueprint id.
The only proof is the named theorem's `sorry`; there is no proved helper.
I checked the header, namespace, imports, line lengths, and signature record:
`lean.statement` is verbatim identical to the complete theorem signature.

No mathematical mismatch was found, and no Lean or node edit was made. The only
change is this independent second-reading report. Fresh server `scompile.py`
validation succeeded: exit code 0, compiled in 2.1 seconds, no warnings or errors.
