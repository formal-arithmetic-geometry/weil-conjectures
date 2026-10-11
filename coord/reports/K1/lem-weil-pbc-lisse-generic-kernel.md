## Worker report

The module `Sheaf.AlgebraicGeometry.LisseGenericKernel` states
`AlgebraicGeometry.Scheme.mono_of_mono_generic_stalk`. It introduces a scheme `X`,
nonempty irreducible underlying space with generic point `η`, an algebraically closed
field `Ω`, a geometric point `barη` whose image is `η`, sheaves `F` and `G` of
abelian groups on the small étale site, local constancy of `F`, and a morphism `φ`.
The hypothesis `hφ` is monomorphy of the induced geometric generic stalk map, and
the conclusion is monomorphy of `φ`. `AbelianEtaleSheaf` is the dependency module's
precise encoding `Sheaf X.smallEtaleTopology AddCommGrpCat`.

The Lean binders render each clause as follows: `(X : Scheme.{u₂})` is the scheme;
`hX : IsIrreducible (Set.univ : Set X)` and `hne : Nonempty X` are irreducibility
and nonemptiness; `η : X` and `hη : IsGenericPoint η (Set.univ : Set X)` specify
the generic point; `Ω` with `[Field Ω] [IsAlgClosed Ω]` is the algebraically closed
residue field; `barη : Spec (.of Ω) ⟶ X` and `hbarη : barη default = η` specify the
geometric point over η; `F G : AbelianEtaleSheaf X` are abelian étale sheaves;
`[IsLocallyConstantSheaf F]` is local constancy; `φ : F ⟶ G` is the morphism; and
`Mono ((pointSmallEtale barη).sheafFiber.map φ)` is injectivity at the geometric
stalk, with conclusion `Mono φ`.

Dependency declarations used are
`Sheaf.AlgebraicGeometry.AbelianEtaleSheaves`, declaration
`AlgebraicGeometry.Scheme.AbelianEtaleSheaf`, and Mathlib's
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` for geometric stalks.
The existing `EtaleSheaves.lean` record was unusable for this dependency because it
only records set-valued local-constancy predicates; the dependency module supplies
the abelian sheaf category required by the node. `def-weil-pbc-scheme-conventions`
is used for scheme and geometric-point conventions.

Edge cases checked: `Nonempty X` permits the empty scheme to be excluded as required;
`IsIrreducible Set.univ` permits the one-point scheme; no finiteness or characteristic
hypothesis is introduced; `Ω` is quantified in the same universe as `X`; zero sheaves
and empty sections remain allowed.

Searches made: `msearch.py leanfinder` for a generic-stalk monomorphism found only
`TopCat.Presheaf.mono_of_stalk_mono`, `TopCat.Presheaf.mono_iff_stalk_mono`, and
locally-injective sheaf results (no exact étale result); `msearch.py loogle` for
`Sheaf, Presheaf, Mono, stalk` returned 0 hits; `msearch.py grep` for
`locally constant.*stalk|geometric.*stalk.*mono` returned no match; LeanSearch was
unavailable (Internal Server Error). Repository searches found no declaration of this
node or its theorem. Mathlib's `pointSmallEtale`/`sheafFiber` was read at
`Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean:64-65` and
`Mathlib/CategoryTheory/Sites/Point/Basic.lean:277-278`.

## Original proposed dependency module (removed in second reading)

`def-weil-pbc-etale-sheaves` receives `Sheaf.AlgebraicGeometry.AbelianEtaleSheaves`.
Its prior mixed record only provided set-valued local-constancy declarations and did
not provide the abelian sheaf category stated by the dependency; the new abbreviation
states exactly that category.

## Earlier second reading (a previous round; superseded)

I reread the target node and module. The nonempty irreducible scheme, chosen generic
point, geometric point over it, locally constant abelian sheaf, arbitrary abelian
étale sheaf, morphism, generic-stalk injectivity, and monomorphism conclusion all
appear as explicit Lean binders or the final proposition. The dependency module was
also reread: it defines precisely the category of abelian sheaves used by `F` and `G`.


## Second reading by K1

I opened the item's node and Lean module together, and read the original blueprint
source on the server at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-lisse-generic-kernel.md`.
Its statement agrees verbatim with the node. This item's source is a blueprint lemma,
not a Stacks tag; it assumes no ambient Noetherian, finiteness, reducedness, base-field,
or characteristic conditions. Its proof has the two steps transcribed into the final
docstring. No statement correction was needed.

Object/hypothesis/conclusion checklist, in the order of the source:

- Scheme S: `(X : Scheme.{u₂})`. Same arbitrary scheme; pass.
- Nonempty and irreducible: `(hX : IsIrreducible (Set.univ : Set X))`
  and `(hne : Nonempty X)`. Same topological condition; pass. The explicit
  nonemptiness is redundant with irreducibility and the chosen point, but matches
  the source and imposes no new condition.
- Generic point η: `(η : X)` and
  `(hη : IsGenericPoint η (Set.univ : Set X))`. Same point and genericity; pass.
- Fixed geometric point over η: `(Ω : Type u₂) [Field Ω] [IsAlgClosed Ω]`,
  `(barη : Spec (.of Ω) ⟶ X)` and `(hbarη : barη default = η)`.
  Spec of a field has one point, so this equality is exactly the condition on the
  image. Algebraic closedness is the geometric-point convention, not an added
  assumption on X. Pass.
- Abelian étale sheaves F and G:
  `(F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u₂ + 1})`. The Mathlib
  `CategoryTheory.Sheaf` is the full subcategory of presheaves satisfying
  `Presheaf.IsSheaf`; `X.smallEtaleTopology` is the small étale site. This is the
  precise specialization recorded by `def-weil-pbc-abelian-etale-sheaves`, whose
  statement, mathlib_match and lean record I opened. Pass after removing the
  redundant private abbreviation.
- F locally constant: `[IsLocallyConstantSheaf F]`; no condition on G.
  I read `LocallyConstantDatum` and `IsLocallyConstantSheaf` in
  `WeilConjectures/ConstructibleSheaf/Defs.lean`: a jointly surjective étale cover,
  and `F.over` constant on each localized site, with no extra sheafification.
  Specializing its coefficient category to AddCommGrpCat supplies all its
  Grothendieck/abelian/sheafification instances; none is an extra binder. Pass.
- Morphism: `(φ : F ⟶ G)`. A natural transformation of the same abelian sheaves;
  pass.
- Injective chosen generic stalk map:
  `(hφ : Mono ((pointSmallEtale barη).sheafFiber.map φ))`. I opened
  Mathlib `EtalePoint.lean` at `pointSmallEtale`, and `Point/Basic.lean` at
  `presheafFiber` and `sheafFiber`: the point fibre is lifts to étale neighbourhoods,
  and the stalk is the colimit over the opposite category of elements. This is
  exactly the recorded `def-weil-pbc-geometric-stalks` declaration, which I read.
  The map is in AddCommGrpCat, where `AddCommGrpCat.mono_iff_injective` identifies
  Mono with injectivity of its underlying group map. Pass.
- Conclusion: `Mono φ`. Exactly monomorphy of the given morphism; pass.

I also read `def-weil-pbc-scheme-conventions`: it fixes no new notion and points to
Mathlib schemes and geometric points with algebraically closed fields. The recorded
`def-weil-pbc-etale-sheaves` module `EtaleSheaves.lean` supplies set-valued predicates;
the arbitrary-coefficient abelian local-constancy notion required here already exists
in the source module above. No dependency replacement is needed.

Edge cases: the empty scheme is excluded by the source, and the chosen η already
excludes it. A one-point irreducible scheme, nonreduced schemes, zero F or G,
infinite abelian groups, and empty values of sheaves remain allowed. There is no
integer parameter, finite index set or positive-rank requirement. The scheme universe
u₂ is arbitrary; Ω is in the same universe as the schemes of the small site, with
abelian groups in u₂+1, exactly the universes of the recorded sheaf and stalk
specializations. There is no fixed universe level or restriction on characteristic.

Independent searches (different wording from the worker):

- `msearch.py ... leanfinder "injective generic fiber locally constant sheaf
  irreducible scheme"`: eight hits, all about integral structure-sheaf germs,
  function fields or germ-injective schemes, none this theorem.
- `msearch.py ... loogle "CategoryTheory.Mono,
  CategoryTheory.GrothendieckTopology.Point.sheafFiber"`: zero hits.
- `msearch.py ... leansearch "a locally constant etale sheaf embeds if its generic
  stalk embeds"`: service unavailable, Internal Server Error (no verdict inferred).
- `rg` in Mathlib AlgebraicGeometry and CategoryTheory/Sites for
  `mono.*stalk|stalk.*mono|generic.*stalk`: only unrelated scheme stalk criteria.
  `rg` in the source WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json for generic-stalk/mono wording, the item id and
  `AbelianEtaleSheaf`: no existing statement; project hits are uses in
  ConstructibleFiniteSelection or unrelated structure-sheaf statements.

Mismatches and repairs:

1. H4/H13: the proposed dependency module `AbelianEtaleSheaves.lean` only restated
   one category clause of the much larger `def-weil-pbc-etale-sheaves`, and duplicated
   the already usable Mathlib specialization recorded on
   `def-weil-pbc-abelian-etale-sheaves`. Removed that module and its dependency node
   copy. Replaced its abbreviation in F/G by the recorded `Sheaf` specialization,
   and added the existing abelian-sheaf node to the item's stmt_deps. The original
   worker discussion above describes the superseded proposal, not the final delivery.
2. H8: the original proof docstring compressed away cofinality, lifting of geometric
   points, filtered-colimit refinement, and the nonzero constant germ contradiction.
   Expanded it step by step with the cited nodes. Added the module blueprint marker.
3. Removed imports made redundant by the source Defs import. No mathematical binder
   was changed, and no proof was filled. The sole theorem retains `by sorry`;
   there are no new definitions or dependency modules in the final delivery.

The node's lean.statement was regenerated verbatim from the final signature.
`scompile.py K1 lem-weil-pbc-lisse-generic-kernel .../LisseGenericKernel.lean`
compiled on the server in 1.8 seconds with no errors or warnings. All identifiers
and the sole universe are explicitly bound.
