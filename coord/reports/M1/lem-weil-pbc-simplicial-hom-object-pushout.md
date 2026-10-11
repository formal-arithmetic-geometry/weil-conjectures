## Worker report

The dependency module `SimplicialHomObjectFixed.lean` bundles a chosen representing object, its universal compatible family, and the representing property for the degree-zero Hom functor. It uses `exists_simplicial_hom_object` and contains no proved result beyond the existing existence theorem.

The item module defines `simplicialHomMap`, contravariant in a simplicial-set map, by the universal property. The theorem `simplicialHomObject_pushout_isPullback` states that for admissible A, B, C, D and a simplicial pushout square, the induced Hom maps form a categorical pullback. The theorem `simplicialHomObject_pushout_empty_isProduct` states the empty-common-part case as existence of the binary product limit. Every finiteness and nonemptiness hypothesis is explicit for each admissible simplicial set; the empty case uses `IsEmpty` degreewise for A.

The pushout hypothesis is `CategoryTheory.IsPushout p q i j`; the pullback conclusion is `CategoryTheory.IsPullback` on the four induced maps. The product conclusion is `Nonempty (IsLimit (BinaryFan.mk ...))`, the propositional form of the universal property. Proofs are `sorry` as required for stage 2.

Dependencies used: `Sheaf.AlgebraicGeometry.SimplicialHomObjectFixed`, declarations `SimplicialHomObjectData` and `simplicialHomObjectData`; `Sheaf.AlgebraicGeometry.SemiRepresentableObject`, via the existing formal coproduct category and finite-limit instance; Mathlib `SSet`, `SSet.Finite`, `CategoryTheory.IsPushout`, `CategoryTheory.IsPullback`, `BinaryFan`, and `IsLimit`.

Edge cases checked: degreewise finite nonempty admissible sets; the empty common simplicial set is handled separately with degreewise `IsEmpty`; no restriction on the scheme, simplicial-object degrees, or universes beyond explicit universe parameters.

Searches made: `rg` over Mathlib simplicial-set files and project `lean/Sheaf` found no Hom-object pushout declaration; `msearch.py` searches for simplicial Hom pushouts and expected categorical names found only unrelated simplicial-set limits and generic pushout/pullback APIs. The recorded Hom-object dependency declaration was a functor only, so a dependency module was required.

## Dependency modules

`def-weil-pbc-simplicial-hom-object`: its recorded declaration `simplicialHomFamilyFunctor` gives only the presheaf of families, not the node's fixed representing object and universal family. `SimplicialHomObjectFixed.lean` states the node's full representing pair as a structure and chooses it from the existing existence theorem.

## Earlier second reading (a previous round; superseded)

The node and both files were read together. The admissibility clauses are rendered by explicit `Finite` and `Nonempty` hypotheses degree by degree, the pushout clause by `IsPushout`, and the two conclusions by `IsPullback` and binary-product `IsLimit`. The empty case is separated and uses `IsEmpty` degreewise. No hypotheses or categorical maps are hidden in local notation; all universes and variables are bound explicitly.

## Second reading by M1

This reading supersedes the worker's proposed dependency module and map definition.
I read the item and all three statement dependencies, the source of the existing
Hom-family declarations, the Hom-object existence statement, Mathlib's SSet.Finite
and IsRepresentedBy, and the formal-coproduct/etale-category signatures. I read
Stacks simplicial.tex Section 017H, Definition 017I, Lemmas 017J/017K and 017N,
and hypercovering.tex Lemma 01GM, including its n = 0 argument. The local Stacks
source is in the c1-stacks-review source mirror; the logical source places remain
those recorded in the node. No statement correction is needed.

The node's objects, hypotheses and conclusions, matched in order:

- X is any scheme: `{X : Scheme.{u₁}}`. No field, characteristic, finiteness,
  separatedness or nonemptiness assumption. Verdict: exact.
- SR(X) is the category of formal families in the small etale site:
  `FormalCoproduct.{w₁} X.Etale`, exactly the dependency's category, not schemes
  or sheaves substituted for formal families. K is its simplicial object:
  `{K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)}`. Verdict: exact.
- A, B, C, D are simplicial sets: `{A B C D : SSet.{t₁}}`. Admissibility is
  `[S.Finite]` (Mathlib: finite total set of nondegenerate simplices), together
  with `hSfin` and `hSne` quantifying over every natural degree. Both theorems
  require B, C, D admissible; only (a) requires A admissible. Verdict: exact.
- H(S) and its universal family: implicit `HA`, `HB`, `HC`, `HD`, families
  `uA`, `uB`, `uC`, `uD : SimplicialHomFamily ...`, and `huA`/`huB`/`huC`/`huD`
  using the dependency's `(simplicialHomFamilyFunctor K S).IsRepresentedBy uS`.
  The family subtype includes every simplicial compatibility equation, and
  IsRepresentedBy says precisely that precomposition with this family is
  bijective for every W. Thus these are arbitrary fixed representing pairs,
  as in the node and the already landed sibling Hom lemmas. Existence is the
  recorded `exists_simplicial_hom_object`, not a new assumption about K.
  Verdict: exact; no second definition is needed.
- The induced contravariant maps: `iStar`, `jStar`, `pStar`, `qStar` have exactly
  the sources and targets of i*, j*, p*, q*. Equations `hi`, `hj`, `hp`, `hq`
  quantify over all degrees and simplices and read `fStar ≫ uS.val n s =
  uT.val n (f.app (op ⦋n⦌) s)`. These characterize the maps named in the node;
  they impose no extra geometric condition. Compatibility follows from the
  naturality of f; representation gives existence and uniqueness. Inclusions
  give exactly the existing `simplicialHomRestriction`. Verdict: exact.
- p, q, i, j form the stated simplicial pushout: typed morphism binders and
  `hpush : CategoryTheory.IsPushout p q i j`. No injectivity is required.
  Verdict: exact.
- Clause (a): `CategoryTheory.IsPullback iStar jStar pStar qStar` states that
  HD with those very projections is a fibre product, including commutativity
  and the universal property. Verdict: exact, not merely an abstract isomorphism.
- Clause (b): `hAempty : ∀ n, IsEmpty (A.obj (op ⦋n⦌))` replaces admissibility
  of A; `Nonempty (IsLimit (BinaryFan.mk iStar jStar))` states precisely the
  product universal property of HD and these projections. It assumes no H(A).
  Verdict: exact; Nonempty only makes the universal-property witness propositional.

Edge cases: A empty is covered by (b), including the empty boundary for n = 0
in 01GM. All maps out of the empty simplicial set are allowed. Empty B or C
are excluded exactly by the node's admissibility, not by an added assumption.
Degree zero is included in every degreewise binder. The empty scheme and empty
formal family are not excluded. There is no characteristic restriction.
Independent u₁, w₁, t₁ permit arbitrary scheme, family-index and simplex universes;
IsRepresentedBy is the universe-general version of representation, so no small
universe of test objects or test morphisms is silently substituted.

Independent searches used different words: LeanFinder, “cotensor of simplicial
object sends colimits of simplicial sets to limits”, returned SSet's monoidal
closed structure and generic simplicial limits/colimits, not this statement.
LeanSearch, “representing compatible families indexed by simplices takes a pushout
to a pullback”, was unavailable (HTTP Internal Server Error), recorded as such.
Loogle `CategoryTheory.IsPullback, CategoryTheory.SimplicialObject` returned no hits.
The msearch grep `cotensor|weightedLimit|homFromSSet` in AlgebraicTopology had no
hits. Direct rg for these notions, homFrom, simplicialHom and the proposed
structure in Mathlib CategoryTheory/AlgebraicTopology, WeilConjectures and
lean/Sheaf found the existing Hom-family API and sibling Hom lemmas, but no
pushout statement. Those existing declarations were opened and used.

Mismatches repaired: (H4/H13) the proposed dependency structure re-encoded the
already available representing-pair notion. Removed its module and dependency
node copy; imported the existing SimplicialHomObject module and used its families,
functor and Mathlib IsRepresentedBy directly. (H6) the proposed simplicialHomMap
contained a proved compatibility lemma inside its definition. Removed this
unnecessary definition; maps are now specified by the node's own universal-family
equations, as the landed sibling statements do. (H8) expanded both theorem
docstrings with the corresponding numbered proof steps and dependency names;
the empty-case theorem previously lacked its proof. No new nodes or dependency
modules remain. No hollow data, private copies, local instances, local notation,
let-bindings or hidden casts remain. Every theorem proof is sorry.

The recorded lean.statement is verbatim the first theorem signature. Local
single-file compilation passed cleanly (exit 0); final server compilation and
preflight are performed by deliver2.py.
