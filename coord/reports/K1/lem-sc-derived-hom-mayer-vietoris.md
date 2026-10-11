## Worker report

Repaired all five points of return R-dmv1022. The retained statement correction
asserts exactness at global Hom and the pair of local Hom groups, without asserting
surjectivity onto overlap Hom. Source: [Stacks Tag 08BW](https://stacks.math.columbia.edu/tag/08BW).

Hypothesis and clause correspondence:

- Ringed space: `X : RingedSpace.{u}`, with no local-ring hypothesis.
- Two open subspaces covering X: `U V : Opens X`, `hcover : U ⊔ V = ⊤`.
- Structure sheaf of rings: the transparent expression abbreviation `moduleRings X`
  is exactly `(sheafCompose (Opens.grothendieckTopology X)
  (forget₂ CommRingCat RingCat)).obj X.sheaf`, as in the merged stalk siblings.
- D(O_X): `DerivedCategory (SheafOfModules.{u} (moduleRings X))`.
  Likewise for the opens: `SheafOfModules.{u} ((moduleRings X).over U)`,
  `.over V`, and `.over (U ⊓ V)`, each with its own explicit `HasDerivedCategory.{w}`.
  These instances choose the localization, as in `def-weil-abstract-derived-category`;
  they impose no geometric restriction.
- Any E,F: both belong to that fixed global derived category. There is no arbitrary C.
- Restrictions: the three let-bound functors are exactly
  `(SheafOfModules.overFunctor R U).mapDerivedCategory`, and similarly V and U ⊓ V.
- Global Hom to the direct sum: `fun f => (R_U.map f, R_V.map f)`.
  A product of two additive Hom groups is their finite direct sum.
- Local Hom to overlap Hom: `derivedOpenHomRestriction` applies
  `(SheafOfModules.overMap R i).mapDerivedCategory.map` and conjugates by the
  canonical derived lift of `SheafOfModules.overFunctorMap R i`.
  The inclusions are `homOfLE inf_le_left` and `homOfLE inf_le_right`.
  The second arrow subtracts these two restrictions. Neither is existential.
- Preceding negative Ext: `R_UV.obj E ⟶ (R_UV.obj F)⟦(-1 : ℤ)⟧`.
- Connecting map: only `negExt` remains existential; it is additive (`→+`).
- Exactness at global Hom: the first `Function.Exact` takes `negExt` followed by
  the pair of actual restrictions.
- Exactness at the direct sum: the second `Function.Exact` takes the same pair
  followed by the difference of the canonical overlap restrictions.

The canonical transport is fully defined, with no sorry data. Private helper
`derivedCompIso` uses `Localization.liftNatIso` and the factorization isomorphisms
`mapDerivedCategoryFactors`, together with `Functor.mapHomologicalComplexCompIso`.
The six named sorry'd lemmas supply additivity, preservation of finite limits,
and preservation of finite colimits for `overFunctor` and `overMap` on opens.
Their instance wrappers use those lemmas, rather than adding exactness hypotheses
to the main theorem. Their docstrings explain sectionwise sums and kernels and
compatibility of sheafification of cokernels with open restriction. All sorry'd
lemmas belong to this item's restriction-map construction.

Dependency declarations read and used: `def-weil-sheaf-of-modules-category`:
`SheafOfModules` in Mathlib.Algebra.Category.ModuleCat.Sheaf and its Abelian
instance in Sheaf.Abelian; `def-weil-abstract-derived-category`: `DerivedCategory`,
`HasDerivedCategory`, and `Q` in Mathlib.Algebra.Homology.DerivedCategory.Basic;
`def-weil-locally-ringed-space-morphism`: the ringed-space part uses `RingedSpace`
in Mathlib.Geometry.RingedSpace.Basic. The leaf's recorded `LocallyRingedSpace.Hom`
is not a binder needed here: the node explicitly includes the underlying ringed-space
notion, and Tag 08BW does not require local stalks. Restrictions use
`SheafOfModules.overFunctor`, `.overMap`, `.overFunctorMap` from
Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.

Edge cases: empty X, empty overlap, either open empty, equal opens, an open equal
to X, and zero E or F are allowed. The cover is the sole geometric hypothesis.
No separation, finiteness, boundedness, or local-ring assumptions are added.
All universe variables are explicitly declared; module and scalar universes are
u as in the merged siblings, and derived Hom has explicit universe w.

Searches in this repair:

- `msearch.py leanfinder`: “Mayer Vietoris exact sequence derived Hom ringed space
  restriction”: eight hits, chiefly `MayerVietorisSquare.shortComplex_exact`, with
  no derived Hom sequence.
- `msearch.py loogle`: `SheafOfModules.overFunctor, SheafOfModules.overMap`: found
  `SheafOfModules.overFunctorMap`, which is used for the canonical transport.
- `msearch.py grep`: `Mayer.Vietoris.*Hom|derived_hom_mayer|overFunctor.*[Aa]dditive`:
  three hits in sheaf cohomology files, none the required statement or instances.
- `rg` of Mathlib's DerivedCategory, Localization, and Homology.Additive sources:
  found `mapDerivedCategory`, its factors, `liftNatIso`, and the complex composition
  iso; full signatures read before writing the transport.
- `rg` of WeilConjectures and lean/Sheaf for Mayer-Vietoris/derived Hom and restriction
  instances: no matching existing statement or restriction instances.

Server compilation of the repaired module succeeded without warnings (4.0 seconds).
No new statement correction, dependency replacement, or new notion is needed for
this repair; the earlier exactness correction is retained.

## Prior second reading superseded

Return point (5) is accepted: the earlier second reading matched binder names and
missed the unconstrained category, functors, and maps. Its conclusions are withdrawn.
The independent second reader must read this repaired module and write the new
`Second reading by K1` section; this worker does not claim an independent review.

## Statement corrected

The original statement was:

“Let (X, O_X) be a ringed space [def-weil-locally-ringed-space-morphism] covered by
open subspaces U and V, and let D(O_X) be the derived category of sheaves of
O_X-modules [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category],
and likewise for the opens. For any two objects E and F of D(O_X), there is an exact
sequence from global Hom(E,F) to the direct sum of Hom between their restrictions
to U and V, then to Hom between their restrictions to the intersection; the second
map is the difference of restrictions, and this is the beginning of the
Mayer–Vietoris long exact sequence with a preceding negative Ext term.”

The retained correction makes explicit exactness at global Hom (preceded by
negative Ext) and at the direct sum, following Tag 08BW. It avoids the original
Lean's erroneous surjectivity assertion on the overlap term. Every citer:

- `lem-sc-derived-open-gluing`: holds; compatible local maps lift by exactness
  at the pair of local Hom groups.
- `lem-sc-perfect-into-support-on-T`: holds; a globally defined map restricting
  to zero comes from negative Ext by exactness at global Hom.

## Second reading by K1

I independently read the corrected sandbox node first against Stacks Tag 08BW,
then the module against that node. The local TeX source is
`/home/ubuntu/c1-stacks-review/cohomology.tex`, lines 8077–8198, including the
whole Unbounded Mayer–Vietoris section and the lower-shriek triangle proof.
I also checked https://stacks.math.columbia.edu/tag/08BW. This section has no
standing Noetherian, separation, boundedness, or local-ring hypothesis. The
correction specifies the two exactness positions in the displayed segment;
it agrees with the source and does not add surjectivity at its final term.

Object, hypothesis, and conclusion checklist (all pass):

1. A ringed space `(X,O_X)`: `X : RingedSpace.{u}`. I opened
   `Mathlib.Geometry.RingedSpace.Basic`, where this is `SheafedSpace CommRingCat`,
   and the dependency `def-weil-locally-ringed-space-morphism`, which explicitly
   defines a ringed space with a sheaf of commutative rings before discussing
   local stalks and morphisms. The recorded `LocallyRingedSpace.Hom` is not an
   extra hypothesis here; its underlying ringed-space definition is the part
   used. No local-ring assumption is present.
2. Opens U and V with union X: `U V : Opens X`, `hcover : U ⊔ V = ⊤`.
   These are arbitrary opens, with exactly the source's covering condition.
3. The module-sheaf category: `SheafOfModules.{u} (moduleRings X)`.
   I read `def-weil-sheaf-of-modules-category` and Mathlib's `SheafOfModules`,
   its `Hom` and `Abelian` instance: a presheaf of modules whose underlying
   abelian-group presheaf is a sheaf, with sectionwise linear morphisms.
   `moduleRings` is only a transparent abbreviation for composing `X.sheaf`
   with `forget₂ CommRingCat RingCat`, exactly as in the landed stalk module;
   it does not introduce another module-sheaf definition.
4. The derived categories on X, U, V, and U∩V: `DerivedCategory` of the four
   corresponding `SheafOfModules` categories. I opened
   `def-weil-abstract-derived-category` and Mathlib's `HasDerivedCategory`,
   `DerivedCategory`, and `Q`: localization of all ℤ-indexed cochain complexes
   at quasi-isomorphisms, with chosen Hom universe w. The four instance
   binders choose those localizations; they impose no geometric condition.
   The slice site `Over U` of opens of X is the open-subspace site, since its
   objects are precisely opens contained in U. Thus `R.over U` is O_U.
5. Any two objects: `E F : DerivedCategory (SheafOfModules.{u} (moduleRings X))`.
   There is no arbitrary substitute category or restriction functor binder.
6. Global-to-local map: the let-bound `R_U`, `R_V`, `R_UV` are the induced
   derived functors of Mathlib's `SheafOfModules.overFunctor`. The first map
   is exactly `fun f => (R_U.map f, R_V.map f)`. A binary product of additive
   Hom groups is their finite direct sum, including its zero elements.
7. Difference of restrictions on the overlap: the second map is
   `derivedOpenHomRestriction X (homOfLE inf_le_left) p.1 -
    derivedOpenHomRestriction X (homOfLE inf_le_right) p.2`.
   I opened `overMap` and `overFunctorMap`: the former restricts along
   `Over.map i`, the latter is the canonical comparison with direct
   restriction. In the repaired definition, its derived comparison is
   `(Functor.mapDerivedCategoryCompIso A B).symm ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap R i)`.
   The transport `e.inv.app E ≫ B.mapDerivedCategory.map f ≫ e.hom.app F`
   has the correct direction and fixes both restricted endpoints.
8. Preceding negative Ext: `(R_UV.obj E ⟶ (R_UV.obj F)⟦(-1 : ℤ)⟧)`.
   This is Ext^-1 in the overlap derived category, not a negative natural
   number or a bounded-category substitute. Its connecting map `negExt`
   is existential and additive (`→+`), as appropriate for this existence
   statement; the two restriction arrows are fixed, not existential.
9. Exactness at global Hom: `Function.Exact negExt` followed by the actual
   pair of restrictions. I read `Function.Exact` (the additive declaration
   generated from `MulExact`): vanishing under the second arrow is
   equivalent to membership in the image of the first arrow.
10. Exactness at the direct sum: the second `Function.Exact` uses precisely
    the same global-to-local map and the canonical difference map. There
    is no claim of surjectivity onto overlap Hom. Quantifiers introduce
    X, the cover, E and F, and then a connecting homomorphism, in that order.

Edge cases: empty X and both opens empty are allowed; either open may be
empty, the overlap may be empty, the opens may coincide or equal X, and E or
F may be zero. No assumption that a negative Ext group vanishes is made.
No characteristic, finiteness, or nonzero-ring assumption occurs. There
is no varying index set or n in this two-open statement. The universe check
compiled a scratch copy with `pp.universes` and `#check`: the declaration
has exactly universes `{u,w}`, with `RingedSpace.{u,u}` and module universe u.
This common ambient universe is the dependency's small-site convention and
can be enlarged for any given collection of spaces, rings and module sheaves;
Hom universe w is explicit and independent. There is no unbound variable or
silently generated universe in the final declaration.

Independent searches (different queries from the worker, logged by msearch):

- LeanFinder: “morphisms in unbounded derived category of module sheaves glue
  across an open cover with obstruction in shifted overlap Hom”: eight hits,
  principally ordinary sheaf Mayer–Vietoris gluing and `shortComplex` maps;
  none states this derived Hom segment.
- Loogle: `SheafOfModules.overFunctorMap`: one hit; signature opened and used.
- Mathlib grep: `yoneda_exact|overMap.*[Aa]dditive|overFunctor.*[Pp]reserves|mayer.*hom`:
  hits include the generic triangle representable exactness lemmas, not the
  ringed-space derived Hom sequence. Direct restriction-instance searches
  found no existing additivity/finite-limit/finite-colimit instances.
- LeanSearch: “Exact sequence of derived morphisms on a ringed space covered
  by two open subsets”: unavailable (Internal Server Error), recorded as
  unavailable, not as evidence of absence.
- Direct rg in WeilConjectures and project Lean: `mayer|vietoris` and the
  restriction/helper names. The adic pro-étale MayerVietoris module concerns
  K-injective units and detection of zero objects; I opened its declarations,
  and it is not this statement. No existing theorem duplicates the item.
- Searching `mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso` in
  both trees found reusable definitions in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
  (lines 101 and 169). I read their full binders, localization constructions,
  directions, and docstrings. They apply to arbitrary exact functors between
  abelian categories and cover precisely the private helper's construction.
  I also checked `dag/lean_names_upstream.json` for name collisions.

Mismatch and repair: H4, the private `derivedCompIso` recreated composition
and natural-isomorphism lifting already implemented upstream. I removed it,
imported that existing upstream module, and composed its two canonical isos.
Two local composite-preservation instances are built from Mathlib's existing
instances. I removed the helper's unused universe declarations and added the
module's main-declarations list. No theorem signature or mathematical clause
changed. The earlier Worker report's paragraph about `derivedCompIso` describes
the superseded implementation; this section records the delivered one.

The six named sorry'd restriction-property theorems are true sectionwise
additivity/exactness statements used by the restriction construction. Their
instance wrappers refer to those theorems, rather than inserting sorry into
data or assuming exactness in the main theorem. All seven theorem proofs
remain `sorry`; definitions and the abbreviation contain no sorry data.
Each declaration carries the source and this node's blueprint id. The main
docstring follows both proof steps (MV triangle, contravariant Hom exactness,
then all three adjunction identifications and the difference sign). There
are no new node files or dependency modules in this delivery to review.

I opened both citers named in `statement_change`:
`lem-sc-derived-open-gluing` uses exactness at the local pair to lift compatible
maps, so holds:true is correct; `lem-sc-perfect-into-support-on-T` uses
exactness at global Hom to obtain a negative-Ext preimage, so its use of the
corrected segment still holds. Its proof also invokes scalar linearity;
that supplementary property of the canonical MV construction is not an
additional clause of this item's node, and is not asserted by the additive
connecting-map signature. Neither citer requires surjectivity at overlap Hom.

Validation: the repaired module and the scratch universe check compiled on
the server cleanly; the node's `lean.statement` is extracted verbatim from
the delivered main signature. Dry-run and final delivery results follow below.
