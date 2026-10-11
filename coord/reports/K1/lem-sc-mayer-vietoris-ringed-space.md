## Worker report

The module `Sheaf.Topology.ModuleMayerVietoris` states
`AlgebraicGeometry.RingedSpace.module_mayerVietoris`, with its proof `sorry`.
The source is Stacks Project, Cohomology, Lemma 20.8.2 (01EB), read at
https://stacks.math.columbia.edu/tag/01EB because this machine has no local Stacks text.
Its short exact sequence of section complexes gives exactly the maps used here.
No statement correction or disputed statement is needed.

Hypotheses and clauses:

- A ringed space is `X : RingedSpace.{v}`, with no local-ring or scheme assumption.
  Mathlib's `RingedSpace` is `SheafedSpace CommRingCat`; the dependency's
  `LocallyRingedSpace.Hom` was read with its docstring, but the node asks only for
  the ringed-space portion of that dependency, not locality of stalks or a morphism.
- Opens are `U V : Opens X`. The theorem gives the sequence on `U ⊔ V` for all
  pairs simultaneously. In the node's case `U ⊔ V = ⊤`, this is the sequence on X.
  This formulation includes the restricted covers in the node: their union is
  `(U ⊓ W) ⊔ (V ⊓ W) = (U ⊔ V) ⊓ W`, hence W for an original cover of X.
  It is an equivalent simultaneous formulation of the statement for arbitrary
  ringed spaces and their open restrictions, without an additional hypothesis.
- Every module is `F : SheafOfModules (moduleRings X)`. There is no coherence,
  finiteness, or injectivity assumption on F.
- `H p U` abbreviates `openModuleCohomology X p U`, the p-th derived functor of
  additive-group-valued evaluation F ↦ F(U), in the O_X-module category.
  It computes H^p(U,F|_U) by restricting an injective resolution on X (01E1).
  At `⊤` it is the underlying additive-group-valued version of the recorded
  `moduleCohomology X p`: both compute Γ(X,I•), and forgetting the scalar action
  is exact. No Ext-based abelian-sheaf cohomology is substituted.
- The initial `0 → H⁰` clause is `Function.Injective` of the pair of restrictions
  in degree zero.
- The restriction map at every degree is the lambda sending x to the pair
  `(r ... x, r ... x)`. The two summands are represented by the product of two
  additive groups, canonically their finite direct sum.
- The next map is the lambda sending `(x,y)` to `r ... x - r ... y`, in that order.
  Both are group homomorphisms because r consists of morphisms in AddCommGrpCat.
- Connecting maps are the existential family `δ U V p`, with source H^p(U∩V)
  and target H^(p+1)(U∪V). The three `Function.Exact` clauses give exactness at
  H^p(U)⊕H^p(V), H^p(U∩V), and H^(p+1)(U∪V), respectively, for every p : ℕ.
  Together with injectivity this includes every displayed term, including H⁰.
- Naturality in F is built into δ's type: it is a natural transformation between
  the corresponding functors on modules. The restrictions r are also natural
  transformations, so the other squares commute as well.
- For each W : Opens X, the final natural-transformation equality is
  δ(U,V) followed by restriction to the union of the restricted cover equals
  restriction from U∩V to (U∩W)∩(V∩W), followed by δ for the restricted cover.
  Thus it includes connecting-map compatibility. The other squares follow from
  functoriality of the derived restriction maps, inherited from
  `NatTrans.rightDerived_id` and `NatTrans.rightDerived_comp`.

Dependency declarations used/read:

- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `AlgebraicGeometry.LocallyRingedSpace.Hom`, with its underlying
  `PresheafedSpace.Hom` and locality field; `Mathlib.Geometry.RingedSpace.Basic`:
  `AlgebraicGeometry.RingedSpace` (the required ringed-space notion).
- `Sheaf.Topology.RingedSpaceModuleCohomology`:
  `AlgebraicGeometry.RingedSpace.moduleCohomology` and `globalSectionsFunctor`,
  signatures, docstrings and resolution interpretation read in full.
- New dependency `Sheaf.Topology.OpenModuleCohomology`:
  `openModuleSections`, its additive instance, `openModuleCohomology`, and
  `openModuleCohomologyRestriction`, all in `AlgebraicGeometry.RingedSpace`.
- The new module uses the already supplied `moduleRings`,
  `moduleSheaves_abelian_enoughInjectives`, Mathlib `SheafOfModules.forget`,
  `PresheafOfModules.toPresheaf`, evaluation, `Functor.rightDerived`, and
  `NatTrans.rightDerived`. It defines no private replacement for these notions.

Edge cases checked before writing: X empty, either open empty, both opens empty,
U=V=X, F=0, W empty or W=X, and p=0. There are no nonemptiness assumptions.
For U=V=X the maps are diagonal and difference, so connecting maps vanish;
for one open empty the sequence reduces to the identity on the other open.
The existential δ is simultaneous in all opens and modules, not separately
chosen in a way that could lose either naturality requirement. Universe v is
explicit throughout the theorem; universe u is explicit throughout the definition
module. No auto-bound variables or universes are used.

Searches for existing statements and notions:

- msearch leanfinder: "Mayer Vietoris long exact sequence of cohomology of modules
  on a ringed space natural restriction to open subsets" returned eight generic
  site-square declarations (shortComplex and its maps/sheaf-condition results),
  not this theorem.
- msearch loogle: `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact`
  returned the site theorem in Mathlib's SheafCohomology/MayerVietoris.lean.
  Its cohomology is Ext-based abelian-sheaf cohomology; it is not the node's
  derived O_X-module cohomology.
- msearch grep `MayerVietoris|mayer.vietoris` in
  CategoryTheory/Sites/SheafCohomology found only the generic site module.
  rg of source WeilConjectures and lean/Sheaf found the adic pro-etale variant
  and derived Hom variants, respectively. Neither is this statement.
  rg of the item ID in source WeilConjectures found no declaration.
- msearch leansearch "right derived evaluation module sheaf cohomology presheaf
  open subsets" was unavailable (Internal Server Error).
- Additional searches for the new notion are recorded in its mathlib_searches
  and described below. The proposed full names were also checked in the three
  Lean trees and dag/lean_names_upstream.json: no collisions.

Validation: both modules compiled together on the server without errors or warnings.
The earlier elaboration heartbeat failure was repaired by explicitly typing all
open-inclusion proofs, without increasing any limit; combined compilation took 2.1 s.

## New nodes

`def-sc-open-module-cohomology` supplies the missing open-set cohomology API:
sections as an additive functor, its right derived functors, and derived restriction
natural transformations. Source: Stacks 01DZ, 01E1, and the section complexes of 01EB.
The existing module-cohomology node supplies only global sections on a ringed space,
not open-set evaluation or cohomology restriction maps. This extension reuses its
injective module category and the same right-derived-functor construction.
Mathlib's `Sheaf.cohomologyPresheaf` is for Ext-based abelian sheaves, not derived
O_X-module evaluation, so is not duplicated here. Leanfinder returned that API,
underived module evaluation, and sheafification; Loogle's query with
`NatTrans.rightDerived` returned an unknown-identifier response (the actual local
Mathlib declaration was found and read directly). Grep of Mathlib, source and
lean/Sheaf found no module-cohomology open-restriction API. DAG grep and
blueprint_refs search found no node for this API. All definition data is explicit;
the additive instance is inherited, and no auxiliary theorem or sorry occurs in
this module. Its node and module are included in the sandbox and its ID is added
to the item's stmt_deps.


## Second reading by K1

I independently read the item and new definition node, both delivered modules,
the two original statement-dependency nodes, their declarations, and the Mathlib
APIs below. I read the Stacks cohomology.tex source fetched from
https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex
into this sandbox's scratchpad, including the chapter introduction,
section-cohomology-sheaves (01DZ), lemma-cohomology-of-open and the following
restriction-map construction (01E1), and lemma-mayer-vietoris (01EB).
The online tags agree with this text. There is no ambient Noetherian, scheme,
local-ring, finiteness, or field assumption in these source passages.

Object/hypothesis/conclusion inventory and matching, in node order:

1. A ringed space X: `X : RingedSpace.{v}`. PASS. The dependency node defines
   ringed spaces as well as locally ringed morphisms; the former is exactly
   Mathlib `SheafedSpace CommRingCat` in RingedSpace/Basic.lean. I opened
   `LocallyRingedSpace.Hom` in the dependency's recorded Mathlib file: its
   extra local-stalk condition is not assumed by this theorem.
2. Opens U,V covering X: `U V : Opens X`, with ambient open `U ⊔ V` throughout.
   PASS as an equivalent simultaneous open-subspace formulation. For the node's
   cover, `U ⊔ V = ⊤`, so these are exactly the terms on X. For an arbitrary
   pair apply the node to the ringed open subspace U union V and restricted F;
   01E1 identifies the groups and canonical maps with those used here. Thus
   the absence of a separate cover binder does not assert a sequence on X
   for a non-cover. Simultaneous choices allow the node's restriction clause.
3. Any O_X-module F: `F : SheafOfModules.{v} (moduleRings X)`. PASS. I opened
   `moduleRings` through the enough-injectives dependency. There is no property
   assumed of F, nor an extra instance requested of X.
4. Cohomology H^p of each indicated restriction, p nonnegative:
   `H := openModuleCohomology X`, with `p : ℕ`. PASS. The delivered definition
   derives evaluation of module sheaves at the open, using the original
   `moduleSheaves_abelian_enoughInjectives X`. I read `globalSectionsFunctor`,
   `moduleCohomology`, and the resolution-comparison declarations of
   RingedSpaceModuleCohomology. At top the additive section complex is the
   underlying additive complex of that module-valued global-sections complex;
   forgetting scalars preserves its homology. At other opens 01E1 gives the
   same interpretation using the restricted injective resolution. No abelian-
   sheaf Ext cohomology has replaced the recorded module cohomology.
5. Initial zero and H^0(X,F): the first conjunct's `Function.Injective` of
   the pair of degree-zero restrictions. PASS: this is precisely exactness
   at the initial H^0 term after zero.
6. H^p(X,F) to H^p(U,F) direct sum H^p(V,F): the lambda with the two
   `r p ... .app F` components. PASS. The finite product of additive groups
   represents the two-term direct sum, and these are additive maps.
7. The next arrow: `r p ... x.1 - r p ... x.2` on the intersection. PASS,
   including the source's sign order (1,-1).
8. Connecting arrows and exactness at every subsequent term: the family
   `δ U V p : H p (U ⊓ V) ⟶ H (p+1) (U ⊔ V)` and the three
   `Function.Exact` clauses. PASS. They give exactness respectively at the
   direct sum, intersection, and next union group. Taking p=0 includes H^0
   at the intersection and H^1 on X; taking p=q-1 covers the incoming arrow
   to H^q for every q>0. There is no missing interior term or artificial
   terminal surjectivity condition.
9. Functoriality in F: δ is a natural transformation between functors on
   the module category; r is `NatTrans.rightDerived` of section restriction.
   PASS. All arrows, including δ, therefore commute with module morphisms.
10. Restriction to each open W': `∀ U V W : Opens X` and the final equation
    `δ U V p ≫ r (p+1) ... = r p ... ≫ δ (U ⊓ W) (V ⊓ W) p`.
    PASS. Both inclusions have the correct contravariant direction; the
    restricted union is `(U ⊔ V) ⊓ W`, equal to W for a cover of X.
    The equation is the connecting square. Other squares commute from
    composition of section restrictions and `NatTrans.rightDerived_comp`.
    Using the same ambient-X resolution is precisely 01E1's construction
    of the canonical restricted-cover cohomology, not a different F.

Edge cases: p=0 is present; p+1 supplies all positive degrees. No nonempty
space or open is required. X empty, U empty, V empty, both empty, W empty,
W=top, U=V=top and F=0 are included. For U=V=top the maps are diagonal
and difference; for an empty member restriction on the other is the identity.
There is no characteristic restriction, index type, field, or scheme instance.
The universes u and v are declared explicitly in the respective modules;
all term variables are bound. These universe choices follow the recorded
module-cohomology API and can accommodate the data by universe enlargement.

Independent H4/H12 searches (queries differ from the first worker's):

- msearch leanfinder: "derived sections of module sheaves exact sequence two
  open subsets connecting homomorphism" returned the generic site-square
  shortComplex APIs and `ShortComplex.ShortExact.δ_apply'`, not this theorem.
- msearch loogle: `SheafOfModules.evaluation` returned evaluation and its
  limit-preservation APIs, not derived open sections or their restriction.
  I opened the definition: it is underived module-valued evaluation.
- msearch leansearch: "right derived sections on open subsets of a ringed
  space module cohomology restriction" was unavailable (Internal Server Error);
  this is recorded as unavailable, not as a negative search result.
- rg over source WeilConjectures, repository lean/Sheaf and Mathlib's
  Topology/Sheaves and Sites/SheafCohomology found the topological square,
  site Ext-based cohomology sequence, adic pro-etale sequence and derived-Hom
  sequence. I opened `Sheaf.H`, `cohomologyPresheafFunctor`, and the site
  MayerVietoris `δ`, `sequence`, and `sequence_exact`: their objects are
  abelian sheaves and their groups are Ext groups, not this module-derived API.
- DAG rg for "cohomology presheaf|cohomology on open|derived evaluation"
  returned higher-direct-image and comparison nodes, no definition of the
  delivered module-open-cohomology API. There is no existing declaration
  saying exactly this node's statement or defining this API.

New node `def-sc-open-module-cohomology`: PASS. Its statement explicitly
introduces X,U,F,p and V subset U, cites exactly its two stmt_deps, and defines
sections, derived sections and canonical derived restriction. 01E1's text
explicitly computes open cohomology on an ambient-X module resolution and
then constructs restriction using the same resolution; this is exactly the
new definition, with the underlying additive groups of 01DZ's module-valued
cohomology. It is an API extension, not a second cohomology theory. Its own
module contains explicit composites, an inherited additive instance and
right-derived constructions only. I checked the new-node field inventory:
definition, split, same chapter/unit, source, searches of all three kinds,
null mathlib_match/proof_origin, empty proof/proof_deps, worker-created
item/group/date, blueprint ancestor/via, none audit and complete lean record.
The item cites it. There are no dependency-replacement modules to review.

H5/H6/H8/H9: no hollow definition or definition-local sorry; only the named
main theorem has `by sorry`. Module and declaration docstrings name the source
and correct blueprint IDs. The theorem docstring follows all three node proof
steps with their dependency IDs. Imports, namespaces and line lengths conform.
There is no statement correction record and none is needed. I found no
mathematical mismatch and changed no Lean signature or node statement; this
second reading adds the independent review and searches only.

Second-reader validation: both modules compiled together in dependency order in
2.1 seconds, exit code 0, with no errors or warnings. The deliver2 dry run
printed OK: preflight passed and compilation was clean.
