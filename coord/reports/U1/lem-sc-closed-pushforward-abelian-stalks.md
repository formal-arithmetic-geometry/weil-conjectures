## Worker report

The module `Sheaf/AlgebraicGeometry/ClosedPushforwardAbelianStalks.lean` states
`TopCat.closedPushforwardAbelianStalks`. It models the closed subset as `C : Set X`,
with its subtype topology `TopCat.of C`, and uses the canonical inclusion
`TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩`. The hypothesis `hC : IsClosed C`
records closedness. For an abelian sheaf `F : (TopCat.of C).Sheaf AddCommGrpCat`,
the first conjunct states that every stalk of the direct image outside `C` is zero
(`IsZero`); the second states that the canonical stalk pushforward/germ map on each
point of `C` is an isomorphism; the third gives the naturality equation for each
morphism of abelian sheaves.

The direct image is Mathlib's `TopCat.Sheaf.pushforward`, whose underlying presheaf
is sectionwise the presheaf pushforward, hence renders `(i_*F)(U)=F(U ∩ C)` for the
subspace inclusion. The germ maps and stalks are Mathlib's
`TopCat.Presheaf.stalkPushforward`, `TopCat.Presheaf.stalk`, and
`TopCat.Presheaf.stalkFunctor`. The first clause renders `x ∉ C`; the second clause
renders the canonical germ map at `z`; the final clause renders compatibility with
`φ` by equality of the two composites on stalks.

Dependency declarations used: `def-sc-topological-abelian-cohomology` records the
abelian-sheaf context (its Lean attachment is Mathlib `CategoryTheory.Sheaf.H'`,
which is not needed for this stalk statement); `def-weil-pbc-module-stalk` records
stalks and germs (its project attachment is
`PresheafOfModules.moduleStalkFunctor`, while this abelian-group specialization uses
Mathlib's `TopCat.Presheaf.stalk` and `stalkFunctor`).

Edge cases checked: `C = Set.univ` makes the off-subset clause vacuous and the
inclusion the identity; `C = ∅` makes the on-subset clause vacuous and all points lie
outside; the empty sheaf and zero stalks are allowed. The subtype construction works
at every universe `u`.

Searches made:

* `msearch.py ... leanfinder "stalk of pushforward of an abelian sheaf along closed embedding"`:
  found Mathlib `TopCat.Presheaf.stalkPushforward` and germ lemmas, but no closed-image
  vanishing theorem.
* `msearch.py ... loogle "TopCat.Presheaf.stalkPushforward, IsClosedEmbedding"`:
  no results (the latter name is not a Loogle identifier).
* `rg` over Mathlib, `WeilConjectures`, and project `lean/Sheaf`: found only the
  general Mathlib stalk pushforward API and unrelated scheme/constant-sheaf stalk
  statements; no exact declaration for this node.

The module compiles cleanly with `lcompile.py`; the only proof placeholder is the
required theorem `sorry`.

## Second reading by U1

I read the item node, both statement-dependency nodes and their recorded
implementations, and Stacks `sheaves.tex`, lines 4928–4974, label
`lemma-stalks-closed-pushforward` (00AE), including the surrounding setup.
The source assumes only a topological space, a closed subspace and a sheaf;
its abelian clause replaces the singleton stalk outside the subset by zero.
The source's additional inverse-image identity is outside this node's scope.

Object/hypothesis/conclusion checklist (all pass):

1. Arbitrary topological space X: `{X : TopCat.{u}}`, with no separation,
   compactness, scheme or finiteness assumption.
2. Closed subset Z with its subspace topology: `(C : Set X) (hC : IsClosed C)`
   and `TopCat.of C`, whose topology is the induced subtype topology.
3. Inclusion i: every occurrence uses
   `TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩`, the actual inclusion.
4. Abelian sheaf F on Z: `(F : (TopCat.of C).Sheaf AddCommGrpCat.{u})`.
   This is exactly a sheaf of abelian groups, with no module, coefficient-field
   or constant-sheaf restriction.
5. Direct image with sections F(U ∩ Z): `TopCat.Sheaf.pushforward` applied to
   the inclusion. I opened `Functors.lean:62–80`: its underlying presheaf is
   `Presheaf.pushforward`; inverse image of U under the inclusion is U ∩ C,
   and restrictions and pushed-forward morphisms are the original ones.
6. Stalks and germs: `TopCat.Presheaf.stalk` is the neighbourhood colimit;
   `stalkFunctor.map` is its induced additive map, and `stalkPushforward`
   is the canonical map from the ambient pushforward stalk to the original
   stalk. I opened their definitions in `Stalks.lean:76–94,172–183`;
   `stalkPushforward_germ` specifies the required germ representative map.
7. Outside-subset vanishing: first conjunct, `∀ x : X, x ∉ C → IsZero (...)`.
   The object is in AddCommGrpCat; IsZero means the zero abelian group, rather
   than the invalid IsZero assertion on a bare type.
8. On-subset canonical isomorphism: second conjunct, `∀ z : TopCat.of C,
   IsIso (TopCat.Presheaf.stalkPushforward ... F.1 z)`. Its source is
   `(i_*F)_(Subtype.val z)` and its target is `F_z`; the direction is correct.
9. Compatibility with every sheaf morphism: third conjunct quantifies G, φ,
   then z, and says `(i_*φ)_z ≫ c_G = c_F ≫ φ_z`. These are additive-group
   maps of the same source and target, using the very same canonical c_F and
   c_G as in the preceding conjunct. No arbitrary isomorphism is substituted.

Dependency check: `def-sc-topological-abelian-cohomology` records
`CategoryTheory.Sheaf.H'`, whose signature I opened in
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic:87`. This theorem uses
only its abelian-sheaf context, not cohomology, so no cohomology import or
replacement definition is needed. `def-weil-pbc-module-stalk` records
`PresheafOfModules.moduleStalkFunctor`; I read its whole module
`Sheaf.Topology.PresheafModuleStalkFunctor`. Its `stalkObj` is literally
`TopCat.Presheaf.stalk M.presheaf x`, and `stalkAddMap` is literally
`stalkFunctor AddCommGrpCat x` on the underlying presheaf morphism.
Thus the theorem uses exactly the existing underlying abelian-group stalks
and maps described by this dependency; adding a constant-integer-module
wrapper would introduce no needed notion. No private copy, missing definition,
new node or dependency repair was found.

Edge cases: C = ∅ leaves no z to quantify over and gives zero stalks at all
ambient points; C = univ makes outside vanishing vacuous and gives the
canonical comparison everywhere. If X is empty, both pointwise clauses and
naturality at points are vacuous. The zero sheaf is admitted. The bound
universe u is arbitrary, including u = 0; any space and coefficient groups
can be placed in a common universe. There is no nonempty hypothesis, index
set, degree n, coefficient characteristic or scheme condition to exclude.
All variables and universes are explicit (`autoImplicit false`).

Independent searches, using different phrasing from the worker:

- LeanFinder: `direct image sheaf stalk vanishes away from closed support`;
  eight hits about vanishing germs on ringed spaces and schemes, no exact
  closed-subset abelian-sheaf statement.
- Loogle: `"stalk", "IsZero"`; found
  `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero`. I checked its signature
  in `Mathlib.Topology.Sheaves.Abelian:90`: it detects a zero sheaf from all
  its stalks, and does not describe closed-subset pushforward stalks.
- LeanSearch: `For a sheaf of abelian groups on a closed subspace, its direct
  image has zero stalk outside the subspace.` Service returned HTTP 500;
  unavailable, no mathematical verdict drawn.
- rg of Mathlib, upstream WeilConjectures and this project's Sheaf modules:
  searched closed/stalk/pushforward, zero-stalk combinations, and then
  `stalkPushforward|closedPushforwardAbelianStalks|closed_pushforward.*stalk`.
  Read Mathlib `stalkPushforward_iso_of_isInducing` (only the on-image clause).
  Opened project `closed_pushforward_constant_stalks` (constant set-valued
  sheaves only) and `closedImmersion_pushforward_stalks` (O-modules on
  schemes only). Neither has this node's arbitrary topological-space,
  arbitrary abelian-sheaf statement. No full existing match was found.

Mismatches repaired: the module lacked the required copyright/module header,
its theorem docstring compressed the node's five proof steps without the
empty-cover argument, germ equality criterion or explicit dependency references,
and it was in AlgebraicGeometry despite introducing no scheme. Added the
headers, expanded the docstring step by step, and moved the module to
`Sheaf/Topology/ClosedPushforwardAbelianStalks.lean`, updating only `lean.module`
and `lean.file` in the node. The theorem signature, including its quantifier
order and all three clauses, is unchanged; `lean.statement` was checked
verbatim against it. No node statement correction, extra assumptions, hollow
definitions, proofs or extra theorems were introduced. The sole named theorem
still has the required stage-2 `sorry` proof.

Validation: `lcompile.py` completed with exit code 0 and no warnings. The
`deliver2.py --no-push` dry run printed OK after the final server compilation
and stage-2 preflight. The delivery contains one theorem module and the item
record, with no new definitions or dependency modules.
