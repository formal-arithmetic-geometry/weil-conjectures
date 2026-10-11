## Worker report

The module `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMaps` states
`AlgebraicGeometry.module_extensionByZero_stalk_maps`. Every proof is `sorry`;
the three private abbreviations have complete data and only abbreviate existing
functors. No new mathematical notion, definition node, dependency module, or
statement correction is needed. No statement is disputed.

The source was read at https://stacks.math.columbia.edu/tag/00A7 (Sheaves,
`lemma-j-shriek-modules`, clauses (2)--(4)) and
https://stacks.math.columbia.edu/tag/00A5 (`lemma-j-shriek-abelian`). The local
`literature/stacks-project/` checkout is absent on this machine, so the official
Stacks pages supplied the source. The item includes the nested-open maps and their
compatibilities as consequences of these adjunctions, as its proof explains.

Hypotheses and every clause are represented as follows:

* An arbitrary ringed space is `(X : RingedSpace.{u})`, not a scheme or a locally
  ringed space. There is no locality or separation assumption. Its structure sheaf
  is the existing `AlgebraicGeometry.moduleRings X`.
* A sheaf of modules on X is the binder
  `∀ F : SheafOfModules.{u} (moduleRings X)` in the third conjunct. The clauses
  about an arbitrary G do not require an extension of G to X.
* The open is `(W : Opens X)`. The category on the open is
  `SheafOfModules.{u} ((moduleRings X).over W)`, equivalent to modules on the open
  subspace through Mathlib's `W.sheafOfModulesEquivOver (moduleRings X)`.
* The existing restriction is `SheafOfModules.overFunctor (moduleRings X) W`.
  `moduleOpenRestriction` merely abbreviates it. The existing extension by zero is
  `SheafOfModules.extensionByZeroPresheaf (moduleRings X) W ⋙
  PresheafOfModules.sheafification (𝟙 (moduleRings X).obj)`;
  `moduleZeroExtension` merely abbreviates this same construction.
* The family `adj : ∀ W, moduleZeroExtension X W ⊣ moduleOpenRestriction X W`
  supplies the adjunctions already asserted by the dependency. It is existential
  conclusion data, not an extra hypothesis or an unrelated pair of functors.
* Clause (1), outside W: for **every** module G on W and **every** x in X,
  `x ∉ W → IsZero ((RingedSpace.moduleStalkFunctor X x).obj
  ((moduleZeroExtension X W).obj G))`. Thus the stalk is the zero stalk module.
* Clause (1), inside W: for every subtype point `x : W` and every G,
  `IsIso ((moduleOpenStalk X W x).map ((adj W).unit.app G))`.
  `moduleOpenStalk` is the recorded `RingedSpace.moduleStalkFunctor` on
  `X.restrict (Opens.isOpenEmbedding W)`, after the existing equivalence of opens
  sites. This is the map G_x → (j_!G)|_W,x induced by the unit. Restricting to an
  open preserves the stalk at a point in that open (cofinal neighbourhoods),
  canonically identifying the latter with (j_!G)_x. The restricted structure-ring
  stalk is similarly canonically O_X,x; `IsIso` is in ModuleCat over that ring,
  so this is a module isomorphism, not just a bijection of carriers.
* Clause (1), naturality in G: this map is explicitly the image of the
  adjunction's **natural** unit under the functor `moduleOpenStalk X W x`.
  Its naturality square is therefore part of these existing structures; the
  isomorphism and its inverse commute with every module morphism G → G'.
* Clause (2), canonical map: `iota` is one family indexed by W,W' and
  `h : W ≤ W'`, with the precise source j_W!(F|W) and target j_W'!(F|W').
  Its defining `homEquiv` equation asserts that its transpose is the restricted
  unit on W'. The inverse and forward components of
  `SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)` make the canonical
  identifications of restrictions to nested opens on each end. The middle factor
  `SheafOfModules.overMap ... .map ((adj W').unit.app ...)` is exactly that unit
  restricted to W. A homEquiv is bijective, so this equation specifies the map
  uniquely and cannot be satisfied by arbitrary unrelated morphisms.
* Clause (2), top open: the localized opens site is equivalent to the opens of X,
  so j_top! R_top is represented up to canonical identification, rather than
  literally as the identity functor. `IsIso ((adj ⊤).counit.app F)` supplies this
  identification with F. The equation
  `iota W ⊤ le_top ≫ (adj ⊤).counit.app F = (adj W).counit.app F`
  says iota_W,X is exactly the counit under it. The triangle identity makes the
  top-open unit the identity under the same identification. This is the node's
  j_X!=id convention expressed in the dependency's localized-site representation,
  not a change of its mathematical statement.
* Clause (2), identity: `∀ W, iota W W le_rfl = 𝟙 _`.
* Clause (2), composition: for W≤W'≤W'',
  `iota W W' h ≫ iota W' W'' h' = iota W W'' (h.trans h')`.
  Lean's `≫` writes the smaller-to-larger map first.
* Clause (3): `e` is one family of ambient O_X,x-module isomorphisms from F_x to
  (j_W!(F|W))_x whenever `hx : x ∈ W`. The equation
  `(e W x hx).inv = (RingedSpace.moduleStalkFunctor X x).map
  ((adj W).counit.app F)` identifies this with clause (1)'s canonical isomorphism:
  the unit on F|W is inverse to the restricted counit by the triangle identity.
  The final equation
  `(e W x hx).hom ≫ stalk.map (iota W W' h) = (e W' x (h hx)).hom`
  states that this **same** iota family acts as the identity under the two
  identifications with F_x. All objects and maps here are in ModuleCat(O_X,x).

Dependency declarations read and used:

* `def-weil-locally-ringed-space-morphism`: Mathlib's
  `AlgebraicGeometry.LocallyRingedSpace.Hom`, inherited
  `AlgebraicGeometry.PresheafedSpace.Hom`, and `RingedSpace` (SheafedSpace of
  CommRingCat) for this node's ringed-space clause. The node has mathlib status;
  no Lean record is required. No local-ring condition is used by this item.
* `def-weil-sheaf-of-modules-category`: `SheafOfModules`, its `val` and `isSheaf`
  fields and module-sheaf Hom, in `Mathlib.Algebra.Category.ModuleCat.Sheaf`.
  This is also a Mathlib leaf.
* `lem-sc-derived-open-restriction-adjunction-exact`:
  `AlgebraicGeometry.open_restriction_adjunction_exact`, in
  `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`. Its full statement
  fixes both functors to the exact overFunctor and sheafified extension-by-zero
  construction used here. Its recorded module is imported; the theorem's
  adjunction family is conclusion data compatible with that existence statement.
* `def-weil-pbc-module-stalk`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`, in
  `Sheaf.Algebra.Homology.ModuleStalkFunctor`. Its full signature and docstring,
  as well as its linear stalk-map construction, were read. The Mathlib stalk
  and germ module instances in `Mathlib.Algebra.Category.ModuleCat.Stalk` and
  `TopCat.Presheaf.stalk` in `Mathlib.Topology.Sheaves.Stalks` were also read.

Edge cases: W=⊥ has no subtype points, and all ambient stalks of every extended
module are zero. W=⊤ has no outside points and the counit identification realizes
the identity-extension convention. The zero input module is included without a
nonzero assumption. An empty X makes all pointwise assertions vacuous and leaves
the usual identities in its module category. W=W' gives the actual identity
morphism; equal stages in a three-open chain satisfy the composition equation.
No nonempty-space, nonempty-open, finite-cover, or characteristic hypothesis is
present. All variables and the universe are explicitly bound.

Searches actually run (logged in `searches.jsonl`):

* `msearch.py leanfinder`, query "stalks of extension by zero of sheaves of modules
  on ringed spaces and canonical maps for nested open subsets": 8 hits, the
  ModuleCat.Tilde stalk/germ results and TopCat.stalkToFiber; no generic match.
* `msearch.py loogle`, query
  "SheafOfModules.overFunctorMap, TopCat.Presheaf.stalk": 0 hits.
* `msearch.py grep`, query "extensionByZero|jShriek|overFunctorMap", directory
  `Algebra/Category/ModuleCat`: overFunctorMap in PushforwardContinuous.lean;
  no matching theorem.
* `msearch.py leansearch`, query "stalk of extension by zero of sheaves of modules
  on a ringed space, and maps for nested opens": service unavailable (HTTP
  Internal Server Error), **not** a negative match.
* `rg` of `WeilConjectures/` and `lean/Sheaf/` for extensionByZero and this node id:
  the existing scheme-only `Scheme.Modules.module_extensionByZero_adjunction`
  and unrelated WeilSheaf/pro-etale extension functors were read; none states
  the arbitrary-ringed-space theorem with nested-open maps. The exact new names
  and node id were also checked in the source and `dag/lean_names_upstream.json`;
  no collision or upstream attachment exists.
* Mathlib source searches found the usable `sheafOfModulesEquivOver`,
  `overFunctorMap`, and `overMap`; their full signatures and docstrings were read.

Validation: the final 109-line module compiles cleanly on the server with
`scompile.py E1 lem-sc-module-extension-by-zero-stalk-maps <module>`. The recorded
Lean signature is the complete signature copied verbatim from the file. The
second-reading section is deliberately left for the independent second worker.

## Second reading by E1

I independently read the item's node, all four statement-dependency nodes and
both recorded project modules, and the delivered Lean file. No mathematical or
Lean mismatch was found; the module and node record are unchanged. This section
is the only change of the second reading.

Source check: the local Stacks checkout is absent. I read the official pages
https://stacks.math.columbia.edu/tag/00A7 and
https://stacks.math.columbia.edu/tag/00A5 and the actual `sheaves.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/sheaves.tex,
including `definition-restriction`, `definition-j-shriek-abelian` (the module
clauses preceding the lemmas), and `lemma-j-shriek-modules`. The context assumes
an arbitrary ringed space and an open inclusion, with no finiteness, locality,
separation, or characteristic condition. The nested-open conclusions are the
adjunction consequences spelled out in the node's proof, rather than an extra
verbatim clause of Tag 00A7.

Object/hypothesis/conclusion checklist (node order):

1. Ringed space `(X,O_X)`: `(X : RingedSpace.{u})`. The dependency's definition
   explicitly means commutative rings; Mathlib's `RingedSpace` is precisely
   `SheafedSpace CommRingCat`. Verdict: same object, no locally-ringed assumption.
2. Arbitrary global O_X-module F: `∀ F : SheafOfModules.{u} (moduleRings X)`.
   `moduleRings` forgets the commutativity of the structure sheaf; the
   `SheafOfModules` fields `val` and `isSheaf` and its morphisms are the recorded
   dependency notion. Verdict: all module sheaves, not coherent modules.
3. Arbitrary open W and its inclusion: `W : Opens X`; subtype `x : W` expresses
   a point inside W, and `homOfLE h` is the inclusion for `h : W ≤ W'`.
   Verdict: no extra open or space condition.
4. Modules on O_X restricted to W: `SheafOfModules ((moduleRings X).over W)`.
   I opened `Opens.sheafOfModulesEquivOver`: its functor takes modules on the
   localized opens site to modules on the actual open subspace. Verdict: the
   same module category through an existing equivalence, not a private copy.
5. Restriction and its left adjoint: `moduleOpenRestriction` abbreviates exactly
   `SheafOfModules.overFunctor`; `moduleZeroExtension` abbreviates exactly the
   sheafified extension presheaf fixed in `open_restriction_adjunction_exact`.
   `∃ adj : ∀ W, ... ⊣ ...` supplies their adjunctions as conclusion data.
   Verdict: the recorded functors, with no additional hypothesis.
6. Clause (1), outside: for every W, every G on W and every ambient x,
   `x ∉ W → IsZero (stalk.obj (moduleZeroExtension.obj G))`.
   The recorded `moduleStalkFunctor` lands in `ModuleCat (X.presheaf.stalk x)`;
   thus this is zero as a stalk module. Verdict: exact zero-stalk assertion.
7. Clause (1), inside and naturality: for every W, `x : W`, and G,
   `IsIso ((moduleOpenStalk X W x).map ((adj W).unit.app G))`.
   I checked the abbreviation's equivalence and recorded stalk-functor signature.
   This is the canonical unit-induced map on the restricted stalk. Cofinal open
   neighbourhoods identify the restricted stalk and its ring with the ambient
   stalk and O_X,x; transporting a module isomorphism along that ring isomorphism
   is equivalent to the node's O_X,x-module isomorphism. Naturality in G follows
   from the existing natural transformation `unit` and functor `moduleOpenStalk`.
   Verdict: the intended canonical, natural module isomorphism, not an unrelated
   existential isomorphism or a mere bijection of underlying sets.
8. Clause (2), canonical map and its quantifiers: after fixing F, `∃ iota` is
   one family for all W,W' and h, with source `j_W!(F|W)` and target
   `j_W'!(F|W')`. Its `homEquiv` equation specifies its transpose. I opened
   `overFunctorMap` and `overMap`: the inverse comparison at F first goes from
   F|W to the twice-restricted F; the middle map restricts the W'-unit; the final
   forward comparison reaches the restriction to W of the target. Verdict:
   exactly the required map, uniquely determined by the bijective homEquiv.
9. Clause (2), W'=X convention: `IsIso ((adj ⊤).counit.app F)` identifies
   top-open extension with F, and
   `iota W ⊤ le_top ≫ (adj ⊤).counit.app F = (adj W).counit.app F` states that
   the top transition is the counit under that identification. The triangle
   identity identifies the top unit with the identity. Verdict: the node's
   identity-functor convention in the dependency's equivalent-site encoding.
10. Clause (2), identity and composition: `iota W W le_rfl = 𝟙 _` and
    `iota W W' h ≫ iota W' W'' h' = iota W W'' (h.trans h')`.
    Verdict: actual identity and the correct order of all three nested opens.
11. Clause (3), identity on stalks: one family `e W x hx` identifies F_x with
    each extended restriction's ambient stalk. Its inverse is explicitly the
    counit's stalk map, tying it to clause (1) by the triangle identity, rather
    than permitting independently chosen identifications. The last equation
    `e.hom ≫ stalk.map (iota W W' h) = e'.hom` says exactly that this same iota
    is the identity under those identifications. Verdict: all objects and maps
    are modules and linear maps over the single ambient ring O_X,x.

Edge cases checked: W bottom has no inside points and zero stalks everywhere;
W top has no outside points and is identified with identity extension by the
counit. G=0 and F=0 are admitted. Empty X has vacuous pointwise clauses and retains
all categorical identities. Equal successive opens are included in composition.
There is no index set, integer n, or characteristic parameter to restrict.
The universe u is explicitly bound: spaces, rings and modules can all be placed
in a common arbitrarily large universe, as in both dependency signatures; no
small test-object quantifier or unintended extra instance makes a clause vacuous.

Independent searches, with different words from the worker's:

- `msearch.py leanfinder`: "lower shriek along inclusion of an open subset has
  zero stalk off the subset and identity transition on germs". Eight hits,
  involving germ restrictions, skyscraper adjunctions and restricted ringed-space
  stalks, not this theorem.
- `msearch.py loogle`: "SheafOfModules, IsIso" returned an unknown-identifier
  diagnostic for IsIso; this is an inconclusive search, not a negative match.
- `msearch.py leansearch`: "module sheaf lower shriek stalk vanishes outside an
  open subset" was unavailable (Internal Server Error), not a negative match.
- `msearch.py grep`: "lowerShriek|extension_by_zero|jShriek" found no matches.
  Direct `rg` also searched Mathlib's Topology/Sheaves and ModuleCat sources for
  lowerShriek, lower_shriek, extensionByZero, extension_by_zero and j_!; no generic
  theorem was found. Direct searches of WeilConjectures and lean/Sheaf found
  scheme-only `Scheme.Modules.module_extensionByZero_adjunction` (opened and
  read), and the unrelated pro-etale/Weil lower-shriek constructions. The scheme
  theorem does not cover arbitrary ringed spaces or the nested-open maps.
  The new declaration and node id have no upstream-name attachment or collision.

No new definition nodes or dependency modules are present or needed. All three
private abbreviations have complete data and merely compose existing notions.
The sole theorem has `sorry` as required by stage 2; nothing was proved. Module
and declaration docstrings cite the source and blueprint id, and the theorem's
proof docstring follows all three steps of the node. No variable is unbound;
all lines meet the 100-character convention. The node's `lean.statement` was
checked verbatim against the file's full theorem signature. Compilation through
`scompile.py` succeeded (exit 0, 2.0 seconds), without warnings.
