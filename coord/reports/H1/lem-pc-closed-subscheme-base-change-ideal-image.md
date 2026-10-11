## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage` states
`AlgebraicGeometry.closedSubscheme_baseChange_ideal_image`, with its only proof `sorry`.
No definitions or additional nodes are needed. Nothing is proved.

Hypotheses and clauses, in order:

- Schemes S, Z, Y: `{S Z Y : Scheme.{u}}`, for explicitly declared arbitrary universe `u`.
- The closed immersion i: `(i : Z ⟶ S) [IsClosedImmersion i]`.
- Its ideal I is not additional independent data: `i.ker`, as in the dependency record.
  The existing bridge `i.ker.toModules` realizes it as an actual module sheaf and
  `i.ker.toModulesι` is its inclusion in `SheafOfModules.unit S.ringCatSheaf`.
- The arbitrary morphism g: `(g : Y ⟶ S)`; there is no flatness assumption.
- The fibre product and its projection q: `pullback i g` and `pullback.snd i g`.
- The first conclusion: `IsClosedImmersion (pullback.snd i g)`.
- The ideal of q, including its position inside O_Y:
  `Subobject.mk (pullback.snd i g).ker.toModulesι`.
  For a closed immersion `Hom.ker` is the kernel ideal on affine opens; the
  `IdealSheafData.toModules` bridge recovers that quasi-coherent ideal as a module sheaf.
- Pullback of the ideal inclusion: `(Scheme.Modules.tensorPullback g).map i.ker.toModulesι`.
  Its source is g*I and target is g*O_S.
- The displayed epsilon is the inverse hom-equivalence applied to
  `SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom`, the O_S-linear
  structure-sheaf map O_S → g_*O_Y. The adjunction is obtained by `Classical.choice`
  from the dependency's `nonempty_tensorPullbackAdjunction g`. Thus epsilon is,
  literally, the map adjoint to g-sharp under that tensor-pullback adjunction.
  This choice is made in the expression, not assumed as additional input. Changing
  the adjunction precomposes the composite by an automorphism of g*I, so leaves its
  image subobject unchanged.
- The second conclusion is equality with `imageSubobject` of this composite.
  It is equality of subobjects of O_Y, not an isomorphism of abstract objects, and
  not equality of sectionwise ranges on every open (which would be stronger).

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `AlgebraicGeometry.Scheme.Hom.ker`
  and `Hom.ker_apply` (latter for interpretation, not in the signature).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.snd`.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback` and
  `Scheme.Modules.nonempty_tensorPullbackAdjunction` (both under `AlgebraicGeometry`).

The source's existing `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`
provides `IdealSheafData.toModules` and `toModulesι`, with docstrings and affine-open
identification checked. `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`
provides `unitToPushforwardObjUnit`; `Mathlib.CategoryTheory.Subobject.Limits`
provides `imageSubobject`. No private copy of any notion is introduced.

Source checked: [Stacks Tag 01JU, Lemma 26.17.6 (1)](https://stacks.math.columbia.edu/tag/01JU).
The local `literature/stacks-project/schemes.tex` is absent on this machine, so the
published tag was read. Its two clauses are exactly the closed-immersion and
image-ideal conclusions. The docstring records the node's single proof step and
also the source's direct proof route. The proof dependency `lem-pc-closed-imm-base-change`
has an unrelated existing Lean record (`IsVeryAmple.pullback_of_field`); this is
reported for later proof work, not imported or used to define the present statement.
It is not a statement dependency of this item.

Edge cases checked: empty Z gives the unit ideal on Y; i an isomorphism gives the
zero ideal; empty Y gives equality in the zero module category. Arbitrary nonflat
g is included: for Spec(Z/2) → Spec(Z), pulling back the ideal (2) can have a
nonzero kernel, while the image is the ideal of the base change. The conclusion
asserts an image, not injectivity. No Noetherian, affine, field, or characteristic
hypothesis is imposed. Arbitrary schemes in every universe u are allowed.

Searches (all via `msearch.py H1 lem-pc-closed-subscheme-base-change-ideal-image`
unless indicated):

- leanfinder: `ideal sheaf of base change of closed immersion is image of pullback ideal sheaf`:
  eight hits, including `IdealSheafData.comap`, `map`, `ker_fst_of_isClosedImmersion`,
  `comap_map_le`, `ideal_map`, `ideal_map_of_isAffineHom`, `map_vanishingIdeal`,
  `le_map_comap`. These give ideal data/comap statements, not this module-image formula.
- loogle: `AlgebraicGeometry.Scheme.IdealSheafData.toModules, image`: no hits;
  unknown identifier (the bridge is a project declaration).
- grep: `toModules|image.*pullback|pullback.*image` in `AlgebraicGeometry/IdealSheaf`:
  four hits, in Basic and Functorial, none the sheaf-image assertion.
- leansearch: `closed immersion base change ideal sheaf image pullback`:
  unavailable, Internal Server Error; no verdict assigned to that service.
- `rg` in the source project's IdealSheaf and Modules directories located the
  toModules bridge and affine-local `ideal_comap_appLE`, but no exact image theorem.
- `rg` in `lean/Sheaf` for ideal/image/base-change combinations: no exact theorem;
  located and read the recorded tensor-pullback dependency.
- `rg` for the exact item tag throughout `WeilConjectures`: no occurrence.
  The new full declaration name was checked against Mathlib/project source by search;
  the delivery preflight also checks the declaration-name inventories.

Validation: `scompile.py H1 lem-pc-closed-subscheme-base-change-ideal-image`
compiled the module on the server in 1.9 s, exit 0, with no warnings.


## Second reading by H1

I independently read the delivered node, its Lean module, all five statement
 dependency nodes and their recorded declarations, the tensor-pullback module,
 and the source ideal-sheaf bridge. No mathematical mismatch was found; the Lean
 statement and node record are unchanged. Only this independent report was added.

Object/hypothesis/conclusion inventory and correspondence (H3):

1. Arbitrary schemes S, Z, Y: `{S Z Y : Scheme.{u}}`, with explicitly bound `u`.
   `Scheme` is a locally ringed space locally isomorphic to affine spectra.
   Verdict: same objects, no affine, field, Noetherian or finiteness restriction.
2. Closed immersion i: `(i : Z ⟶ S) [IsClosedImmersion i]`.
   The recorded Mathlib class combines a closed embedding and surjective stalk
   maps, equivalent to the source's closed immersion. Verdict: exact hypothesis.
3. Its defining ideal I inside O_S: `i.ker.toModules` and `i.ker.toModulesι`.
   I is determined by i, not arbitrary additional data. `Hom.ker_apply` identifies
   its affine ideals with the actual section kernels, since a closed immersion
   is quasi-compact. The existing `IdealSheafData.toModules` is a genuine module
   kernel with inclusion `toModulesι`; `range_toModulesι_app` identifies the
   inclusion's affine ranges with those ideals. Thus the associated ideal
   subsheaf equals ker(O_S → i_*O_Z), by equality on the affine basis.
   Verdict: precisely the dependency node's ideal, not a private replacement.
4. Arbitrary scheme morphism g: `(g : Y ⟶ S)`. Verdict: exact, no flatness added.
5. Fibre product and q: `pullback i g` and `pullback.snd i g`.
   The recorded `Limits.pullback`, its projections and universal property are
   used, with scheme pullbacks supplied by the imported library. Verdict: exact.
6. q is a closed immersion: the first conjunct
   `IsClosedImmersion (pullback.snd i g)`. Verdict: full first conclusion.
7. q's defining kernel ideal inside O_Y:
   `Subobject.mk (pullback.snd i g).ker.toModulesι`.
   The first conjunct and existing base-change closed-immersion instance ensure
   q is quasi-compact, so the same affine-kernel bridge as in item 3 applies.
   Verdict: actual defining ideal with its inclusion, not just an abstract module.
8. g*I → g*O_S: `(Scheme.Modules.tensorPullback g).map i.ker.toModulesι`.
   The recorded dependency explicitly uses inverse image of modules, extension
   of scalars along g's ring map, and module sheafification. Its functor laws
   depend on named proof theorems; no data definition contains `sorry`.
   Verdict: the node's tensor pullback and inclusion map, no stronger hypothesis.
9. epsilon_g: the chosen `nonempty_tensorPullbackAdjunction g` has right adjoint
   `Scheme.Modules.pushforward g`, definitionally the Mathlib module pushforward.
   Applying its inverse `homEquiv` to
   `unitToPushforwardObjUnit g.toRingCatSheafHom` gives precisely the adjoint of
   g-sharp: the latter map's component sends a to g-sharp(a), as its definition
   and `unitToPushforwardObjUnit_val_app_apply` show. No adjunction is assumed
   as new input. Any alternative adjunction differs by a natural automorphism
   alpha of g*. Naturality gives alpha(O_S) composed with g*(inclusion) equal
   to g*(inclusion) composed with alpha(I), so the resulting composite differs
   by an isomorphism of its source and has the same image subobject.
   Verdict: the specified adjoint map has exactly the required image.
10. Equality with the image of the composite: `imageSubobject` of the map in
    items 8 and 9, equated in `Subobject (SheafOfModules.unit Y.ringCatSheaf)`.
    Verdict: full second conclusion, including its embedding in O_Y. This is
    the sheaf image; it does not require surjectivity onto sectionwise ranges
    on arbitrary opens or injectivity of the pulled-back inclusion.

Source check: the repository does not contain the Stacks .tex checkout.
I read published [Tag 01JU](https://stacks.math.columbia.edu/tag/01JU), and fetched
`schemes.tex` from the Stacks project's official GitHub source into this item's
`scratchpad/schemes.tex`. At `lemma-fibre-product-immersion` the only hypotheses
are two scheme morphisms with common target, with the first closed for part (1).
The section introduces no ambient field, characteristic or finiteness condition.
Part (1) gives both conclusions. Its proof constructs the closed subspace cut
out by the image, identifies its locally ringed space with the fibre product,
and uses `lemma-closed-subspace-scheme` to see it is a scheme. The declaration
and module docstrings cite the source and blueprint, and the declaration
records the node's one proof step with `lem-pc-closed-imm-base-change` as well
as this direct source route. There is no delivered statement correction,
new definition node or dependency module, so H12/H13 and citer-change audits
have no new records to check. The proof-only dependency's unrelated existing
Lean record was already correctly reported by the worker; it is not used in
the present signature and must be repaired when that proof node is formalized.

Edge cases: empty Z gives I = O_S and image O_Y, including empty Y; an
isomorphism i gives I = 0 and image 0. Empty S forces empty Z and Y. For the
nonflat map Spec(Z/2) → Spec(Z) with i defined by (2), the pullback ideal module
can be nonzero while its image and q's ideal are zero; the formula includes
this case. Zero rings and every characteristic are covered. There is no index
set or natural-number parameter, hence no empty-index or n = 0 exclusion.
The explicit arbitrary universe u imposes no fixed size bound: schemes can
all be placed in a common universe. Every identifier's variables are bound.

Independent H4 searches, using different wording from the worker:

- LeanFinder via msearch: `extension of scalars kernel ideal closed subscheme
  cartesian square image subobject`: eight hits. The closest was
  `IdealSheafData.ker_fst_of_isClosedImmersion`; reading its signature and
  `comap` definition shows an ideal-data equality, with no module-image clause.
- Loogle via msearch: `AlgebraicGeometry.Scheme.IdealSheafData.comap`: twelve
  hits, including `comapIso`, `ker_fst_of_isClosedImmersion` in the direct
  source search, and composition/order results. No full image statement.
- LeanSearch via msearch: `defining ideal of fiber product closed subscheme
  extension of scalars image`: Internal Server Error, recorded unavailable;
  no negative mathematical verdict inferred from an unavailable service.
- rg of Mathlib IdealSheaf and project IdealSheaf for `imageSubobject`,
  `toModules`, `ker_fst_of_isClosedImmersion`, `ideal_comap_appLE` located only
  the bridge and affine extension-of-ideal formula. I opened these definitions
  and signatures; neither states the present sheaf-image equality.
- rg across repository lean/Sheaf and source WeilConjectures for
  `ideal.*image|image.*ideal|closedSubscheme_baseChange` found no exact statement.
  The exact declaration name and node id have no upstream inventory/source hit.

H5/H6/H8/H9: no new definition, one named theorem with proof exactly `sorry`,
source/blueprint docstrings and complete node proof step, standard namespace,
all four imports used, lines within 100 characters, no implicit variable or
universe. The node's `lean.statement` was compared programmatically with the
file's exact signature and is verbatim equal.

Validation: independent scompile invocation with the absolute sandbox module
path compiled cleanly on the server in 1.8 seconds, exit 0, no warnings. An
initial relative-path invocation from the read-only repository could not locate
the sandbox file; correcting the invocation path resolved it without edits.
