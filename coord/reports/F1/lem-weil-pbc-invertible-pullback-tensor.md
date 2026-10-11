## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor` in
`lean/Sheaf/AlgebraicGeometry/Modules/InvertiblePullbackTensor.lean`. Its only proof is
`sorry`. The auxiliary module `ResidueFiber.lean` contains two complete definitions,
`residueFiber` and `residueValue`; it has no postponed data or proofs.
No correction of the item's statement was needed.

Hypotheses and clauses, in the order of the node:

- Schemes and their morphism are `{X Y : Scheme.{v}} (f : X ⟶ Y)`, with arbitrary
  universe `v`. Invertible modules are quantified as `(L M : Y.Modules)` with
  `[L.IsInvertible] [M.IsInvertible]`, using exactly Scheme.Modules.IsInvertible.
  The conjunction quantifies these modules separately for the different clauses;
  these universal quantifiers express the node for every permitted pair.
- The fibre introduced in the statement is `residueFiber L y`, the module
  `κ(y) ⊗[O_Y,y] L_y`. The node writes the factors in the opposite order. The canonical
  tensor flip identifies the two conventions; our section value is `1 ⊗ s_y`, hence
  the same value as the node's `s_y ⊗ 1`. Scalars are supplied by the actual residue
  map `(Y.residue y).hom`, not an arbitrary algebra structure. The first conjunct
  explicitly states `Module.rank (Y.residueField y) (residueFiber L y) = 1`.
- The local `pb` abbreviation is the map on sections of the unit of
  `Classical.choose (exists_tensorPullbackAdjunction h)`. It is quantified over
  arbitrary schemes, morphisms, modules, and opens. Thus `pb f L V s` has precisely
  the node's meaning of `f^*s`, on `f ⁻¹ᵁ V`. This uses the canonical adjunction
  characterized by the tensor/inverse-image unit, rather than an unspecified choice
  of adjunction. Tensor sections are the existing `tmulSection`, explicitly defined
  upstream as the sheafification image of a pure section tensor.
- (1): the first conjunct includes `((tensorPullback f).obj L).IsInvertible`;
  the second says `(L ⊗ M).IsInvertible` for each invertible pair.
- (2), tensor comparison: the third conjunct supplies an isomorphism family
  `e L M : (tensorPullback f).obj (L ⊗ M) ≅
  (tensorPullback f).obj L ⊗ (tensorPullback f).obj M`.
  Naturality is the commuting square for every `a : L ⟶ L'`, `b : M ⟶ M'`
  between invertible modules, expressed by equality of composites with `(e _ _).hom`.
  Its second condition, for every open `V` and sections `s,t`, sends
  `pb f (L ⊗ M) V (tmulSection s t)` to `tmulSection (pb f L V s) (pb f M V t)`.
- (2), composition: for every `W`, `g : W ⟶ X` and invertible `L`, the fourth
  conjunct gives `e : (tensorPullback g).obj ((tensorPullback f).obj L) ≅
  (tensorPullback (g ≫ f)).obj L`, and an equality on every pulled-back section.
  The direction is exactly `g^*f^*L → (f ∘ g)^*L` (`g ≫ f` is `f ∘ g`).
  Both source opens reduce to the same inverse-image open. The requirement on all
  pulled-back sections characterizes the canonical comparison: their germs generate
  the pulled-back modules locally over the structure ring.
- (2), symmetry: the fifth conjunct uses the existing symmetry isomorphism
  `β_ L M` and says its hom sends `tmulSection s t` to `tmulSection t s`.
  The sixth spells out the parenthetical finite reordering consequence: for every
  `n`, family `L : Fin n → Y.Modules` of invertibles and permutation `π`, it supplies
  an isomorphism of the iterated tensors in the original and permuted order.
  The tensor is a right-associated `List.ofFn` fold with the tensor unit at the end.
  The permuted factor at position `i` is `L (π.symm i)`, moving factor `i` to `π i`.
  Associators and unitors identify this bracketing with any finite tensor bracketing.
- (3), pullback fibre: the seventh conjunct gives an isomorphism of
  `X.residueField x`-modules between the pulled-back fibre and extension of
  `residueFiber L (f x)` along `(f.residueFieldMap x).hom`. This is exactly the
  node's field extension; the scalar-extension notation writes the field first.
  For every section over `V` containing `f x`, the isomorphism sends
  `residueValue (pb f L V s) x hx` to `1 ⊗ residueValue s (f x) hx`.
- (3), tensor fibre: the last conjunct gives an isomorphism in
  `ModuleCat (Y.residueField y)` from `residueFiber (L ⊗ M) y` to
  `residueFiber L y ⊗ residueFiber M y`. For every `V,hy,s,t`, its hom sends the
  value of `tmulSection s t` to the pure tensor of the two values.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`: local triviality on a neighbourhood
  of every point. Imported through TensorSection, with its scheme-specific monoidal
  and symmetric structures. No alternative invertibility predicate is introduced.
- `Sheaf.AlgebraicGeometry.TensorPullback`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, imported through its adjunction
  module. This is the tensor/inverse-image formula, not Mathlib's abstract pullback.
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.exists_tensorPullbackAdjunction`: its unit is
  characterized on all sections by the inverse-image unit and the tensor `1 ⊗ m`.
  Its already-landed node `lem-pc-module-pullback-adjunction` is added to stmt_deps.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: the existing sheaf monoidal
  structure and `SheafOfModules.tensorObjIsoSheafification`, imported through
  TensorPullbackAdjunction. The tensor definition is the sheafification tensor, also
  used by the source's `Scheme.Modules.tmulSection` in
  `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`.
- `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField`, `Scheme.residue`,
  `Scheme.Hom.residueFieldMap`, including the displayed compatibility of the residue
  map with the stalk map. No change of this Mathlib dependency record is needed.
- `Mathlib.Algebra.Category.ModuleCat.Stalk`, `TopCat.Presheaf.stalk`, with the
  `PresheafOfModules` module instance and `germ_ringCat_smul`. The source's
  `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` exposes that same
  module instance for `M.presheaf.stalk x`; it is the import of ResidueFiber.

Edge cases checked before writing: no nonemptiness, integrality, characteristic,
Noetherianity, finite-type, or affine assumption is present. For empty schemes all
pointwise assertions are vacuous but module comparisons and section formulas remain
stated. Empty opens are allowed. An invertible module cannot have zero fibre at a
point, but the empty scheme is not excluded. For `n = 0`, the finite tensor fold is
exactly the tensor unit, with its identity isomorphism available. `n = 1` includes its
unit factor, removed by the right unitor. Identity morphisms and non-invertible section
values (including zero sections) require no special hypotheses. The same universe is
used for schemes and all module fibres, as in the project's existing categories.

Searches made before writing (raw msearch results are in sandbox searches.jsonl):

- LeanFinder: `pullback invertible sheaf tensor product fibre compatibility with sections`:
  eight hits, primarily `SheafOfModules.pullbackObjFreeIso` and pullback carrier tensor
  comparisons; none gives all the node's clauses for the tensor-formula pullback.
- Loogle: `Scheme.Modules.tensorPullback, Scheme.Modules.IsInvertible`: zero hits,
  unknown `Scheme.Modules.tensorPullback` on the remote search service.
- Mathlib grep through msearch: `fiber|fibre` in `AlgebraicGeometry/Modules`: zero hits.
- LeanSearch: `fibre of sheaf of modules at point tensor stalk with residue field`:
  unavailable, Internal Server Error. This is recorded as unavailable, not no match.
- LeanFinder: `fibre of module sheaf at a point tensor product of stalk with residue field`:
  eight hits, all tilde/localized-module stalk results, not residue-field fibres.
- Mathlib grep through msearch:
  `residueFiber|residueValue|module.*[Ff]ibre|module.*[Ff]iber`: twelve hits, concerning
  topological vector bundles, quasi-finite ring fibres, and golden-ratio calculations.
- Direct source and landed-project `rg` on the same residue-fibre pattern: no declaration;
  one landed comment on nonvanishing in the residue fibre. Source searches for tensor,
  pullback, stalk and section declarations found the above reusable notions and
  PullbackMonoidal (whose pullback is the different abstract functor).
- Direct `rg` of the item id throughout `WeilConjectures`: no declaration of this node.
- DAG search for stalk/residue fibres: nodes using fibre formulas but no definition of
  the general module residue fibre. `tools/blueprint_refs.py search 'module fibre'`
  found an unrelated finite-etale trivialization of lisse sheaves.

The local Stacks .tex files are absent on this machine. The original Stacks statements
were read at https://stacks.math.columbia.edu/tag/01CD,
https://stacks.math.columbia.edu/tag/0098, and
https://stacks.math.columbia.edu/tag/01CB. They agree with the tensor and stalk formulas
used here; the eight-step proof in the item's node is reproduced in the theorem's
source docstring, including invertibility, composition, symmetry and fibre base change.
No disputed statement or node fault was found.

Validation: both modules compiled together cleanly on the server; the declaration's
`sorry` is intentional at stage 2. There is no build on this machine.

## New nodes

`def-weil-pbc-module-residue-fiber` defines the residue-field fibre and value of a section,
using the existing module stalk and residue map. Its module is
`Sheaf.AlgebraicGeometry.Modules.ResidueFiber`. It cites
`def-weil-sheaf-of-modules-category`, `def-weil-pbc-module-stalk`, and
`def-weil-residue-field`. Its source is the fibre notation of the item, with Stacks
Modules 01C5/01CB and Sheaves 0098. The searches just listed found stalks and tilde
localizations but no such general fibre or section-value declaration. Both definitions
have explicit data. Extension of scalars takes the residue field first; the tensor
flip gives exactly the node's stalk-first presentation. The new node is added to the
item's stmt_deps and retains the original blueprint ancestor and via chain.

## Second reading by F1

I read the item's original node, both sandbox modules, all six statement dependencies,
and the three dependencies of the new definition node. There is no statement correction
and no dependency module in this delivery. I retained the mathematical signatures.

Source reading: local literature has no Stacks checkout. I read the official pages
[01CD](https://stacks.math.columbia.edu/tag/01CD),
[0098](https://stacks.math.columbia.edu/tag/0098),
[01CB](https://stacks.math.columbia.edu/tag/01CB), and
[01C5](https://stacks.math.columbia.edu/tag/01C5), then downloaded the original
`modules.tex` and `sheaves.tex` from the official stacks/stacks-project repository into
this item's scratchpad. I read section-tensor-product, lemma-stalk-tensor-product,
lemma-tensor-product-pullback, lemma-pullback-invertible,
lemma-constructions-invertible, definition-pushforward,
lemma-adjoint-pullback-pushforward-modules, lemma-push-pull-composition-modules, and
lemma-stalk-pullback-modules, including the preceding section conventions. Their ambient
objects are ringed spaces and arbitrary module sheaves. Specializing to schemes and
invertible modules is exactly the item's statement, with no hidden field, flatness,
Noetherianity or nonemptiness hypothesis. Scheme stalks are nonzero local rings, so the
warning in 01C5 about zero stalk rings does not add a hypothesis here.

The node's objects, hypotheses and conclusions, matched in order:

1. Schemes X,Y and f:X→Y: `{X Y : Scheme.{v}} (f : X ⟶ Y)`. Verdict: exact,
   arbitrary schemes and morphisms; no additional instances on the schemes.
2. Invertible O_Y-modules L,M: the appropriate universal binders `(L M : Y.Modules)`
   with `[L.IsInvertible] [M.IsInvertible]`. Verdict: exact. I read
   `Scheme.Modules.IsInvertible` in upstream Modules/Invertible.lean: every point has
   a trivializing open neighbourhood. Local rank-one freeness implies quasi-coherence,
   so this does not drop the dependency node's quasi-coherence clause. The universal
   quantifiers distributed across conjuncts are logically the same hypotheses.
3. Fibre L(y) and its dimension: `residueFiber L y`, with
   `Module.rank (Y.residueField y) (residueFiber L y) = 1`. Verdict: exact.
   The new definition uses `ModuleCat.extendScalars (Y.residue y).hom` on the actual
   O_Y,y-module stalk. Scalar-first κ(y)⊗L_y is the canonical flip of the node's
   L_y⊗κ(y), so rank one is exactly one-dimensionality over this field.
4. Section value s(y): `residueValue s y hy`. Verdict: exact germ tensored with one,
   written `1 ⊗ s_y` in the same scalar-first convention, for every open containing y.
5. Pullback module and f* s: `(tensorPullback f).obj L` and the local `pb f L V s`.
   Verdict: exact. I read TensorPullback's object and morphism definitions: change
   of rings of the abelian inverse image, with the structure-sheaf ring map, then
   module sheafification. I read `exists_tensorPullbackAdjunction` in its module:
   the chosen adjunction has the specified `θ(1 ⊗ η(s))` unit. Consequently `pb`
   uses the node's canonical unit, not an unconstrained adjunction. Its arbitrary
   auxiliary N binder defines the section operation; it is not an extra hypothesis.
6. Tensor modules and tensor sections: `L ⊗ M` and `tmulSection s t`. Verdict: exact.
   The tensor dependency imports the upstream sheaf monoidal structure. I read
   `tmulSection`, `toSheafifyTensor` and `tensorObjIsoSheafification`: this is the
   image of a pure tensor under module sheafification and its canonical identification.
7. (1), invertibility of f*L: the second part of the first conjunct,
   `((tensorPullback f).obj L).IsInvertible`. Verdict: exact.
8. (1), invertibility of L⊗M: second conjunct `(L ⊗ M).IsInvertible`. Verdict: exact.
9. (2), functorial tensor comparison: third conjunct's family `e L M` of isomorphisms
   and the square for every `a : L ⟶ L'`, `b : M ⟶ M'`. Verdict: exact naturality
   between the same invertible objects, not merely unrelated pointwise isomorphisms.
10. (2), tensor comparison on sections: `(e L M).hom.app (f ⁻¹ᵁ V)` sends
    `pb f (L ⊗ M) V (tmulSection s t)` to
    `tmulSection (pb f L V s) (pb f M V t)`. Verdict: exact, every V,s,t.
11. (2), composition: fourth conjunct quantifies every W,g,L and gives
    `e : g* (f* L) ≅ (g ≫ f)* L`, with the displayed equality for every V,s.
    Verdict: exact order (`g ≫ f` is f∘g) and action on sections. The section condition
    pins the canonical comparison: pulled-back germs of sections generate locally,
    and the comparison is linear. Thus an arbitrary isomorphism is not substituted
    for the canonical one; compatibility also forces its usual naturality.
12. (2), symmetry: fifth conjunct uses the actual isomorphism `β_ L M` and sends
    `tmulSection s t` to `tmulSection t s`. Verdict: exact, including invertibility
    of the comparison, already carried by the Iso type.
13. (2), finite reordering consequence: sixth conjunct quantifies n, the invertible
    family `L : Fin n → Y.Modules`, and every permutation; the target family is
    `L (π.symm i)`. Verdict: exact movement of factor i to π(i). A right-associated
    fold ending in the unit is a valid bracketing of the finite tensor product.
    The statement asks for reordering isomorphisms; the stronger section description
    in its natural-language proof is not an additional clause of the node statement.
14. (3), pullback fibre: seventh conjunct's Iso has target
    `(ModuleCat.extendScalars (f.residueFieldMap x).hom).obj (residueFiber L (f x))`.
    Verdict: exact κ(x)-linear comparison with extension of L(f(x)) along the
    induced residue-field map. I read `residueField`, `residue`, `residueFieldMap`,
    and `residue_residueFieldMap` in Mathlib: no arbitrary algebra map is involved.
15. (3), value of pulled-back section: its hom sends
    `residueValue (pb f L V s) x hx` to `1 ⊗ residueValue s (f x) hx`.
    Verdict: exact s(f(x))⊗1 after the tensor flip, for every V containing f(x).
16. (3), tensor fibre: final conjunct's Iso is in `ModuleCat (Y.residueField y)`
    from `residueFiber (L ⊗ M) y` to `residueFiber L y ⊗ residueFiber M y`.
    Its hom sends the value of `tmulSection s t` to the pure tensor of the two values.
    Verdict: exact both the identification and every section-value clause.

Edge cases: no empty scheme or empty open is excluded. On empty schemes pointwise
claims are vacuous while section and module comparisons are retained. Zero sections
are allowed throughout. A zero module is not invertible on a nonempty scheme, as the
node requires; on the empty scheme the invertibility predicate is vacuous. The finite
family binder includes n=0, where each fold is the unit; n=1 includes the removable
unit factor. All characteristics are covered, and no field base is assumed. The
universe v is arbitrary and bounds schemes, their structure rings, stalks and invertible
modules together. Rank-one modules have the scheme's size; no independent small test
universe or finiteness instance excludes larger schemes. No variable or universe in
either signature is unbound.

Independent H4/H12 searches, using different wording from the worker:

- LeanFinder via msearch: `line bundle residue field base extension of fibre and tensor
  product sheaves`. Eight hits concerned Scheme.Pullback.Triplet residue-field pushouts,
  scheme-theoretic fibres, PrimeSpectrum fibres, and Scheme.Γevaluation. None is a module
  residue fibre or the conjunction here. Γevaluation evaluates structure-sheaf global
  sections, rather than sections of arbitrary modules.
- Loogle via msearch: `ModuleCat.extendScalars, TopCat.Presheaf.stalk`: zero hits.
- LeanSearch via msearch: `value of section in residue field tensor module stalk for a
  scheme`: service returned Internal Server Error. This is unavailable, not a no-match.
- Direct rg in Mathlib/AlgebraicGeometry, WeilConjectures/AlgebraicGeometry and landed
  lean/Sheaf/AlgebraicGeometry for `residue.*(stalk|[Ff]ib)`,
  `([Ff]ib|[Vv]alue).*residue`, and the declaration name. Hits were residue maps,
  scheme fibres and uses of cohomology on fibres, not a general module-fibre definition.
  Reading upstream Modules/PullbackMonoidal and TensorSection confirmed reuse of the
  tensor structure and symmetry, but its pullback is the abstract functor and does not
  state this conjunction for tensorPullback. I also searched dag/lean_names_upstream.json:
  no residueFiber, residueValue, or invertible_pullback_tensor declaration.
- DAG search for fibre/stalk/residue expressions found formulas inline in the ample
  invertible-module and related nodes, not a node defining the general fibre and value.
  The general module stalk already has its own node, correctly reused here.

New node review: `def-weil-pbc-module-residue-fiber` is genuinely absent as a declaration
and as a separate DAG notion. Its statement introduces arbitrary X,M,x,U,s and hx and
uses exactly the module category, stalk and residue-map dependencies. I read Mathlib's
SheafOfModules structure and its stalk Module instance/germ_ringCat_smul, and upstream
FlatPullbackStalk's scheme-specific instance exposing that same action on M.presheaf.
The two definitions are explicit extension of scalars and pure tensor of a germ; no
postponed data, well-definedness proof or duplicate stalk construction. This is precisely
the fibre notation of the source item, with the stalk/tensor operations in 0098/01CB.
Its definition-kind/split-status, empty proof fields, null mathlib_match, search records,
created record, chapter/unit, ancestor/via chain, none audits and lean record satisfy
§5. It is cited in the item's stmt_deps. There is no dependency module to review.

Mismatches and repairs: no mathematical or signature mismatch found. The residue-fibre
module had two definitions but no Main definitions list required by the multi-declaration
module convention. I added that documentation list only. The item's eight-step proof
is present in its theorem docstring in order, with the source places and blueprint id.
Only the item's named theorem contains sorry, as required for stage 2; nothing is proved.
The new definitions have their own source/blueprint docstrings and no sorry. Imports
are used, declaration namespaces carry no Sheaf prefix, and lines meet the length bound.
The node's lean.statement remains verbatim the corresponding source signature.

Validation: scompile compiled both modules together in dependency order with exit code 0
and no warnings. The final delivery dry run and delivery recompile the documentation
change and check the signatures and node fields mechanically.
