## Worker report

The module `Sheaf.AlgebraicGeometry.FlatResidueFibreSquare` states
`AlgebraicGeometry.flat_residue_fibre_square`, with its proof `sorry`. No definition,
new node, dependency repair, or statement correction is needed. The statement is
unchanged. Source checked: Stacks Project, `more-morphisms.tex`, Tag 05VJ, proof of
`lemma-base-change-criterion-flatness-fibre`, final cartesian diagram and the sentence
asserting that its horizontal arrows are base changes of the flat residue-field map.
Although the surrounding flat-locus lemma has finiteness hypotheses, the diagram and
flatness assertion extracted here are purely properties of pullbacks and field maps.

Hypotheses and objects, clause by clause:

- Schemes `S,X,Y,T`: `{S X Y T : Scheme.{u}}`, with the universe explicitly declared.
  Morphisms `p,q,f,h` are separate binders with exactly the node's sources and targets.
- The condition `q ∘ f = p` is `hf : f ≫ q = p`. The point is `(t : T)` and its image
  `s` is written directly as `h t`, so no equality-of-points hypothesis is imposed.
- `X_T` and `Y_T` are `pullback p h` and `pullback q h`. The structure maps to `T`
  are `pullback.snd p h` and `pullback.snd q h`, and the maps to `X,Y` are `pullback.fst`.
- The residue-field homomorphism is exactly `h.residueFieldMap t`; its spectrum map
  `e` is `Spec.map (h.residueFieldMap t)`.
- The morphism over `S` is `(Over.homMk f hf : Over.mk p ⟶ Over.mk q)`. Its image
  under `Over.pullback h`, followed by `.left`, is the induced `f_T`. Pulling back
  this over-`T` morphism along `T.fromSpecResidueField t` gives `(f_T)_t`.
  Pulling back the original over-`S` morphism along `S.fromSpecResidueField (h t)`
  gives `f_s`. These are Mathlib's actual universal pullback maps, not extra map
  parameters. The definition of `Over.pullback` and its full signature were read.
- The first two conclusions supply isomorphisms `α` and `β` from the new fibres to
  `pullback (p.fiberToSpecResidueField (h t)) (Spec.map (h.residueFieldMap t))` and
  its `q` counterpart. Each has first projection `a` or `b` and second projection
  equal to the canonical residue-field projection of the new fibre.
- The explicit equality `a ≫ f_s = (f_T)_t ≫ b` renders the commuting square.
  `IsPullback a (f_T)_t f_s b` renders its cartesianness with the same maps and objects.
- The next two equalities are exactly the node's fibre-inclusion identities:
  `a ≫ p.fiberι (h t) = (pullback.snd p h).fiberι t ≫ pullback.fst p h` and the
  corresponding equality for `q,b`.
- The final three conjuncts are `Flat e`, `Flat a`, and `Flat b`. No assumptions
  of finite type, finite presentation, flatness, or Noetherianity occur anywhere.

Canonicity: `a` and `b` are existentially introduced together with the comparison
isomorphisms, rather than assumed. Their inclusion identities and their scalar
projection identities specify both coordinates in the defining old fibre pullback,
so they uniquely specify the canonical maps. The two coordinates of each isomorphism
then specify the canonical isomorphism uniquely. Thus the existential formulation
does not replace the comparison by an arbitrary map or an arbitrary isomorphism.

Dependency declarations used (all signatures and docstrings read in source):

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`,
  and `.map`, in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, in `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`, `.fiberι`, and
  `.fiberToSpecResidueField`, in `Mathlib.AlgebraicGeometry.Fiber`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`, with its stalkwise equivalence
  `Flat.iff_flat_stalkMap`, in `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- Proof leaves: `isPullback_fiberToSpecResidueField_of_isPullback` in the fibre module;
  `Flat.SpecMap_iff`, the field-target flatness instance, and
  `Flat.isStableUnderBaseChange` in the flatness module. These cover the three
  non-elementary proof steps without requiring a new dependency interface.

Imports are public statement imports `Mathlib.AlgebraicGeometry.Fiber`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`, and
`Mathlib.CategoryTheory.Comma.Over.Pullback`; the first two also supply every
recorded proof-dependency module. No additional private proof import is needed.
The docstring includes all three proof steps and the explicit universal-property
argument, with their DAG identifiers.

Edge cases checked before writing: empty `T` has no `t`, so the assertion is vacuous
as required; empty `X` or `Y` gives empty corresponding fibres and the usual empty
pullbacks. Identity `h` and identity `f` are included by the same functorial maps.
Arbitrary residue-field extensions, including inseparable and infinite extensions,
are allowed: flatness of a field extension has no finiteness or separability premise.
Nonflat and non-Noetherian parameter maps are admitted; only the residue-field
extension and its pullbacks are asserted flat. All schemes lie in an arbitrary
common universe `u`, and no independent test-scheme universe restricts the assertion.
`set_option autoImplicit false` confirms that every variable is explicitly bound.
No disputed statement or node fault was found.

Searches for an existing declaration:

- `msearch.py leanfinder`, query "For arbitrary scheme maps X to Y over S and T to S,
  residue fibre comparison maps form a cartesian square and are flat": eight hits,
  chiefly `Scheme.Pullback.Triplet.Spec_map_tensor_isPullback`, residue-field
  tensor-product identities, and `Flat.instSndScheme`. None states this simultaneous
  natural square together with the isomorphisms, inclusion identities and flatness.
- `msearch.py loogle`, query `"AlgebraicGeometry.Scheme.Hom.fiber", "Flat"`: no hits.
- `msearch.py grep`, query
  `fiber.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*fiber|fiber.*[Ff]lat|[Ff]lat.*fiber`
  restricted to `AlgebraicGeometry`: three `SmoothFiber.lean` hits about smoothness,
  not this assertion.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for fibre/base-change patterns:
  related declarations include upstream `baseChange_fiber` in
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, whose full source was
  read; it identifies a different pullback with a fibre, without this natural square
  or the flatness assertions. Mathlib's recorded fibre comparison is reused in the
  proof plan. Neither root contains the item's blueprint identifier or a declaration
  `flat_residue_fibre_square`. No exact existing declaration was found.

Validation: `scompile.py` compiled the module in sandbox and library modes cleanly.
Every proof is `sorry`; there are no helper definitions or additional postponed
theorems. Delivery preflight and its final compilation are run through `deliver2.py`.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
