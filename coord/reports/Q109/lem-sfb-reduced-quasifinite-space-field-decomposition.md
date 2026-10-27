## Worker report

Item: `lem-sfb-reduced-quasifinite-space-field-decomposition`.
Module: `Sheaf.AlgebraicGeometry.ReducedQuasiFiniteSpaceFieldDecomposition`.
Declaration:
`AlgebraicGeometry.AlgebraicSpace.exists_iso_coproduct_spec_finite_fields_of_reduced_locallyQuasiFinite`.

This delivery states the accepted reduced specialization of Stacks 06S0, (1) implies
(5). It adds one theorem with whole proof `by sorry`, no definitions or other theorems.
The only node-field change is `lean`. The source was read in
`literature/stacks-project/spaces-over-fields.tex`, lines 1815–1842: locally quasi-finite
spaces over a field are schemes and disjoint unions of spectra of finite-dimensional
local Artinian algebras. Reducedness makes these algebras fields, as in the node's
accepted four-step proof, reproduced in the declaration docstring.

Hypotheses and conclusions, clause by clause:

- A field k: `(k : Type u) [Field k]`, the Mathlib field with nonzero identity and
  inverses for nonzero elements. No characteristic or perfectness condition occurs.
- X an algebraic space over Spec k:
  `(X : AlgebraicSpace (Spec (.of k)))`. This is the recorded full subcategory of
  fppf sheaves with representable diagonal and a surjective etale atlas.
- Reducedness means that some etale scheme atlas has reduced local rings:
  `hreduced` existentially quantifies an object `U : Over (Spec (.of k))` and
  `a : yoneda.obj U ⟶ X.obj.obj`, requires `IsEtale a ∧ IsSurjective a`, and then
  `∀ x : U.left, _root_.IsReduced (U.left.presheaf.stalk x)`.
  There is no requirement that this atlas be quasi-compact, affine, or nonempty.
  The existential atlas is a hypothesis, not additional chosen data in X.
- Local quasi-finiteness on every etale scheme chart: `hquasifinite` quantifies
  every `V : Over (Spec (.of k))` and every `a : yoneda.obj V ⟶ X.obj.obj` and
  requires `IsEtale a → V.hom.IsLocallyQuasiFinite`.
  `V.hom` is exactly its structural map to Spec k. The predicate is the recorded
  Stacks definition, which includes local finite type; bare Mathlib
  `LocallyQuasiFinite` would omit that condition and is deliberately not substituted.
- A set I: `∃ (I : Type u)`. There is no `Finite`, `Fintype`, or `Nonempty` binder.
  This universe admits the component set of a u-small atlas and hence of X.
- A field extension K_i/k for each i: `K : I → Type u`, `∀ i, Field (K i)`,
  and `∀ i, Algebra k (K i)`. A unital map from the nonzero field k to a field
  is injective, so this is exactly a field extension; no separability is required.
- Finite dimension of every extension: `∀ i, Module.Finite k (K i)`. Over a
  field this says finite vector-space dimension. No uniform degree bound occurs.
- The disjoint union of the represented schemes, over k: each summand's structure
  morphism is `Spec.map (CommRingCat.ofHom (algebraMap k (K i)))`.
  `Sigma.desc` of these morphisms has domain the actual scheme coproduct of all
  these spectra. `Over.mk` equips that disjoint union with this precise structure
  map to Spec k; `yoneda.obj` regards it as its represented presheaf on schemes
  over k. In particular this is not the pointwise presheaf coproduct of yonedas.
- The required isomorphism is
  `Nonempty (X.obj.obj ≅ yoneda.obj (Over.mk (Sigma.desc ...)))`.
  It is a natural isomorphism on `(Over (Spec k))ᵒᵖ`. Thus it already respects
  the base k; no structural-map compatibility clause is missing. Algebraic spaces
  form a full subcategory of sheaves, and sheaves form a full subcategory of
  presheaves, so this is precisely an isomorphism of the corresponding algebraic
  spaces, including the assertion that X is represented by that scheme. The
  represented presheaf inherits its sheaf and algebraic-space properties from X
  by the isomorphism. No arbitrary map replaces a canonical construction.
- No quasi-compactness, separatedness, or perfectness is assumed anywhere.

Dependency declarations used, with signatures and docstrings read in the checkout:

- `def-weil-field`: `Field`, Mathlib `Mathlib.Algebra.Field.Defs`.
- `pqf-def-quasifinite`:
  `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, whose definition is
  `∀ x, IsQuasiFiniteAtPoint f x`. Its pointwise definition uses finite type
  and the recorded ring-level quasi-finite-at-prime predicate on affine charts.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicGeometry.AlgebraicSpace.IsEtale`,
  and `AlgebraicGeometry.AlgebraicSpace.IsSurjective`. The latter two explicitly
  test scheme base changes using `IsRepresentableWith` and pullback squares.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- Mathlib's scheme coproduct (`Mathlib.AlgebraicGeometry.Limits`), `Sigma.desc`,
  `Over.mk`, `yoneda`, and `Module.Finite` are used without private replacements.

The available recorded proof dependencies are imported without `public`:
`WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`,
`Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension`,
`WeilConjectures.Mathlib.Topology.KrullDimension`,
`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`,
`Mathlib.AlgebraicGeometry.Properties` (`def-pc-reduced-scheme`), and
`Mathlib.RingTheory.Artinian.Module` (`IsArtinianRing.equivPi`, the Mathlib match
of `lem-sfb-reduced-artinian-residue-product`). The statement dependency
`QuasiFiniteMorphism` is public even though it is also a proof dependency.
`Sheaf.AlgebraicGeometry.SpaceSmoothReducedLocality` is also imported: its
`AlgebraicGeometry.AlgebraicSpace.smooth_reduced_locality` now supplies the recorded
reducedness descent proof input. It landed after the preserved draft was written;
its full signature and docstring were read on resumption.
`lem-sfb-zero-dimensional-field-space-components` has no recorded Lean module or
Mathlib match in the current checkout, so its future proof import is omitted and
must be added when stated. It is not needed to type this theorem's statement.
No import cycle is introduced.

Edge cases checked before writing:

- Empty X: choose an empty atlas; the local-ring condition and all conditions on
  the component fields are vacuous. The conclusion admits empty I and the empty
  scheme coproduct; there is no nonemptiness binder.
- Arbitrarily infinite disjoint unions of finite field spectra: the atlas and
  index set are unrestricted, and neither the input nor output is quasi-compact.
- Purely inseparable finite extensions over an imperfect field: allowed by
  `Field`, `Algebra`, and `Module.Finite`; there is no separability assumption.
- Dual numbers over k: local quasi-finiteness holds but reducedness fails. The
  reduced-local-ring atlas condition is essential, not a hollow hypothesis.
- Positive-dimensional reduced schemes, for example the affine line over k:
  they fail the chartwise Stacks local quasi-finiteness hypothesis.
- Component size: the definition of algebraic space uses an atlas by u-small
  schemes, so the component set can be taken u-small. All field spectra and the
  scheme coproduct are in the same Scheme universe; no extra size equality is
  imposed on independent mathematical data.

Searches for an existing statement (Q109 wrapper searches were actually run):

- `msearch.py ... leanfinder "A reduced algebraic space locally quasi finite over
  a field is a disjoint union of spectra of finite field extensions"`: eight
  hits, including the unique point of a field spectrum, finite integral schemes,
  finite sigmaSpec, and finite discrete affine schemes. None states the result
  for arbitrary reduced algebraic spaces and an arbitrary component set.
- `msearch.py ... loogle "AlgebraicSpace, IsLocallyQuasiFinite"`: zero hits;
  unknown identifier `AlgebraicSpace` in the Mathlib search service.
- `msearch.py ... grep "AlgebraicSpace|reduced.*quasi.*finite.*field"
  AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch "Reduced locally quasi-finite algebraic space over
  a field decomposes into spectra of finite extensions"`: eight hits on
  `LocallyQuasiFinite`, `Algebra.QuasiFinite`, residue-field finiteness, and
  formally unramified algebras being reduced. No exact statement.
- `rg -n 'reduced.*quasi.*finite|field.*decomposition|quasi.*finite.*field'
  lean/WeilConjectures lean/Sheaf`: no exact statement. Read the nearby
  `UnramifiedFieldFibreDecomposition` declaration: it is about schemes with an
  unramified structural map and separable fields, so does not cover this node.
- `grep -rn 'lem-sfb-reduced-quasifinite-space-field-decomposition'
  lean/WeilConjectures`: no hits.
- Searches of the algebraic-space modules for reducedness, local quasi-finiteness,
  and scheme representation found the recorded atlas calculus and the chartwise
  convention in `SpaceFieldDiscretenessCriterion`; these are used as the existing
  interfaces rather than replaced by new definitions.

No statement dispute or node correction is necessary. The inherited stage-1 tool
refusal does not apply: current `coord/brief-stage2.md` §0 explicitly authorizes
stage-2 delivery of a passing split with no Lean record, and `coord/queue.tsv`
currently lists this node at stage 2. There is no released repair note for this id.

Validation on resumption: `scompile.py` compiled the updated file in sandbox and
library positions cleanly (2.5 s and 2.4 s). The required `deliver2.py --no-push`
then printed OK: preflight and per-file compile passed. The proof remains `sorry`
as required for stage 2.

## Second reading by Q109

Sequential second reading by the same dispatched worker; the explicit dispatcher
instruction prohibits spawning another agent. I reopened the node and completed
file and checked the entire signature independently of the proof sketch. `hreduced`
contains exactly an etale surjective atlas and reduced stalks; `hquasifinite` covers
all etale charts with their structural maps. The conclusion quantifies arbitrary I
and finite-dimensional fields over k. `Sigma.desc` constructs the map from the
scheme disjoint union, and its represented presheaf is on the category over k, so
both the coproduct and its base are correct. I checked specifically that there is
no finite-index or separability requirement and that empty I is permitted. The
presheaf isomorphism is equivalent to the algebraic-space isomorphism because the
relevant categories are full subcategories. No mismatch was found and no
mathematical change to the accepted node was made. No new nodes or dependency
modules are included. The theorem proof is exactly `by sorry`; all variables and
universes are explicitly bound.
