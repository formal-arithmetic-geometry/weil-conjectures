## Worker report

The module `Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth` states
`AlgebraicGeometry.smooth_and_geometricallyReduced_of_geonormal_dim_le_one`, with its entire
proof left as `sorry`. It introduces no definitions. The node is unchanged except for `lean`.

Clause-by-clause correspondence:

- The base field is `(k : Type u) [Field k]`.
- The scheme over that field is `(Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of k))]`.
  Its structure morphism is `Z ↘ Spec (CommRingCat.of k)`.
- Finite type means the two instance hypotheses `LocallyOfFiniteType` and `QuasiCompact`
  on precisely that structure morphism; no separatedness is imposed.
- Dimension at most one is `hdim : topologicalKrullDim Z ≤ 1`.
- Geometric normality is `hnormal`: for every `(L : Type u) [Field L] [Algebra k L]`
  and every point `x` of `pullback` of the structure morphism along
  `Spec.map (CommRingCat.ofHom (algebraMap k L))`, its stalk satisfies
  `IsDomain ... ∧ IsIntegrallyClosed ...`. This is exactly the node's explicit
  local-ring definition, using the recorded inline normal-domain form, without
  a second predicate for geometric normality.
- Smoothness is the first conjunct `Smooth` of the same structure morphism.
- Geometric reducedness is the second conjunct `GeometricallyReduced` of that morphism.
  Mathlib's `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` identifies this
  with reducedness of precisely these field base changes.
- The last conjunct quantifies over the same field extensions, and concludes
  `IrreducibleSpace` of the same pullback from `ConnectedSpace` of that pullback.
  `ConnectedSpace` already includes `Nonempty`, so both words of the node's antecedent
  are present. The explicit `↥` selects the underlying point space rather than a
  pullback in the category of types.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms
  (def-pc-scheme). The conventions node is bookkeeping and has no module or declaration.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`, as the
  conventions node's cited finite-type node records.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`
  (def-kun-topological-krull-dimension).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, and
  `Mathlib.Algebra.Ring.Defs`: `IsDomain` (def-weil-pbc-normal-ring, domain clause).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` (def-pc-fibre-product), with scheme pullbacks
  available through the geometrically reduced import.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.AlgebraicGeometry.Geometrically.Reduced`:
  `AlgebraicGeometry.GeometricallyReduced` (the reduced clause of
  def-pc-geometrically-irreducible; its mathlib_match specifies this declaration).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (def-weil-connected-scheme).
- `Mathlib.Topology.Irreducible`: `IrreducibleSpace` (the irreducibility clause of
  def-weil-irreducible-components, whose match explains `IsIrreducible`).

Proof imports include the recorded
`Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension` and
`WeilConjectures.AlgebraicGeometry.Regular` (the latter carries both
`IsRegular.of_isIntegrallyClosed_stalk` and `IsRegular.isIntegral`), and the Mathlib
Noetherian and discrete valuation ring modules. The geometric-regularity smoothness
criterion proof dependency has no `lean` or `mathlib_match`, hence no available
module to import; it is explicitly cited in the proof docstring for stage 3.
Other Mathlib proof dependencies are available through the imported modules.

The six proof steps of the node are reproduced in the theorem docstring, including
Noetherianity after scalar extension, preservation of the dimension bound, the
field/DVR dichotomy, the geometric regularity criterion, geometric reducedness,
and integrality of connected nonempty regular schemes.

Edge cases checked: the empty scheme has dimension bottom and satisfies geometric
normality vacuously; the first two conclusions hold while `ConnectedSpace` is false.
Dimension zero is included, with regular local rings fields. Disconnected schemes
and disconnected base changes are allowed, and no irreducibility is asserted for
those. Imperfect fields and arbitrary characteristic are allowed: geometric
normality is tested after extensions, not replaced by ordinary normality. All
universe variables are explicitly bound. The field, scheme, and test extensions
share the ambient universe `u`, just as Mathlib's geometric-property interface;
no smaller independent test universe is used, and arbitrary larger data can be
placed in a common ambient universe.

Searches for an existing theorem (msearch.py, group NL, this item):

- LeanFinder: "A geometrically normal finite type scheme of dimension at most one is
  smooth and geometrically reduced": 8 hits, including integral/reduced properties,
  normalization and the chart criterion for smoothness; none states this theorem.
- Loogle: `AlgebraicGeometry.Smooth, IsIntegrallyClosed`: 0 hits.
- Mathlib grep: `geometricallyNormal|geonormal|smooth_of.*normal` in AlgebraicGeometry:
  0 hits.
- LeanSearch: "A geometrically normal finite type scheme of dimension at most one is
  smooth": service unavailable (Internal Server Error); no verdict drawn from it.
- `rg` with `geonormal|geometricallyNormal|smooth_of.*normal` and the item id in
  upstream `WeilConjectures` and side `lean/Sheaf`: the only result was the ring
  theorem `isNormal_tensorProduct_of_geometricallyNormal` in
  `Sheaf.RingTheory.GeometricallyNormalTensorNormal`, which concerns tensor products
  of rings and is not this scheme theorem. No item-id attachment was found.
- `rg` for the proposed declaration name and geometric-normality names in
  `dag/lean_names_upstream.json`: no match.

Sources opened locally: Stacks properties.tex, lemma-normal-dimension-1-regular
(Tag 0BX2); varieties.tex, lemma-geometrically-regular-smooth (Tag 038X), and
lemma-dim-1-projective-completion-after-insep (Tag 0GK5), including its proof.
The source's use of normal implies regular in dimension at most one and then
geometrically regular implies smooth agrees with this statement. No node faults
or statement disputes found.


## Second reading by NL

Independently opened the node, its six proof steps, the delivered module, every
statement dependency record and the actual dependency declarations. No mathematical
mismatch found; the Lean and node are unchanged. This reading adds only this report.
There are no new definition nodes, dependency modules, or statement corrections.

Object/hypothesis/conclusion checklist (all pass):

- Field k: `(k : Type u) [Field k]`. Mathlib Field extends a commutative ring and
  a division ring, including nontriviality. No characteristic restriction.
- Finite type k-scheme Z: `(Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of k))]`,
  with `LocallyOfFiniteType` and `QuasiCompact` on `Z ↘ Spec (CommRingCat.of k)`.
  These are exactly the finite-type convention's two conditions, with no extra
  separatedness, projectivity, integrality, or connectedness instance.
- Dimension at most one: `(hdim : topologicalKrullDim Z ≤ 1)`. The recorded
  topologicalKrullDim is the Krull dimension of IrreducibleCloseds; its value
  includes bottom for the empty scheme, not just natural-number dimensions.
- Every extension L/k and its base change: `∀ (L : Type u) [Field L] [Algebra k L]`
  followed by `pullback (Z ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k L)))`. Algebra supplies precisely the
  field homomorphism; the recorded categorical pullback is the scheme fibre
  product, not a product over the terminal scheme or a fibre at a closed point.
- Geometric normality: hnormal quantifies over every point x of each such
  pullback and asserts `IsDomain (...presheaf.stalk x) ∧
  IsIntegrallyClosed (...presheaf.stalk x)`. Read IsDomain and IsIntegrallyClosed
  themselves: the former includes nontriviality, the latter uses FractionRing.
  This uses the normal-domain clause of def-weil-pbc-normal-ring verbatim.
- Smoothness: first conjunct `Smooth (Z ↘ Spec (CommRingCat.of k))`. Read its
  affine-local smooth-ring-map definition; this is the dependency's smooth
  morphism, without a relative dimension fixed to one.
- Geometric reducedness: second conjunct `GeometricallyReduced` of the same
  structure morphism. Its field is `geometrically IsReduced f`; opened
  geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms, which gives exactly
  reducedness of these chosen pullbacks for every field algebra over k.
- Final conclusion: for every L/k as above, `ConnectedSpace` of that pullback
  implies `IrreducibleSpace` of the identical pullback. ConnectedSpace extends
  PreconnectedSpace and explicitly includes Nonempty; IrreducibleSpace likewise
  includes Nonempty. Thus the node's connected AND nonempty antecedent is exact.
  The universal quantifier occurs after the first two conclusions, as required.

Source check: opened properties.tex lemma-normal-dimension-1-regular (0BX2),
lemma-normal-Noetherian (033M), lemma-normal-locally-Noetherian (033N), and
varieties.tex lemma-geometrically-regular-smooth (038X), including its proof,
and lemma-dim-1-projective-completion-after-insep (0GK5), including its proof.
0BX2 requires locally Noetherian, normal and dimension at most one; finite type
supplies Noetherianity here after every field extension. 038X requires only
locally finite type over a field. The surrounding completion theorem assumes
separatedness/projectivity for completion, but its normal-to-regular-to-smooth
argument does not use those assumptions. 033M/033N justify the final connected
normal/regular assertion. The delivered docstring preserves all six node steps,
including the dimension-zero field case and geometric reducedness. The existing
Regular.of_isIntegrallyClosed_stalk and IsRegular.isIntegral signatures were
opened: their local Noetherian hypotheses are supplied by finite type, not
silently added to this statement. The dimension-preservation import was also
opened. The unstated geometric-regularity criterion has no module to import;
its identifier remains explicitly in proof step 4.

Edge cases: empty Z is allowed (dimension bottom, vacuous normal stalks), with
no final connectedness antecedent; dimension zero and disconnected schemes are
allowed; disconnected base changes give no irreducibility conclusion. Imperfect
fields, inseparable extensions, and every characteristic are allowed. There is
no finite-generation or algebraicity restriction on L. The common universe u is
polymorphic and agrees with Scheme and Mathlib's geometric-property interface;
there is no independent smaller test universe. All parameters are explicitly
bound. There are no definitions, private predicates, local notation or instances,
and the sole proof is sorry. The recorded lean.statement equals the file's
signature verbatim; every Lean line is at most 100 characters.

Independent duplicate searches used alternate wording:

- LeanFinder via msearch: "normal scheme dimension one geometrically regular
  smooth over arbitrary field": eight hits about standard smooth presentations
  and the smooth locus, none this implication.
- Loogle via msearch: `IsIntegrallyClosed, AlgebraicGeometry.Smooth`: zero hits.
- LeanSearch via msearch: "geometrically normal curve is smooth": service
  unavailable (Internal Server Error), recorded without a negative verdict.
- Direct rg in Mathlib AlgebraicGeometry, upstream WeilConjectures and project
  lean/Sheaf for smooth together with geonormal/geometrically normal, and the
  full proposed declaration name: no match. Upstream smooth_of_isRegular was
  opened; it requires PerfectField and is not this arbitrary-field theorem.

Validation: scompile.py is used for the delivered module, with no local compiler
or library build. The delivery dry run rechecks compilation and preflight.
