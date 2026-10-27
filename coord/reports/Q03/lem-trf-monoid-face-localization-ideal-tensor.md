## Worker report

The module `Sheaf.RingTheory.MonoidFaceLocalizationIdealTensor` states
`MonoidAlgebra.FaceIdealTensor.face_localization_ideal_tensor`, with exactly one
postponed theorem, whose entire proof is `sorry`. Its docstring records all eight
proof steps of the DAG node. All supporting definitions have real data. No
statement correction is needed.

The node uses additive notation; the module uses the already published
multiplicative convention for `Algebra.faceLocalization`. Thus `1`, `p * q`, and
`GrothendieckGroup.of p * (GrothendieckGroup.of f)⁻¹` represent `0`, `p + q`, and
`p - f`. This is notation for the same commutative monoids, not an extra algebraic
hypothesis. The bound universes `u`, `v`, and `w` independently accommodate the
monoid, coefficient ring, and new coefficient ring. `autoImplicit` is false.

Hypotheses and constructions, clause by clause:

- Integral commutative monoid: `{P : Type u} [CommMonoid P]` and
  `hP : Function.Injective (GrothendieckGroup.of : P →* GrothendieckGroup P)`.
  No finite generation, saturation, sharpness, or torsion-free-group condition is
  imposed.
- Face: `F : Submonoid P` supplies the identity and closure under products;
  `hF : ∀ p q : P, p * q ∈ F → p ∈ F ∧ q ∈ F` is exactly the face condition.
- Coefficient ring and chart: `{A : Type v} [CommRing A] (α : P →* A)`.
  `hα : ∀ f : F, IsUnit (α f.1)` expresses that the face maps to units, including
  in the zero ring.
- `P_F` is the existing `Algebra.faceLocalization P F`, the submonoid of the
  Grothendieck group consisting of these fractions. `fraction F p f` merely
  packages the displayed fraction as a subtype element using its explicit witness.
  The inclusion is the existing `MonoidAlgebra.toricLocalizationInclusion F`.
- The theorem supplies `αF : faceLocalization P F →* A`, its equality with `α`
  after composition with the inclusion, and the equation
  `αF (fraction F p f) = α p * (↑((hα f).unit⁻¹) : A)` for every representative.
  These equations uniquely determine the extension, so this is the localization
  chart and cannot be an arbitrary coefficient map.
- A monoid ideal is `H : Set P` with `∀ h ∈ H, ∀ p : P, h * p ∈ H`.
  `localizedIdeal F H` is exactly the set of `fraction F h f` with `h ∈ H`.
  The first ideal conclusion explicitly asserts its stability under multiplication
  by every element of `P_F`.
- The integer monoid algebra is Mathlib's `MonoidAlgebra ℤ P`, whose underlying
  finite coefficient sums have the specified monomial product. The reused
  `LogChartFaceTor.ideal H` is `Ideal.span {z | ∃ h ∈ H, z = single h 1}`.
  For stable `H` this is precisely the finite sums supported in `H`, by
  `MonoidAlgebra.mem_ideal_span_of_image` (read in Mathlib's Ideal module).
  Thus it is the node's `Z[H]`, including the empty ideal. The analogous ideal in
  the fraction monoid algebra is `LogChartFaceTor.ideal (localizedIdeal F H)`.
- Ideal extension is rendered by `.map (MonoidAlgebra.mapDomainRingHom ℤ
  (MonoidAlgebra.toricLocalizationInclusion F))`; the second ideal conclusion
  equates it to the monomial ideal on `H_F`.
- `tensor α H` is an abbreviation for the actual Mathlib module tensor
  `LogChartFaceTor.ideal H ⊗[MonoidAlgebra ℤ P] A`, using the algebra structure
  `(MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra`. This is the same restriction
  of scalars as the recorded chart coefficient module; it permits independent
  universes for `P` and `A`, rather than using that helper's common-universe
  `ModuleCat` packaging. No tensor quotient or coefficient action is copied.
- `tensorModule α H` transfers the standard `A`-module structure on the swapped
  tensor `A ⊗ Z[H]` back through `TensorProduct.comm`, via `AddEquiv.module`.
  Thus its action on `z ⊗ a` is `z ⊗ (c*a)`, on the coefficient factor. The
  statement retains the node's tensor order. `pure α H z a` is precisely this
  actual pure tensor with the chart action explicit.
- The asserted `e : tensor α H ≃ₗ[A] tensor αF (localizedIdeal F H)` is the
  required A-linear isomorphism. `IsComparison` first requires
  `e (pure α H z a) = pure αF (localizedIdeal F H) zF a` whenever `z` and `zF`
  are the monomials of the same `h ∈ H` under the inclusion.
- The second conjunct of `IsComparison` requires, for EVERY `h ∈ H` and `f : F`,
  `e.symm (pure αF (localizedIdeal F H) zF a) =
  pure α H z ((↑((hα f).unit⁻¹) : A) * a)` when `zF` is the monomial of `h/f`.
  Requiring this for every representative enforces representative independence.
  Unit extraction gives the inverse of the specified chart value, not a chosen
  unrelated invertible scalar.
- Both multiplication maps are the concrete `multiplication` definitions. Each
  is the ideal subtype followed by the chart evaluation linear map, lifted by
  `LinearMap.liftBaseChange A` and precomposed with the A-linear transported tensor
  swap. Hence on `z ⊗ a` it evaluates to `a * α(z)`, equal by commutativity to
  the node's `α(z) * a`. In particular its monomial values are `α(h)a` and
  `αF(h/f)a`. The last conjunct of `IsComparison` is
  `∀ x, multiplication αF (localizedIdeal F H) (e x) = multiplication α H x`.
  This is the multiplication square with identity on `A`.
- For every `(A' : Type w) [CommRing A'] (φ : A →+* A')`, the new charts are
  explicitly `φ.toMonoidHom.comp α` and `φ.toMonoidHom.comp αF`. The theorem
  supplies `e'` with the same `IsComparison` formulas, using the mapped unit
  proofs `(hα f).map φ`. The additive coefficient maps `c` and `cF` are specified
  on EVERY pure tensor `z ⊗ a` by `z ⊗ φ(a)`. These formulas uniquely determine
  the canonical coefficient maps by tensor generation. They are not extra
  hypotheses or arbitrary unconstrained maps. Both naturality squares are present:
  `∀ x, cF (e x) = e' (c x)` and
  `∀ y, c (e.symm y) = e'.symm (cF y)`.

Dependencies read and reused:

- `def-weil-pbc-module-tensor-product` is a Mathlib leaf: `TensorProduct` and
  `TensorProduct.mk` in `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  `TensorProduct.lift`, `lift.tmul`, and `ext'` in `.Basic`, and
  `LinearMap.rTensor` in `.Map`. Their definitions, signatures and adjacent
  docstrings were opened. They supply the actual tensor and its universal property.
- `def-trf-monomial-quotient-tor` records
  `AlgebraicGeometry.LogChartFaceTor.ideal`, `.coefficients`, and `.tor` in
  `Sheaf.TraceFormula.LogChartFaceTorComparison`. The full source was read.
  This delivery reuses `.ideal`; its coefficient action uses the same monoid
  algebra lift directly. It does not assume the log-geometric theorem in that
  module, nor any fs or strictly henselian hypothesis.
- `def-trf-monoid-face-localization`, added in this repair with an `existing: true`
  record, owns `Algebra.faceLocalization` in `Sheaf.TraceFormula.FaceLocalizationFs`.
  Its full construction was read. Only the general definition is used; the
  fine-saturated theorem is not a dependency.
- `def-trf-monoid-face-localization-inclusion`, added in this repair with an
  `existing: true` record on `Sheaf.RingTheory.AffineToricEquivariantIdeals`, owns
  `MonoidAlgebra.toricLocalizationInclusion`. Its full definition and docstring
  were read. The definition has no field, finiteness, or fs hypothesis; none is
  imported into the statement. The field-specific toric ideal is NOT used for
  the integer coefficient ring.
- Additional Mathlib constructions: `AddEquiv.module` and `.linearEquiv` in
  `Mathlib.Algebra.Module.TransferInstance`, `TensorProduct.comm`,
  `LinearMap.liftBaseChange` in `Mathlib.RingTheory.TensorProduct.Basic`, and
  `MonoidAlgebra.lift` / `mapDomainRingHom` in the monoid algebra modules. Their
  defining source was read. These supply concrete data without postponed proofs.

The item cites the published definition node `def-trf-monomial-quotient-tor` and
these two new definition nodes in `stmt_deps`. The theorem nodes
`lem-trf-face-localization-fs` and `lem-trf-affine-toric-equivariant-ideals` are
removed from the returned packet's `stmt_deps`: neither conclusion is needed.
Relative to current main the item changes only `lean` and adds these definition
dependencies. All other main-branch fields are retained. All new helper declarations
in the item's module serve the comparison and are listed in `lean.declarations`.
The two new definition nodes record existing data and add no Lean module.
The import of `LogChartFaceTorComparison`
is needed for its existing ideal construction. If the maintainer later adds the
proof import of this lemma to that containing module, that import must be omitted
there by the documented import-cycle rule; downstream files can use this lemma
without an import cycle. This delivery changes no existing module.

Edge cases checked before writing: `H = ∅` gives bottom monomial ideals and zero
tensors; the generator clauses are empty while the actual equivalence and squares
remain asserted. `H = P` gives the full ideal. If `H` meets the face, the localized
ideal is the full ideal, with no cancellation of a nonunit in `A` required.
For `F = {1}` the fractions have denominator 1 and the formulas give identity.
For `F = P`, the hypothesis requires every chart value to be a unit and yields
the group-completion localization. Trivial monoids, torsion in the group
completion, non-finitely-generated monoids, nonreduced coefficient rings, and
zero rings are all admitted. No `Nontrivial`, nonemptiness, domain, flatness,
Noetherian, finiteness or saturation assumption is introduced. Every denominator
scalar that is inverted is already a unit. The injectivity hypothesis is exactly
integrality, not cancellation of arbitrary elements of `A`.

Sources read: ILO PDF physical pp. 104–105 (printed 98–99), especially VIII 3.1.2,
and physical p. 116 (printed 110), proof of 3.4.3 and its monomial ideal tensor
sequence. Also opened the current `literature/blueprint/latest` ancestor
`lem-trf-local-term-locality.md`. The requested old CompactObject example is now
a withdrawn empty module; its node record and the actual current module header
conventions were read, and the new module follows the public module convention.

Searches made:

- `msearch.py ... leanfinder "Tensor product of a monomial ideal with a ring is
  unchanged by monoid face localization when chart values on the face are units"`:
  8 hits, including `IsLocalization.mk'_tmul`, `IsLocalization.tmul_mk'`, and
  polynomial tensor formulas; no exact ideal comparison with all requested maps.
- `msearch.py ... loogle "IsLocalization, TensorProduct"`: 12 hits, including
  `IsLocalization.moduleLid`, `.moduleTensorEquiv`, `.tensor`, `.tensorRight`;
  general localization infrastructure rather than this monomial ideal statement.
- `msearch.py ... leansearch "Face localization gives an isomorphism on tensor
  products of monomial ideals with chart coefficients when face values are units"`:
  8 hits, including `IsLocalization.instIsLocalizedModuleTensorProductMap`,
  `.tensorProduct_tensorProduct`, `.atUnits`; no exact match for this statement.
- `msearch.py ... grep 'MonoidAlgebra.*localiz|localiz.*[Ii]deal|monomialIdeal'
  RingTheory`: 25 hits of general localization and ideal material, no exact match.
- `rg -n 'monomialIdeal|[Ff]ace[Ll]ocal|[Mm]onoid[Ii]deal|[Ii]deal[Tt]ensor|[Mm]onoid.*[Ff]ace'
  lean/Sheaf lean/WeilConjectures`: found the existing fraction localization,
  the chart ideal and tensor helpers, and the field-specific toric construction;
  reused these constructions as described above. The exact blueprint id search
  in `lean/WeilConjectures` found no statement.
- Further `rg` searches for monomial ideal definitions, tensor module actions and
  `mapDomainRingHom` in Mathlib and both project roots located the canonical APIs.
  `MonoidAlgebra.FaceIdealTensor` and `face_localization_ideal_tensor` had no name
  collision. `python3 tools/blueprint_refs.py search 'monoid ideal'` returned no
  blueprint matches. DAG searches located the existing definition owner
  `def-trf-monomial-quotient-tor`, so no replacement ideal definition was written.

Validation: `scompile.py Q03 lem-trf-monoid-face-localization-ideal-tensor
<module>` compiled both the sandbox view and its library module name successfully
(8.9 s and 9.3 s), without errors or unexpected warnings. The file has no line
longer than 100 characters. Only the named main theorem uses `sorry`.


## New nodes

`def-trf-monoid-face-localization` owns the already published
`Algebra.faceLocalization` in `Sheaf.TraceFormula.FaceLocalizationFs`, with
`existing: true`. For every commutative monoid `P` and submonoid `S` it is the
actual submonoid `{i(p)i(s)⁻¹}` of the Grothendieck group. The Lean signature is
copied verbatim through the result type preceding `where`. The carrier has exactly
the two existential fraction witnesses; its identity uses `(1,1)` and multiplication
uses `(pq,st)`. This is the source's localization construction for integral monoids,
and the definition itself is meaningful without integrality. Source: ILO VIII
3.1.2, printed p. 98. The new node assumes neither finiteness nor saturation and
cites no theorem. It adds ownership of existing data, not a duplicate definition.

`def-trf-monoid-face-localization-inclusion` owns the already published
`MonoidAlgebra.toricLocalizationInclusion` in
`Sheaf.RingTheory.AffineToricEquivariantIdeals`, with `existing: true`.
It cites `[def-trf-monoid-face-localization]` and defines `j_S(p)=i(p)` in that
submonoid, with denominator `1` as its actual membership witness. The published
structure's identity and multiplication fields are the corresponding equalities
for `GrothendieckGroup.of`; thus this is precisely `p ↦ p/1` for every monoid,
without introducing a field or fine-monoid hypothesis. Source: ILO VIII 3.1.2,
printed p. 98, and its canonical map used in VIII 3.2.2. Its signature is also
recorded verbatim. No additional Lean module or construction is introduced.

For both new nodes, fresh LeanSearch, LeanFinder, and Mathlib grep searches were
run. Their full tool output is retained verbatim in `mathlib_searches`. LeanSearch
found 8 general quotient-localization hits including `Localization`, `.mk`, and
`.monoidOf`; LeanFinder found 8 hits including `Submonoid.divPairs`,
`Submonoid.isLocalizationMap_of_group`, and `Localization.monoidOf`. Mathlib grep
found only `GrothendieckGroup.of` and `Localization.monoidOf`. Those quotient
constructions do not replace the project's existing literal fraction-submonoid
construction. Source-root grep found no duplicate in `WeilConjectures` and the
exact existing definitions in the two `Sheaf` modules. DAG ownership searches
found no definition node recording either declaration as its primary declaration;
mentions in theorem helper lists and review notes are not definition ownership.
`blueprint_refs.py search 'face localization'` returned 0 matches. The ancestor
command identified `lem-trf-local-term-locality`; both nodes use that ancestor
and the item's original `via` prefixed by this item. Both have the item's chapter
and unit and the complete required definition-node metadata.

## Repair of returned delivery 60731223b912

H2 is repaired by the two new definition ownership nodes above. The two theorem
ids are dropped from the item's `stmt_deps`; the item cites the new definitions
instead. The existing monomial-ideal definition dependency is retained. This is
a substantive DAG repair, not an unchanged re-push. The Lean mathematics, which
the maintainer independently checked correct, is retained exactly. No theorem
statement, helper definition, axiom, universe, or hypothesis is changed.

Compared the retained packet against current main: the original item has no
Lean record and only the tensor-product statement dependency; every other field
is identical to the returned packet. The repaired item is reconstructed from that
current node plus the retained Lean record and the repaired definition dependencies.
The prescribed delivery wrapper fetches current main and rebuilds the commit on
that base. Independent review remains the maintainer's responsibility; no worker
second-reading claim is made here.

Repair validation: the retained Lean module again passes `scompile.py` in sandbox
and library mode. The repaired packet's `deliver2.py --no-push` passed preflight
and compilation at dry-run commit `5ee72d5e06f`; this includes the server's module-mode
`#check` probes for both `existing: true` definition records. Five delivery paths
were staged: the item module, item node, the two new definition nodes, and report.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
