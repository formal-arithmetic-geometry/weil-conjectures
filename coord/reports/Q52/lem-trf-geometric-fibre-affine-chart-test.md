## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.GeometricFibreAffineChartTest`.
Its only declaration is `AlgebraicGeometry.geometric_fibre_affine_chart_test`, a theorem
with proof `sorry`. No definitions, helper axioms, dependency repairs, new nodes, or
statement corrections are introduced. Only `lean` changes in the item's JSON.

### Hypotheses and objects

- Arbitrary schemes and morphisms: `{X T T' : Scheme.{u}}`, `f : X ⟶ T`,
  `g : T' ⟶ T`. There are no morphism-property instances, in particular no flatness,
  finite type, finite presentation, or nonemptiness assumption.
- The point is `t' : T'`; `t` is written directly as `g t'`. Thus `k` is
  `T.residueField (g t')`, `L` is `T'.residueField t'`, and the required residue-field
  embedding is `(g.residueFieldMap t').hom`.
- `X'` is the existing `pullback f g`, and `f'` is `pullback.snd f g`.
  `Y` is exactly `f.fiber (g t')`, with maps `f.fiberι (g t')` to `X` and
  `f.fiberToSpecResidueField (g t')` to `Spec k`.
- An arbitrary index set is `I : Type v`. The chart rings are `A : I → Type u`,
  `[∀ i, CommRing (A i)]`, and `[∀ i, Algebra k (A i)]`.
  The affine open charts are represented by `ι i : Spec (.of (A i)) ⟶ Y` with
  `[∀ i, IsOpenImmersion (ι i)]`. Their images are the opens `U_i`; using these
  open immersions is equivalent to choosing isomorphisms `U_i ≅ Spec (A i)`.
- `hι` asserts `ι i ≫ f.fiberToSpecResidueField (g t') = Spec.map (ofHom (algebraMap k
  (A i)))`, precisely that these are the given affine charts as *k-schemes*.
- `hcover : ∀ y : Y, ∃ (i : I) (x : Spec (.of (A i))), ι i x = y` says their images
  cover `Y`. No chosen distinguished chart and no `Nonempty I` is required.
- A field extension `H/L` is `[Field H]` and `h : L →+* H`, as permitted by
  `def-pc-field-extension`. Ring homomorphisms between fields are injective.
  `[Algebra k H]` together with `hH : algebraMap k H = h.comp (g.residueFieldMap t').hom`
  specifies *exactly* the composite algebra structure required in the node. This
  equality is not an extra condition on an arbitrary field extension: its composite
  ring map always supplies this algebra by `RingHom.toAlgebra`.
- The point morphism `Spec H ⟶ T'` is literally
  `Spec.map (CommRingCat.ofHom h) ≫ T'.fromSpecResidueField t'`.
  Thus the left-hand iterated pullback is exactly the stated `Z_H`.

All variables and universes are explicitly bound. A common arbitrary universe `u`
contains the schemes and field/rings, as in Mathlib's scheme pullbacks and
`pullbackSpecIso`; any collection here can be placed in such a common universe.
The cover index has independent universe `v`, and no categorical limit indexed by `I`
is requested.

### Every conclusion clause

The conclusion existentially supplies `p : Z_H ⟶ Y` and
`e : Z_H ≅ pullback (f.fiberToSpecResidueField (g t')) (Spec.map (ofHom (algebraMap k H)))`.
The latter target is literally `Y ×_(Spec k) Spec H`.

1. `e.hom ≫ pullback.fst _ _ = p` identifies its first projection.
2. `p ≫ f.fiberι (g t') = pullback.fst _ _ ≫ pullback.fst f g` is compatibility
   with the maps to `X`.
3. `e.hom ≫ pullback.snd _ _ = pullback.snd _ _` is compatibility with `Spec H`.
   These conditions characterize the comparison canonically: maps to the target
   pullback are determined by its projections; maps to `Y = X ×_T Spec k` are
   determined by the map to `X` and the prescribed map to `Spec k`. The latter
   map follows from the pullback condition and the `Spec H` projection. Hence this
   is a projection-characterized isomorphism, not an arbitrary `Nonempty` isomorphism.
4. `∀ i, IsOpenImmersion (pullback.fst p (ι i))` gives the pulled-back open
   subschemes, namely `p⁻¹(U_i)` by the universal property of open base change.
5. `∀ z, ∃ (i : I) (w : ↥(pullback (C := Scheme.{u}) p (ι i))), ... = z`
   states that these opens cover all of `Z_H`.
6. For every `i`, `c : pullback p (ι i) ≅ Spec (.of (A i ⊗[k] H))` identifies
   the inverse image with the claimed spectrum and in particular says it is affine.
   The equation `c.inv ≫ pullback.snd p (ι i) = Spec.map (ofHom includeLeftRingHom)`
   prescribes the projection to `Spec A_i` by `a ↦ a ⊗ 1`.
   The equation `c.inv ≫ pullback.fst p (ι i) ≫ pullback.snd _ _ =
   Spec.map (ofHom includeRight.toRingHom)` prescribes the projection to `Spec H`
   by `h ↦ 1 ⊗ h`. Together these determine the chart isomorphism canonically.
7. The last conjunct is `IsReduced Z_H ↔ ∀ i, _root_.IsReduced (A i ⊗[k] H)`.
   The scheme predicate is the recorded section-wise reducedness predicate,
   equivalent to the local-ring condition; the ring predicate means every nilpotent
   equals zero. These are exactly the node's two reducedness conditions.
8. The rings under `Spec` and in the final predicate use Mathlib's standard
   `Algebra.TensorProduct` commutative-ring structure. Its multiplication is
   `(a ⊗ h) * (b ⊗ j) = (a*b) ⊗ (h*j)` by `Algebra.TensorProduct.tmul_mul_tmul`,
   and `includeLeftRingHom` and `includeRight` have the pure-tensor formulas above.
   This is the node's specified multiplication, not an unspecified ring structure.

### Dependency declarations read and used

Every statement dependency's node, recorded declaration, signature and docstring were read.

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom` (`X ⟶ T`).
- `def-pc-base-change`: recorded module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, publicly imported.
  Its documented scheme convention is `pullback f g` with `pullback.snd` as
  structure map; `Scheme.Modules.moduleBaseChange` is its module-only clause,
  not an alternative definition of the base-changed scheme. Read its full module.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`, `Scheme.Hom.fiber`,
  `Scheme.Hom.fiberι`, `Scheme.Hom.fiberToSpecResidueField`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`;
  the permitted equivalent ring-homomorphism description represents `H/L`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `IsReduced`.
- `def-weil-pbc-module-tensor-product`: its `mathlib_match` is `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; no `lean` repair is needed.

The proof-only dependencies all have usable Mathlib matches, also read: 
`isPullback_fiberToSpecResidueField_of_isPullback` (Fiber), `IsPullback.paste_vert_iff`
(Pullback.IsPullback.Basic), `Scheme.pullback_map_isOpenImmersion` (Pullbacks),
`Scheme.Pullback.range_map` (PullbackCarrier), `pullbackSpecIso` and its inverse
projection formulas (Pullbacks), `Algebra.TensorProduct.instCommRing`,
`tmul_mul_tmul`, `includeLeft`, `includeRight`, `productMap`, and `ext`
(RingTheory.TensorProduct.Basic/Maps), `IsReduced.iff_of_openCover` and
`affine_isReduced_iff` (Properties). `Mathlib.RingTheory.TensorProduct.Maps` is
plain-imported for the proof; the other proof modules are already public statement
imports or their transitive imports. No proof-dependency import is omitted for a cycle.
The theorem docstring gives all four DAG proof steps with their node names.

### Sources and edge cases

Read local Stacks `more-morphisms.tex`, lemma-base-change-fibres-geometrically-reduced
(Tag 0576), including its first proof sentence; and `schemes.tex`,
lemma-fibre-product-affine-schemes (01I4), lemma-open-fibre-product (01JR),
lemma-reduced (01J1), and lemma-affine-reduced (01J2). These support exactly the
fibre comparison, open base change, tensor spectra, and reducedness test.
The item's blueprint is a proof refinement, not a unit's own statement; its source
calculation is valid as written. There are no node faults or disputed statements.

Checked before writing: `I = ∅` forces `Y` empty from `hcover`; the morphism to `Y`
forces `Z_H` empty, so the open-cover and reducedness clauses are vacuous in the
required way. Individual empty charts give the zero ring; tensoring it remains the
zero ring, which is reduced. Repeated charts and infinite index sets are permitted.
An identity base change and `H = L` with the identity embedding are allowed. Fields
of positive characteristic, transcendental field extensions and nonreduced original
chart rings are allowed. No reducedness of `A i`, algebraic closedness of `H`, or
geometric reducedness is assumed. No flatness of `f` or `g` is used or stipulated.

### Searches

The prescribed `msearch.py Q52 lem-trf-geometric-fibre-affine-chart-test` calls were:

- `leanfinder`: "A scheme fibre after arbitrary base change has affine charts Spec of
  the original fibre chart tensor the new field and is reduced if and only if all
  those tensor rings are reduced". Eight hits, including `affine_isReduced_iff`,
  `Algebra.isGeometricallyReduced_iff` and algebraic tensor reducedness instances.
  These give only the separate subclaims, not the full comparison/chart statement.
- `loogle`: `AlgebraicGeometry.IsReduced, CategoryTheory.Limits.pullback`.
  Two hits: reduced pullback instances assuming geometrically reduced, flat and
  locally noetherian hypotheses. Those hypotheses are absent from this item.
- `grep` in Mathlib `AlgebraicGeometry`:
  `fiber.*(baseChange|pullback)|pullbackSpecIso|iff_of_openCover`.
  Twenty-five displayed hits, including `IsReduced.iff_of_openCover` and usages of
  `pullbackSpecIso`. Direct reads of Fiber, Pullbacks, PullbackCarrier and Properties
  found the elementary interfaces listed above; none is the assembled statement.

Also ran direct `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
`geometric.*[Ff]ibre.*[Cc]hart|geometric.*[Ff]iber.*[Cc]hart|fibreScalarAlgebra`.
Hits concern finite geometric points, finite-presentation charts, and unrelated
nodal/regular group-space chart conditions, not this arbitrary-H reducedness test.
The item ID has no source match under `lean/WeilConjectures`.
A search for the proposed full theorem name in `lean` and `dag/lean_names_upstream.json`
returned no match. No duplicate definition is needed.
Search wrapper output is retained in the sandbox's `searches.jsonl`.

### Validation

`scompile.py Q52 lem-trf-geometric-fibre-affine-chart-test` compiled the delivered
file cleanly in sandbox mode (2.1 seconds) and actual library-module mode
(2.3 seconds). The only initial elaboration issue was Lean selecting the category of
Types for a point binder written `w : pullback p (ι i)`; writing
`w : ↥(pullback (C := Scheme.{u}) p (ι i))` resolved that ambiguity without changing
the mathematical statement. There are no diagnostic commands or additional proofs.

## Second reading by Q52

This is the dispatcher's single-worker rereading, not a claim of an independent
second agent; the brief prohibits starting agents and assigns the independent review
to the maintainer. Reopened the node and delivered file together. Checked all binders
against the statement: the residue map is specifically `g.residueFieldMap t'`,
`hι` preserves the *given* k-algebra structures, and `hH` fixes the composite on H.
In particular the field extension is arbitrary, rather than an algebraic closure or
a separately chosen unrelated k-structure.

Checked the three comparison equations: the equation to X includes both projections
through `X'`, and the equation to H is the second projection of the actual iterated
pullback. The charts are `pullback p (ι i)` with their first projection to `Z_H`;
their second projection is to `Spec A_i`. Thus `includeLeftRingHom` belongs in the
second-projection equation, while `includeRight` belongs in the composite to H.
The orientations of both equations use `c.inv : Spec (A_i ⊗ H) ⟶ pullback p (ι i)`,
so the displayed ring maps have exactly the required directions.

Checked covering and reducedness separately: coverage is asserted on every point
of `Z_H`; each chart is affine because of its spectrum isomorphism; the final
biconditional uses scheme reducedness on the left and ring reducedness on the right.
The empty cover has no implicit nonemptiness constraint. No mismatch requiring a
node correction was found. The point-binder elaboration repair above was the only
code change on rereading. All four original proof steps are present in the docstring.
