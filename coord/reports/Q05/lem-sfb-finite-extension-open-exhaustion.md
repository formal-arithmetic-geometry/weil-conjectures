## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteExtensionOpenExhaustion` states
`AlgebraicGeometry.exists_finiteExtension_open_eq_top`. Its sole theorem has proof `sorry`;
no definition or auxiliary theorem is added. I read Milne, Algebraic Groups, iAG2017,
Appendix B Lemma B.36, printed p.604 (PDF p.616), and the adjacent B.37 Step 1 on p.605.
The declaration docstring gives all six steps of the node's alternative proof, explicitly
identified as that alternative rather than Milne's dimension-decrease proof.

Every hypothesis and clause corresponds as follows:

- The field k is `(k : Type u) [Field k]`. The fixed algebraic closure is
  `(Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]`.
- The k-scheme is `(Z : Scheme.{u}) (f : Z ⟶ Spec (CommRingCat.of k))`.
  Its finite-type hypothesis is exactly `[LocallyOfFiniteType f] [QuasiCompact f]`,
  the recorded definition of finite type, with no separatedness hypothesis.
- The finite intermediate extensions are the subtype
  `{K : IntermediateField k Ω // FiniteDimensional k K}`. Both the family and all its
  hypotheses quantify over precisely this subtype. The proof component of the subtype
  means finite dimension, without imposing separability or normality.
- `U K` is an element of
  `(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K.val)))).Opens`.
  Thus its ambient scheme is the node's `Z_K = Z ×_k Spec K`, in that factor order.
- `hpoints` quantifies over the recorded `fieldPoints K.val` of the second pullback
  projection, so these are K-rational points of Z_K. The membership
  `p.val.base default ∈ U K` says their underlying image is contained in the open.
  Spec K has one point, so testing `default` tests the whole image of the section.
- `hmono` quantifies over every pair K, L and inclusion `h : K.val ≤ L.val`.
  `IntermediateField.inclusion h` gives the canonical k-algebra embedding K into L.
  `Spec.map` makes it a morphism Spec L → Spec K over Spec k; `Over.homMk`
  packages that morphism, and the recorded `baseChangeMap f` gives Z_L → Z_K.
  The open inverse image `... ⁻¹ᵁ U K ≤ U L` is exactly the node's compatibility.
  The small proof in the argument to `Over.homMk` checks only the defining commuting
  triangle using Spec functoriality and definitional equality of the inclusion; it
  proves no part of the exhaustion theorem and introduces no new construction.
- The conclusion `∃ K : {K : IntermediateField k Ω // FiniteDimensional k K}, U K = ⊤`
  is precisely equality with the whole scheme at some finite intermediate extension.
- There are no perfectness, separability, smoothness or reducedness assumptions.
  The arbitrary common universe u is the usual universe for schemes and their base
  fields; no extra relation between independent site universes is involved.

Dependency declarations used (I read their source signatures and docstrings):

- `Field` from `Mathlib.Algebra.Field.Defs`, available through the public dependencies.
- `IsAlgClosure` from `Mathlib.FieldTheory.IsAlgClosed.Basic`, the recorded interface
  for an arbitrary chosen algebraic closure, rather than restricting to one concrete model.
- `AlgebraicGeometry.Scheme`, `Scheme.Opens`, `Spec` and `Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` supplies the recorded
  base-change convention: `Limits.pullback f T.hom`, and
  `AlgebraicGeometry.baseChangeMap` (defined in the publicly imported PicardFunctor).
  Its full signature is the canonical map for `φ : T' ⟶ T` in `Over S`.
- `WeilConjectures.AlgebraicGeometry.DensePoints` is the rational-point dependency
  module. Its recorded `Scheme.Hom.baseChangeFieldPoint` docstring specifies that a
  rational point is an element of `Scheme.Hom.fieldPoints`, a section of the structural
  map. The statement uses that existing point type for the base-changed scheme, rather
  than defining rational points again. No smoothness assumption from other results in
  that module is transferred to this theorem.
- `IntermediateField.inclusion` from `Mathlib.FieldTheory.IntermediateField.Basic`
  supplies inclusions as k-algebra maps. Finite-dimensionality is Mathlib's existing
  vector-space finiteness predicate.

Proof dependencies are retained as imports: the finite-type and Jacobson results in
FiniteType; the closed-point residue-field result in AlgClosed.Basic; the algebraic
adjoin finiteness result in IntermediateField.Adjoin.Basic; `CompactSpace` in
Topology.Defs.Filter; pullbacks in Limits.Shapes.Pullback.HasPullback; field-spectrum
surjectivity in Morphisms.UnderlyingMap; and surjective base change in PullbackCarrier.
The statement dependencies are public imports; the additional proof imports are plain.

Edge cases checked before writing:

- Z empty: each open is top, and the bottom intermediate field represents k itself,
  so the existential is not an empty-index assertion. The proof docstring treats the
  empty finite subcover explicitly.
- k algebraically closed: all finite intermediate fields are the base field; all closed
  points are rational and force the open complement to be empty by the Jacobson property.
- Imperfect k and purely inseparable finite intermediate fields are included in the
  index. No separability or normality is inferred from `FiniteDimensional`.
- Nonreduced schemes and positive-dimensional affine schemes satisfy the same statement;
  the hypotheses do not reduce to density alone, since they apply after every finite extension.
- Equality inclusions K ≤ K are included; compatibility gives the expected identity case.

Searches actually run with `msearch.py Q05 lem-sfb-finite-extension-open-exhaustion`:

- leanfinder: `Compatible opens containing rational points over finite intermediate field
  extensions exhaust a finite type scheme` — eight hits, including finiteSubcover,
  directedCover and compact affine unions, none stating exhaustion under field extension.
- loogle: `AlgebraicGeometry.Scheme, IsOpen, FiniteDimensional` — zero hits.
- grep in Mathlib/AlgebraicGeometry: `finite.*extension.*open|rational.*point.*open|open.*rational.*point`
  — zero hits.
- leansearch: `Compatible open subsets containing all rational points exhaust a finite type
  scheme after finite field extension` — eight hits for opens, affine covers and compact
  unions; no match for this theorem.
- `rg` of the same expression in `lean/WeilConjectures` and `lean/Sheaf` returned unrelated
  rational-point, open-complement, finite-etale and extension-by-zero declarations, none
  with this compatible-family statement. Searching the node id in WeilConjectures found
  no declaration. A name search for `exists_finiteExtension_open_eq_top` and
  `FiniteExtensionOpenExhaustion` in both roots and `dag/lean_names_upstream.json` found none.

No statement correction, dependency repair, new node, or disputed mathematical clause
was needed. The node copy differs only in its `lean` field. All writes are in the assigned
sandbox. Server compilation via scompile.py passed; the final delivery checks are run below.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
