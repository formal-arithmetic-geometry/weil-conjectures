## Worker report

The module `Sheaf.AlgebraicGeometry.LciResidueChartCoverExtension` states
`AlgebraicGeometry.lci_residue_chart_cover_extension`, with one `sorry` and no
new definitions. The node's natural-language statement and dependencies are
unchanged. All variables and universes are bound, with `autoImplicit false`.
The declaration docstring contains all five proof steps and their source nodes.

Hypotheses and objects, matched clause by clause:

- The morphism of schemes is `(X Y : Scheme.{u}) (f : X ⟶ Y)`.
- The affine target open is `(V : Y.Opens)` with the specified affine
  identification `eV : V.toScheme ≅ Spec (.of A)` and `[CommRing A]`.
- The family of affine source opens is `(J : Type w) (U : J → X.Opens)`,
  with rings `B : J → Type u`, commutative-ring instances and
  `eU : ∀ b, (U b).toScheme ≅ Spec (.of (B b))`.
- The induced ring maps `A → B b` are `[∀ b, Algebra A (B b)]`.
  `hchart` says that each restricted morphism is its spectrum map followed
  by `eV.inv` and `V.ι`. This encodes both mapping into V and the actual
  A-algebra structure induced by f; it is not an unrelated algebra structure.
- `hcover : f ⁻¹ᵁ V = ⨆ b, U b` is exactly the covering hypothesis.
- `(p : Ideal A) [p.IsPrime]` gives the chosen prime; `p.ResidueField` is
  Mathlib's canonical κ(p), not an independently chosen field.
- Following the project's FIBRE RING convention, the residue algebra is
  `p.Fiber (B b)`, definitionally `p.ResidueField ⊗[A] B b`.
  This is the source's `B b ⊗[A] p.ResidueField` under the canonical
  `Algebra.TensorProduct.comm A (B b) p.ResidueField`.
  Its default left-factor residue-field action is precisely the transported
  right-factor action in the source. This standard tensor-order convention
  changes neither the algebra nor any hypothesis or conclusion.
- `hfin : ∀ b, Algebra.FiniteType p.ResidueField (p.Fiber (B b))`
  expresses finite type of every residue algebra. The following implication
  assumes `Algebra.IsLocalCompleteIntersection` for every b, explicitly using
  `hfin b` as the proof argument required by that predicate.
- `(K : Type u) [Field K] [Algebra p.ResidueField K]` is any field extension.
  `[Algebra A K] [IsScalarTower A p.ResidueField K]` records the composite
  A → κ(p) → K, not an extra property of the extension: the A-algebra
  structure is uniquely determined by this scalar-tower condition.
- `(t : Spec (.of K) ⟶ Y)` and `ht` identify t with the spectrum of this
  composite ring map followed by the affine identification and inclusion.
- `pullback f t`, `pullback.fst f t` and `pullback.snd f t` are respectively
  X_K, π and its K-structure morphism. There is no flatness, presentation,
  condition on other primes, algebraicity, closedness or perfection hypothesis.

Conclusions, matched clause by clause:

- Each W_b is written literally `(pullback.fst f t) ⁻¹ᵁ U b`.
  It is a `Scheme.Opens`, so openness needs no separate assertion.
  `(⨆ b, (pullback.fst f t) ⁻¹ᵁ U b) = ⊤` asserts these opens cover X_K.
- `LocallyOfFiniteType (pullback.snd f t)` is the stated local finite type
  over K. No quasi-compactness or global finite type is asserted.
- For every b, the existential `hfinK : Algebra.FiniteType K (B b ⊗[A] K)`
  and the following `Algebra.IsLocalCompleteIntersection K ... hfinK`
  assert exactly finite type and local complete intersection for the extended
  chart algebra. The two `letI` binders supply real right-factor algebra
  structures via `Algebra.TensorProduct.rightAlgebra`, acting by z ↦ 1 ⊗ z.
  They are instance definitions, not opaque ordinary `let` abbreviations.
- `e₁ : W_b.toScheme ≅ Spec (.of (B b ⊗[A] K))` is the first chart.
  Its first equation identifies its map to the original affine chart with
  `Spec` of `includeLeftRingHom`, c ↦ c ⊗ 1, after the chosen affine
  identification. The equation is written after composition with the open
  inclusion into X; that inclusion is a monomorphism, so it equivalently
  identifies the maps to U_b itself.
- The next equation identifies e₁'s map to Spec K with `Spec` of
  `includeRight.toRingHom`, z ↦ 1 ⊗ z. Thus e₁ is over K.
- The K-algebra equivalence
  `E : (p.Fiber (B b) ⊗[p.ResidueField] K) ≃ₐ[K] (B b ⊗[A] K)`
  has formula `E ((a ⊗ c) ⊗ z) = c ⊗ ((algebraMap _ _ a) * z)`
  and inverse formula `E.symm (c ⊗ z) = (1 ⊗ c) ⊗ z`.
  After the canonical inner tensor symmetry, these are verbatim the source's
  `(c ⊗ a) ⊗ z ↦ c ⊗ az` and `c ⊗ z ↦ (c ⊗ 1) ⊗ z`.
- `e₂ : W_b.toScheme ≅ Spec (.of (p.Fiber (B b) ⊗[p.ResidueField] K))`
  is the other displayed identification.
  `e₂.hom = e₁.hom ≫ Spec.map (CommRingCat.ofHom E.toRingHom)`
  says it is induced by exactly this algebra equivalence, not an arbitrary
  isomorphism. Its final projection equation also states explicitly that
  e₂ is over K. The two charts therefore give the displayed chain of
  isomorphisms of K-schemes.
- The covering equation together with e₁, hfinK and its lci assertion is
  exactly an affine open cover by spectra of lci K-algebras; no second
  abstract cover or unconnected existence assertion is substituted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`;
  existence for schemes is supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`.
  The Fiber import publicly exposes the residue-field interface.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (the node's recorded
  declaration) and its algebra-instance formulation `Algebra.FiniteType`.
  `RingHom.finiteType_algebraMap` identifies these for the structure maps.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsGlobalCompleteIntersection`, `Algebra.IsLocalCompleteIntersection`.
  The latter is used directly, including its finite-type instance parameter.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- Proof-only import `Sheaf.RingTheory.LocalCompleteIntersectionFieldChange`:
  `Algebra.isLocalCompleteIntersection_fieldChange`.
- Other proof dependencies are already in the public Pullbacks import:
  `AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion`,
  `AlgebraicGeometry.Scheme.Pullback.range_map`,
  `AlgebraicGeometry.pullbackSpecIso` and its projection lemmas.
  No dependency interfaces required repair, and no import is omitted for a cycle.

Edge cases checked mathematically before drafting:

- Empty J is allowed (`J : Type w`, no `Nonempty` assumption). hcover then
  makes f⁻¹(V) empty and hence X_K empty; the conclusion is the empty cover,
  local finite type of the empty morphism and a vacuous per-chart assertion.
- Empty fibres with nonempty J also work; all resulting spectra may be empty.
- Every B b may be the zero ring. There is no `Nontrivial` assumption on
  B b or its tensors. A zero residue algebra has zero scalar extension,
  and the dependency's zero-ring convention makes it a complete intersection.
- V may be empty only if A is zero, but then there is no prime p. This is
  already excluded by choosing a prime, exactly as in the node, not by a
  newly added nonemptiness assumption.
- K may equal κ(p), or be any transcendental, inseparable or nonclosed
  extension; only a field algebra structure is used. No characteristic is fixed.
- The cover index universe w is independent of the scheme universe u and
  need not be finite or small relative to the schemes. The schemes, affine
  rings and extension field use Mathlib's common scheme universe convention.

Searches made (2026-10-24):

- `msearch.py` LeanFinder: “Residue fibre affine charts cover a scheme fibre
  after any extension of its residue field, with tensor product charts and
  local complete intersection rings”. Eight hits, including
  `Scheme.Hom.fiberOverSpecResidueField`, `Scheme.Hom.fiberToSpecResidueField`
  and residue-field preimmersion instances; none states this chart/lci theorem.
- `msearch.py` Loogle: `"pullbackSpecIso", "TensorProduct"`: zero hits.
- `msearch.py` grep: `IsLocalCompleteIntersection|residue.*chart` in
  AlgebraicGeometry: zero hits.
- `msearch.py` LeanSearch: “An affine cover of the inverse image of an affine
  neighbourhood gives tensor product affine charts on a field valued fibre,
  preserving local complete intersections”. Eight hits: affine covers and
  local ring-hom property criteria, no combined tensor/lci chart assertion.
- `msearch.py` grep: `IsLocalCompleteIntersection|complete.intersection` in
  RingTheory: only the comment in Extension/Presentation/Basic.lean:103,
  read and found not to be a theorem.
- Project `rg` for `residue.*[Cc]hart|[Cc]hart.*[Ee]xtension` and this
  node id in both `lean/WeilConjectures` and `lean/Sheaf` finds no exact
  declaration. The complete-intersection definition and field-change modules
  were read in full and reused. The proposed full theorem name was also
  checked in those two source trees and `dag/lean_names_upstream.json`:
  no collision.
- Sources read: Stacks schemes.tex, lemma-fibre-product-affine-schemes
  (01I4) and lemma-open-fibre-product (01JR), and algebra.tex,
  lemma-lci-field-change (00SJ), together with the assigned five-step proof.
  The current blueprint is the `latest` snapshot (2026-10-24); its trace
  chapter uses contracting correspondences, as the accepted split already
  records. This delivery supplies the assigned unchanged auxiliary lemma.

No statement dispute, correction, new nodes or dependency modules.

Validation: the prescribed `scompile.py` checked both the sandbox module and
its library module name. After wrapping the one long docstring line and
adding `autoImplicit false`, the prescribed `deliver2.py --no-push` passed
preflight and clean compilation (2026-10-24). The local node comparison
confirms that only `lean` differs; its recorded signature is verbatim from
the module. The delivery contains exactly this module, its node and this report.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
