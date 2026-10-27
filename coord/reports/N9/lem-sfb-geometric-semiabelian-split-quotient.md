## Worker report

This delivery states `AlgebraicGeometry.geometric_semiabelian_split_quotient` in
`Sheaf.AlgebraicGeometry.GeometricSemiabelianSplitQuotient`. The sole theorem has a
`sorry` proof. It introduces no definitions, helper axioms, or dependency modules.
The accepted stage-1 split and its nine-step proof are preserved. The earlier worker's
stage-1 live-wins refusal does not apply: the current brief-stage2 §0 explicitly permits
recording an accepted split's Lean statement. The live node had no Lean record and no
released repair note.

Hypothesis and conclusion correspondence:

- Arbitrary field k: `{k : Type u} [Field k]`. There is no perfection or characteristic
  restriction. The universe is explicit and `autoImplicit` is false.
- H/k a group scheme: `H : Grp (Over (Spec (.of k)))`. Its operations are the bundled
  group object's actual operations. Commutativity is `[IsCommMonObj H.X]`.
- Smooth, separated, finite type: `[Smooth H.X.hom]`, `[IsSeparated H.X.hom]`,
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]` respectively.
- Connected after every field extension: `[GeometricallyConnected H.X.hom]`, whose
  definition tests pullbacks to spectra of fields.
- The rank is the same explicitly bound `r : ℕ` throughout, including zero.
- The chosen algebraic closure is Mathlib's `AlgebraicClosure k`, a field with the
  canonical k-algebra and `IsAlgClosure` instances. Scalar extension is the shared
  `MultiplicativeType.baseChange` functor, using `Over.pullback` and the induced group law.
- The geometric extension is `hgeom`: it supplies a group B and group homomorphisms
  `i : splitTorus (AlgebraicClosure k) r ⟶ H_bar` and `p : H_bar ⟶ B`.
  `IsCommMonObj B.X`, `IsProper B.X.hom`, `Smooth B.X.hom`, and
  `GeometricallyConnected B.X.hom` render each property required of B separately.
- Exactness as fppf sheaves: the `IsPullback` square of i and the terminal morphism
  against p and `η[B.X]` identifies the entire scheme-theoretic kernel with the split
  torus, including its inclusion and group law. `Presheaf.IsLocallySurjective
  (Scheme.fppfTopology.over ...) (yoneda.map p.hom.hom)` states fppf local lifting of
  every section. Representable scheme functors are fppf sheaves; therefore these are
  exactly monicity, kernel exactness, and sheaf epimorphy of the stated sequence.
- Finite Galois K/k: the conclusion existentially supplies `K : Type u`, `Field K`,
  and `Algebra k K`, followed by `FiniteDimensional k K ∧ IsGalois k K`.
  Mathlib defines `IsGalois` as separable and normal; finite dimensionality is the
  additional finiteness condition required here. This does not assert an abelian
  Galois group, nor that the original extension of groups splits.
- A/K an abelian variety: `A : Grp (Over (Spec (.of K)))` with
  `IsAbelianVariety A.X`, the recorded definition of proper, smooth, connected group.
- Smooth surjective homomorphism q: the bundled group morphism q has source the
  actual base change of H and target A; `Smooth q.hom.hom.left` and
  `Surjective q.hom.hom.left` are its scheme properties.
- Identification of the kernel with the rank-r split torus: the supplied group map i
  and its `IsPullback` square with q and `η[A.X]`. The square is in `Over (Spec K)`;
  the forgetful functor creates the scheme pullback, so it is the specified fibre product.
- Faithful flatness: `Flat q.hom.hom.left` together with the already asserted
  `Surjective q.hom.hom.left`. Finite presentation is
  `LocallyOfFinitePresentation q.hom.hom.left ∧ QuasiCompact q.hom.hom.left ∧
  QuasiSeparated q.hom.hom.left`, exactly the dependency node's comparison clause.
- The torsor isomorphism is `e : H_K.X ⊗ (splitTorus K r).X ≅
  pullback q.hom.hom q.hom.hom` in schemes over K. Its first projection is `fst`;
  its second is `lift fst (snd ≫ i.hom.hom) ≫ μ[H_K.X]`. Thus the map is precisely
  `(h,t) ↦ (h,h i(t))`, not an unspecified isomorphism or arbitrary action.

Dependency declarations used (their signatures and docstrings were read):

- `def-weil-field`: Mathlib `Field` (Algebra.Field.Defs).
- `def-sc-group-scheme`: `CategoryTheory.Grp`, `GrpObj`, `IsCommMonObj`, and bundled
  group homomorphisms (Mathlib.CategoryTheory.Monoidal.Grp and Mon). The recorded
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents the specialization to
  `Over (Spec k)` and the kernel fibre product; it is available through the torus module.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`
  (Mathlib.AlgebraicGeometry.Morphisms.Smooth).
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`
  (Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact).
- `def-pc-field-extension`: `Algebra` (Mathlib.Algebra.Algebra.Defs), with its
  `algebraMap` determining the spectrum map used by base change.
- `def-sc-abelian-variety`: `AlgebraicGeometry.IsAbelianVariety`
  (WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd` (Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback).
- `def-sbc-locally-finite-presentation`: `LocallyOfFinitePresentation`
  (Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation).
- `def-pc-fppf-site`: `Scheme.fppfTopology`
  (Mathlib.AlgebraicGeometry.Sites.Fpqc), with its slice topology from
  Mathlib.CategoryTheory.Sites.Over. Local surjectivity uses
  `Presheaf.IsLocallySurjective` (Mathlib.CategoryTheory.Sites.LocallySurjective).
- `def-weil-proper-morphism`: `IsProper` and `IsSeparated`
  (Mathlib.AlgebraicGeometry.Morphisms.Proper and Separated).
- `def-weil-algebraic-closure`: `AlgebraicClosure` and `IsAlgClosure`
  (Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure and Basic).
- Added the already landed `def-sfb-tori-multiplicative-type` to `stmt_deps`, using
  its `MultiplicativeType.baseChange` and `MultiplicativeType.splitTorus`
  (Sheaf.AlgebraicGeometry.ToriMultiplicativeType). This is the shared rank-zero-aware
  finite product of `StandardGroupSchemes.multiplicative`, whose coordinate algebra
  is `LaurentPolynomial k`, as required. No copy of either construction is introduced.

`GeometricallyConnected` (Mathlib.AlgebraicGeometry.Geometrically.Connected) expresses
an inline property in the original statement. `FiniteDimensional` and `IsGalois`
(Mathlib.LinearAlgebra.FiniteDimensional.Defs and Mathlib.FieldTheory.Galois.Basic)
express the statement's explicit meaning of finite Galois.

The module imports all recorded proof modules (ordinary imports for proof-only use):
IsSepClosed, EtaleFieldGsets, FpqcAffineDescent, LimitAffineTransition,
NagataMorphismDescends, AlgebraicSpaceFpqcSheaf, MultiplicativeTypeLargestSubtorus,
and ProperMorphismFpqcDescent. Mathlib proof inputs come from Flat.Basic,
Galois.GaloisClosure, RingTheory.FinitePresentation, and Sites.Fpqc. The proof nodes
with no recorded Lean statement (invertible multiplication, dense-rational descent,
character antiduality, split-torus matrices, algebraic-group monomorphism,
smooth-connected-fibre integrality, and smooth commutative subgroup quotient) remain
named in the nine-step docstring; no fictitious module is imported for them.

Source and edge checks:

- Read Conrad Theorem 3.1 in the primary online PDF, pp.7--8:
  https://math.stanford.edu/~conrad/DarmonCM/2011Notes/SemistableReduction.pdf.
  The theorem explicitly descends the torus over imperfect fields. Read the local
  Milne iAG2017 PDF, Definition 12.14 and Theorem 12.18(d), printed pp.236--238,
  for the split torus and separable splitting. The source supports the unchanged node.
- r=0 uses the existing terminal split torus. The kernel is trivial and the torsor
  identity reduces to the expected diagonal description; nothing requires r>0.
- H=Spec k and A=Spec K are permitted. A group scheme has an identity section, so the
  empty scheme cannot satisfy the group hypothesis over a field.
- A nonsplit torus is allowed: K/k may be nontrivial. The quotient can be the
  zero-dimensional abelian variety. No section of q is assumed or concluded.
- Imperfect fields and positive characteristic are retained; the proof uses a prime
  different from the characteristic, with no perfection hypothesis in the signature.
- Scheme-theoretic kernel equality handles nonreduced test algebras, rather than only
  field points. The fppf topology and local-surjectivity definition test all schemes
  of the chosen universe. All scheme and field objects lie in the same explicit u;
  the finite extension and algebraic closure admit models there. No independent lower
  test universe can make a hypothesis vacuous.

Searches actually run:

1. msearch.py leanfinder: `A smooth commutative geometric semiabelian group has a split
   torus kernel and abelian variety quotient after finite Galois field extension`.
   Eight hits, on absolute Galois groups, abelian Galois extensions, Galois categories,
   and smooth algebras; none states this group-scheme result.
2. msearch.py loogle: `IsAbelianVariety, IsGalois, GrpObj.ker, splitTorus`.
   Zero hits; the service reports unknown identifier `IsAbelianVariety`.
3. msearch.py grep: `semiabelian|splitTorus|torsor`, Mathlib subdirectory
   `AlgebraicGeometry`. Zero hits.
4. msearch.py leansearch: `A semiabelian group scheme is a split torus torsor over an
   abelian variety after a finite Galois extension`. Eight hits on abelian Galois
   extensions, abstract group-extension splittings, and absolute Galois groups; none
   supplies the scheme statement.
5. rg in WeilConjectures for `semiabelian|semiAbelian|split.*quotient|splitTorus`:
   unrelated splitting results only. A literal item-id search there has no match.
6. rg in Sheaf for `geometric.*semiabelian|semiabelian.*split|
   geometric_semiabelian_split_quotient`: the consumer RelativePicardCubeFaceDetection
   cites this missing lemma; no declaration of this theorem exists. Targeted searches
   found the reusable ToriMultiplicativeType and SemiabelianGeometricFibres modules;
   their full definitions were read. The latter quantifies over all geometric fibres
   and existentially binds the rank, so it does not replace this fixed-rank hypothesis.
7. Read the original node, every statement dependency and its Lean record or Mathlib
   match, the group/torus source declarations, and the consumer's use of this lemma.
   No exact existing theorem was found. No new definition search or node was needed.

Validation: the prescribed scompile.py server compile passed for the single delivered
module, with no errors or non-sorry warnings. The theorem's signature is recorded
verbatim in `lean.statement`. Only `lean` and the permitted added statement dependency
change in the item node. There is no statement correction or STATEMENT-DISPUTED flag.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
