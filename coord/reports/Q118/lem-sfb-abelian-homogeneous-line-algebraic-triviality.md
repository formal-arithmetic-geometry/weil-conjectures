## Worker report

Statement-only delivery for `lem-sfb-abelian-homogeneous-line-algebraic-triviality`.
The module is
`Sheaf.AlgebraicGeometry.AbelianVariety.HomogeneousLineAlgebraicTriviality`;
its only declaration is
`AlgebraicGeometry.IsAbelianVariety.areAlgebraicallyEquivalent_unit_of_homogeneous`.
Its proof is `by sorry`. No definitions, axioms or additional assumptions are introduced.

I read the whole node, its five statement dependencies and their recorded declarations,
the existing algebraic-equivalence definition and its node, the recorded proof dependencies,
and Milne, Abelian Varieties I §8, printed pp.35–40 (PDF pp.41–46). Proposition 8.4(b)
is precisely the translation-invariance hypothesis; Proposition 8.14 expresses such a
class as an ample translation difference. The family following it realizes these classes
as fibres. The theorem docstring carries all four accepted proof steps, including the
local tensor-pullback calculation and the smooth connected family.

Clause-by-clause correspondence:

- `Let k be an algebraically closed field`: `{k : Type u} [Field k] [IsAlgClosed k]`.
  `u` is declared explicitly; both automatic-implicit options are disabled.
- `A/k is an abelian variety`: `(A : Over (Spec (.of k))) [GrpObj A]
  [IsAbelianVariety A]`. The recorded `IsAbelianVariety` gives properness,
  smoothness and connectedness; `GrpObj A` supplies the group-scheme structure
  required separately by that recorded definition.
- `L is an invertible O_A-module`: `(L : A.left.Modules)
  [Scheme.Modules.IsInvertible L]`. This is the recorded local-rank-one definition,
  with no assumption of ampleness, symmetry, a rigidification or nontriviality.
- `a in A(k)` and `t_a(x)=x+a`: `a : 𝟙_ (Over (Spec (.of k))) ⟶ A`
  and `(AlgebraicGeometry.GrpObj.mulRight A a).left`. Reading GroupScheme.Basic
  shows its body is `lift (𝟙 A) (toUnit A ≫ a) ≫ μ[A]`, hence right translation
  under the same group structure. It is the existing scheme translation, not a
  newly chosen morphism or the similarly named abstract categorical isomorphism.
- `t_a^*L ≅ L for every a`: `homogeneous : ∀ a, Nonempty
  ((Scheme.Modules.tensorPullback (GrpObj.mulRight A a).left).obj L ≅ L)`.
  Pullback is the recorded tensor inverse image, not Mathlib's adjoint-choice pullback.
- `L is algebraically equivalent to O_A`: `Scheme.Modules.AreAlgebraicallyEquivalent
  A L (SheafOfModules.unit A.left.ringCatSheaf)`. The latter module is the structure
  sheaf. Reading both declarations in LineAlgebraicEquivalence shows that the former
  is the reflexive symmetric transitive closure of isomorphic pairs and pairs of fibres
  of an invertible module on `A ⊗ T`, with T smooth, connected, separated and of finite
  type. The fibre maps are `(id,t_i)` and use `tensorPullback`. This is exactly the
  equivalence relation on line-module isomorphism classes specified in the node;
  smooth connected varieties use Milne's separated finite-type convention.
- `No restriction on characteristic or dimension`: no characteristic predicate,
  integer invertibility, dimension binder or positive-dimension assumption occurs.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field` (read lines 174–185).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (read lines 58–65).
  The algebraic-closure node explicitly records this predicate for the closedness clause;
  an actual extension field `AlgebraicClosure k` is not needed here.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety` (full signature and docstring read).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (full signature and docstring read).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded pullback
  interface; it publicly imports `WeilConjectures.AlgebraicGeometry.TensorPullback`,
  whose `AlgebraicGeometry.Scheme.Modules.tensorPullback` has the real tensor formula.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`:
  `AlgebraicGeometry.GrpObj.mulRight` (lines 119–125).
- `Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence`:
  `AlgebraicGeometry.Scheme.Modules.AreAlgebraicallyEquivalent` and its generator
  `LineAlgebraicEquivalenceStep`; both full definitions and docstrings read.

The existing, landed definition node `def-sfb-line-algebraic-equivalence` is added to
`stmt_deps` under brief-stage2 §5 (statement dependencies may gain landed nodes).
The item's mathematical statement, accepted split and all other fields are unchanged.
No new definition node or dependency repair is needed.

Proof-only imports use plain `import`: the recorded module
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective` (including the read
`IsAbelianVariety.exists_isAmple`) and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
(the recorded module of `def-pur-sheaf-tensor-product`). Invertibility and pullback
are already public statement imports. `lem-sfb-ample-translation-difference-surjectivity`
has no recorded Lean declaration/module in the read base, so its import is omitted;
the theorem docstring names this proof prerequisite without assuming it as a hypothesis.

Edge cases checked mathematically: A = Spec k (dimension zero), L = O_A, the identity
translation, a = 0 in the family, a degree-zero line on an elliptic curve, and positive
characteristic including inseparable ample polarizations. All are admitted. A positive-degree
line on an elliptic curve fails the hypothesis for some translation, as expected. The empty
scheme is not an abelian variety: the recorded connectedness and group unit already exclude
it. No distinctness of parameter points is demanded. The family T=A lives in the same
scheme universe, and no extra size equality is imposed.

Searches actually performed for this delivery:

- `msearch.py leanfinder`, query `A translation invariant line bundle on an abelian
  variety is algebraically equivalent to the trivial line bundle`: 8 hits, all ring
  Picard-group declarations (`CommRing.relPic_eq_top`, `CommRing.Pic.mk_eq_one`, etc.);
  none states the geometric theorem.
- `msearch.py loogle`, query `"Picard"`: 12 hits concerning Picard–Lindelöf ODEs;
  no geometric match.
- `msearch.py leansearch`, query `Translation invariant invertible sheaves on an abelian
  variety are algebraically trivial`: 8 hits, including module-sheaf isomorphism facts,
  ring tensor inverses, group transversals and invariant vector fields; none is this theorem.
- `msearch.py grep`, query
  `algebraically.trivial|algebraicEquiv|homogeneous.*line|translationInvariant`,
  subdirectory `AlgebraicGeometry`: 0 hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for algebraic-equivalence and
  homogeneous-line names: found the landed LineAlgebraicEquivalence definition,
  MultiplicationAlgebraicEquivalence consumer, and HomogeneousCoherentAcyclicity
  theorem, but no declaration of the item. The latter two are different statements.
- `rg` over the upstream source by the item's id: no match.
- Exact-name `rg` in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and
  Sheaf for `areAlgebraicallyEquivalent_unit_of_homogeneous`: no pre-existing match.
- DAG text search located `def-sfb-line-algebraic-equivalence`, so its recorded
  declaration is reused rather than duplicated.

No statement dispute or mathematical correction was found.

## Second reading by Q118

This is a separate sequential self-reading, not a claim of an independent second agent:
the dispatcher's explicit instruction forbids starting other agents; the maintainer's
independent review remains required. I reopened the completed module and the node copy
and compared the displayed signature against each sentence of the unchanged statement.
`Field` plus `IsAlgClosed` matches the base; the bundled k-scheme with `GrpObj` plus
`IsAbelianVariety` matches the abelian variety; `IsInvertible` matches L; the universal
rational-point binder and `mulRight` match x ↦ x+a, with `tensorPullback` and `Nonempty
(_ ≅ _)` matching the invariance hypothesis. The conclusion uses the existing EqvGen
family relation with the structure-sheaf module as endpoint. No reverse implication or
single-family witness was substituted for this conclusion. Reading the generator confirms
smoothness, connectedness, separated finite type, invertible family and the actual tensor
fibre maps. There is no characteristic or dimension restriction. No mismatch found;
no Lean change resulted from this second reading.

Validation: the required `scompile.py Q118
lem-sfb-abelian-homogeneous-line-algebraic-triviality <module>` completed successfully
for both sandbox and library module names (56.0 s and 21.8 s), with no diagnostics.
The node copy differs from the read base only in `lean` and the added landed definition
in `stmt_deps`. The verbatim signature is extracted directly from the final module;
every Lean line is at most 100 characters. The requested CompactObject example has
been withdrawn, so I also read its recorded upstream replacement for conventions.
