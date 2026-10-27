## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupTensorReconstruction` states
`AlgebraicGeometry.RationalRepresentation.affineGroup_tensor_reconstruction` with its
sole proof `sorry`. No definitions, instances, helpers, new nodes, dependency repairs,
or statement corrections are introduced. The node's other fields are unchanged.

Source read: Milne, *Algebraic Groups* (2017), printed pp.163--165, especially
Theorem 9.2, conditions (a), (b), (c), Lemma 9.1, and Note 9.3. The source explicitly
starts with linear maps, not automorphisms, and allows an arbitrary commutative
coefficient algebra. Its algebraic groups here are affine of finite type. The
current blueprint unit `sk-thm-sf-ctf-stability/_section.md` and its direct-images
proof (3) were also read; this supporting lemma does not change that unit.

Hypotheses and clauses, compared with the unchanged DAG statement:

- Field k: `{k : Type u} [Field k]`.
- Affine k-group scheme G: `(G : Scheme.{u}) [G.Over (Spec (.of k))]`,
  `[GrpObj (G.asOver (Spec (.of k)))]`, and `[IsAffine G]`. These retain the
  actual scheme, its structure map, and its specified group law.
- Finite type: `[LocallyOfFiniteType (G ↘ Spec (.of k))]` and
  `[QuasiCompact (G ↘ Spec (.of k))]`, exactly the recorded convention.
- Commutative k-algebra R: `(R : Type u) [CommRing R] [Algebra k R]`.
  There is no field, domain, reducedness, or nontriviality assumption on R.
- Every finite-dimensional rational representation: the dependent family `lam`
  quantifies over every `V : Type u`, its additive group and k-module structures,
  its `FiniteDimensional k V` instance, and every `NaturalRepresentation G V`.
  That is the dependency's recorded natural-family definition, with the
  `finite_dictionary` theorem identifying it with group-scheme representations.
- Scalar extension V_R: the actual `R ⊗[k] V` from Mathlib `TensorProduct`.
  This agrees directly with the left scalar convention of the item's statement
  and the recorded dictionary's implementation.
- R-linear endomorphism lambda_V: `lam V r : R ⊗[k] V →ₗ[R] R ⊗[k] V`.
  The family is indexed by the representation r as well as its vector space.
- Tensor compatibility (a): `h_tensor` quantifies over V, W, r, s, and a
  representation t on the actual `V ⊗[k] W`. Its premise characterizes t by
  `distribBaseChange` intertwining its action with the tensor of the r and s
  actions over EVERY test algebra T and every point x. Its conclusion is the
  same intertwining equation for `lam (V ⊗[k] W) t` and
  `TensorProduct.map (lam V r) (lam W s)` over R, on every tensor z.
  This is precisely conjugation by the canonical tensor identification.
  `tensor_coaction` of the recorded dependency supplies the unique t satisfying
  this action premise, so the premise is not an extra restriction or a vacuous
  hypothesis. Using its characterization avoids choosing a second tensor action.
- Trivial unit compatibility (b): `h_unit` applies to every r on k whose
  action over every T and x is `1`. It requires `lam k r = LinearMap.id` on
  R tensor k; conjugating by the canonical unit isomorphism is exactly id_R.
  The dependency's `trivial_coaction` provides the unique such representation.
  Requiring the identity on the actual scalar extension adds no chosen unit map.
- Equivariant-map compatibility (c): `h_natural` quantifies over all V, W,
  representations r,s, and `f : V →ₗ[k] W`. Its premise says
  `f.baseChange T ∘ₗ r(x) = s(x) ∘ₗ f.baseChange T` for every test algebra
  and point, exactly G-equivariance; the dependency's `intertwines_iff` also
  identifies this with coaction equivariance. The conclusion is
  `lam W s ∘ₗ f.baseChange R = f.baseChange R ∘ₗ lam V r`.
- Existence and uniqueness of g in G(R): `∃! g : points (G.asOver ...) R`.
  Here `points` is the existing actual scheme-of-points interface; no arbitrary
  point model, surrogate algebra map, or chosen bijection is introduced.
- Every action equals lambda: the conclusion quantifies over every finite V
  and every r and gives `(r.action R g).toLinearMap = lam V r`.
- No invertibility assumption: none of the family binders or the three
  compatibility hypotheses requires `IsUnit`, bijectivity, or an equivalence
  for lam. The conclusion identifies it with an action automorphism, so its
  invertibility is automatic, as in Milne Note 9.3; no extra conclusion is added.
- Universe convention: k, G, V, W, R and test algebras use one fixed u,
  exactly the dependency's convention. The family quantifies over Type u and
  lives in u+1. Test algebras have no independent smaller universe, and the
  coordinate algebra itself is among them.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs` (full definition).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; its specialization to `Over (Spec k)`
  was read in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `QuasiCompact`, in the corresponding Mathlib morphism modules.
- `lem-sfb-rational-representation-comodule-dictionary`:
  `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`, full file
  read, in particular `NaturalRepresentation`, `intertwines_iff`,
  `finite_dictionary`, `trivial_coaction`, and `tensor_coaction`.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct` and its
  universal map/lift, `TensorProduct.map`, and the existing `LinearMap.baseChange`.
  `TensorProduct.AlgebraTensorModule.distribBaseChange`, in
  `Mathlib.LinearAlgebra.TensorProduct.Tower`, is the canonical comparison:
  b tensor (v tensor w) maps to (b tensor v) tensor_R (1 tensor w);
  its inverse multiplies coefficients. Full signatures and pure-tensor formulas read.

Recorded proof-dependency modules are imported privately: basis extension
(`Mathlib.LinearAlgebra.Basis.VectorSpace`); coordinate Hopf algebra
(`Mathlib.AlgebraicGeometry.Group.Affine`); algebra-tensor pushout
(`Mathlib.RingTheory.TensorProduct.Maps`); base-change universal property
(`Mathlib.LinearAlgebra.TensorProduct.Tower`); affine spectrum and its
fully faithful dictionary (`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`).
Finite-dimensional spaces are Mathlib's existing `FiniteDimensional` alias;
its instance and tensor finiteness interfaces are available through the public
imports. The recorded proof dependency `lem-sfb-comodule-finite-subrepresentation`
has no Lean record or Mathlib match on the read base, so there is no module to
import for it yet; this is a proof prerequisite only, not a missing statement
notion. The theorem docstring gives the complete ten-step DAG proof, naming
this prerequisite explicitly, for the subsequent proof stage.

Edge cases checked before writing: V=0 (empty basis and unique endomorphism),
zero tensor factors, G the trivial group, R the zero ring (singleton G(R), zero
scalar extensions, identity=zero), R with zero divisors or nilpotents, nonreduced
G such as mu_p, positive characteristic, and arbitrary fixed universe u.
The binders exclude none of these cases. No smoothness, reducedness,
commutativity of the group law, or faithful chosen representation is assumed.

Searches actually run via `msearch.py Q81 lem-sfb-affine-group-tensor-reconstruction`:

- leanfinder: `Affine algebraic group points uniquely reconstructed from tensor
  compatible natural endomorphisms of all finite dimensional rational representations`.
  Eight hits: finite-group Tannaka lemmas and affine-scheme Hom extensionality.
  None covers general affine group schemes or arbitrary coefficient algebras.
- loogle: `HopfAlgebra, Representation, TensorProduct.map`: zero hits.
- grep: `reconstruction|Tannaka|tensor.compatible`, subdirectory `CategoryTheory`:
  one hit, a prospective Tannaka reconstruction comment in `Monoidal/Bimon_.lean`.
- leansearch: `Affine group scheme Tannaka reconstruction tensor compatible natural
  endomorphisms finite dimensional representations arbitrary algebra`: eight hits,
  finite-group Tannaka and FDRep lemmas, not the requested theorem. The full
  Mathlib `RepresentationTheory.Tannaka` header and interfaces were read:
  they assume a finite abstract group and concern automorphisms of its forgetful
  functor over an integral domain, so cannot replace this statement.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for reconstruction,
  Tannaka, and tensor compatibility: unrelated reconstruction results; no match.
  Focused searches for `tensor_reconstruction`, `tensorReconstruction`,
  `Tannaka`, `tannaka`, and representation reconstruction likewise found none.
- Direct recursive grep for the item's exact blueprint id under
  `lean/WeilConjectures`: no match. The existing representation/comodule
  dictionary is a prerequisite, not reconstruction.

No statement fault or disputed mathematical assertion was found.
All compilation uses the prescribed server wrapper; the delivery dry run and
final delivery repeat compilation and the maintainer's preflight.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
