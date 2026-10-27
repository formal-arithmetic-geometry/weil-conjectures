## Worker report

The module `Sheaf.AlgebraicGeometry.TorusInducedQuotient` states
`AlgebraicGeometry.MultiplicativeType.torus_induced_quotient`, with `sorry`
as its entire proof. No definitions, auxiliary theorems, or node corrections
are introduced. Only the assigned node's `lean` field is changed.

Source checked directly: Milne, Algebraic Groups (2017), printed p.251
(PDF page 263), Lemma 12.61, Definition 12.62, Proposition 12.63.
The source constructs an injection of the character lattice into a finite
permutation lattice, and obtains a surjective homomorphism from an induced
torus. The source's product of restrictions has precisely the stated unit
functor. The DAG's expanded proof and all its clauses are retained.

Hypothesis and clause correspondence:

- Any field k: `{k : Type u} [Field k]`, with explicit universe `u`.
- A k-torus T: `T : Grp (Over (Spec (.of k)))` and `hT : IsTorus T`.
  This is the dependency's geometric-splitting definition, without any extra
  smoothness, perfection, characteristic or finite-type assumption.
- Integer m >= 1: `∃ (m : ℕ), 1 ≤ m ∧ ...`. The source's nonnegative integer
  is encoded by a natural number; the positivity conjunct excludes m=0.
- Extensions L_1,...,L_m: `L : Fin m → CommAlgCat.{u} k` together with
  `∀ i, IsField (L i)`. A commutative k-algebra whose ring is a field is
  exactly a field extension, as in def-pc-field-extension. This bundling
  keeps the algebra structures canonical throughout the tensor and maps;
  `IsField` includes 0 != 1, not merely invertibility of nonzero elements.
- Finite dimensionality and separability: the conjunct
  `∀ i, FiniteDimensional k (L i) ∧ Algebra.IsSeparable k (L i)`.
  The latter is Mathlib's assertion that every element's minimal polynomial
  is separable; over a field this means no repeated algebraic-closure roots.
- An affine k-torus P: `∃ P : Grp (Over (Spec (.of k))),
  IsTorus P ∧ IsAffine P.X.left ∧ ...`.
- A group homomorphism pi: `π : P ⟶ T` in the category of group objects.
  The underlying scheme morphism is `π.hom.hom.left`.
- Scheme-point surjectivity: `Surjective π.hom.hom.left`, the existing
  class asserting surjectivity of the underlying continuous point map.
  There is no assertion of surjectivity on rational points.
- A is the product of the L_i: the literal dependent function ring
  `(∀ i, L i)` has componentwise ring operations and diagonal k-algebra
  structure. No auxiliary arbitrary algebra or isomorphism replaces A.
- All commutative k-algebras R: `R : CommAlgCat.{u} k`. Objects include
  zero rings and nonreduced rings. The usual universe of schemes and their
  affine test rings is shared with the recorded torus definition.
- P(R)=Hom_k(Spec R,P): `((algSpec (.of k)).obj (op R) ⟶ P.X)`.
  Mathlib's `algSpec` is Spec of the algebra structure map in the over
  category, and the scoped `CategoryTheory.MonObj` instance gives this
  Hom set exactly the group law from P's group-object structure.
- Group isomorphisms: a single family `e : ∀ R, ... ≃* ...ˣ` is existentially
  quantified before the naturality equation, so all components belong to
  the same natural family. `ˣ` is the units group of the tensor ring.
- Tensor algebra: `((∀ i, L i) ⊗[k] R)` uses the recorded
  `Algebra.TensorProduct.instCommRing` and k-algebra structure.
- Natural in R: for every `f : R ⟶ R'` and every point `p`,
  `e R' ((algSpec (.of k)).map f.op ≫ p) =
  Units.map (Algebra.TensorProduct.map (AlgHom.id k (∀ i, L i))
  f.hom).toMonoidHom (e R p)`.
  The left side is pullback of a point along Spec(f); the right side is
  the units map of id_A tensor f. Thus the variance and group maps are
  the canonical ones, not unspecified maps.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-sfb-tori-multiplicative-type:
  `AlgebraicGeometry.MultiplicativeType.IsTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType. Its scalar extension is
  `Over.pullback(...).mapGrp` and its geometric split torus includes rank 0.
- def-sc-group-scheme: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`,
  Mathlib.CategoryTheory.Monoidal.Grp; `CategoryTheory.Hom.group`,
  Mathlib.CategoryTheory.Monoidal.Cartesian.Grp. The recorded
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documentation confirms
  exactly this interpretation in `Over (Spec k)`.
- def-pc-field-extension and def-weil-pbc-algebra-hom-quotient:
  `Algebra` (Mathlib.Algebra.Algebra.Defs), `AlgHom`
  (Mathlib.Algebra.Algebra.Hom), with their standard CommAlgCat bundling.
- def-weil-finite-dimensional-subspace: `FiniteDimensional`,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs (abbreviation for Module.Finite).
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec`, `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme; their algebra-over-base version
  `AlgebraicGeometry.algSpec`, Mathlib.AlgebraicGeometry.Group.Affine.
- lem-weil-pbc-algebra-tensor-pushout-universal-property:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `ext` in Mathlib.RingTheory.TensorProduct.Basic and
  `productMap` in Mathlib.RingTheory.TensorProduct.Maps. Naturality uses
  that module's `Algebra.TensorProduct.map` on the same tensor algebra.
- Separability uses `Algebra.IsSeparable` and `IsSeparable` in
  Mathlib.FieldTheory.Separable, with the minimal-polynomial signature read.

Recorded proof modules are imported with ordinary (non-public) imports:
FpqcAffineDescent, Morphisms.LocallyOfFiniteTypeOfFpqcCover,
MultiplicativeCharacterAntiduality; the recorded Mathlib proof interfaces
come from Flat.FaithfullyFlat.Algebra, Morphisms.Flat,
Morphisms.FiniteType and LinearAlgebra.TensorProduct.Pi. The existing
StandardGroupSchemes and fpqc definitions are already public dependencies
of these interfaces. The unstated character/induced-unit prerequisites
are not needed to type this statement, and are listed in its proof docstring.
No unstated prerequisite is replaced by an assumption.

Edge cases checked mathematically before drafting:

- Rank-zero T: choose m=1 and L_1=k; G_m -> 1 is scheme-surjective.
  Thus positivity of m is compatible with the trivial torus.
- A zero test algebra R is admitted by CommAlgCat. Both its affine point
  group (morphisms from the empty scheme) and the tensor algebra's units
  group are trivial. No Nontrivial R assumption is imposed.
- Finite fields, imperfect fields, and positive characteristic are included;
  only the existentially supplied L_i/k must be separable.
- Non-normal finite separable extensions are permitted, not only Galois ones.
- Scheme-surjectivity is distinguished from k-point surjectivity; there is
  no saturation or smooth-kernel condition on the lattice injection.
- Naturality includes identities and arbitrary k-algebra maps, including
  maps into the zero ring and maps involving nonreduced test rings.

Searches for an existing theorem:

- msearch.py leanfinder: "Every algebraic torus over a field is a scheme
  surjective quotient of a finite induced torus with points the units of a
  tensor product". Eight hits: affine-space surjectivity, pointsPi,
  affine Spec essential surjectivity, and other unrelated scheme results.
  No algebraic-torus quotient theorem.
- msearch.py loogle: `"IsTorus", "Surjective"`: zero hits.
- msearch.py grep: `inducedTorus|IsTorus|WeilRestriction|weilRestriction`:
  zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for
  `inducedTorus|torus.*[Qq]uotient|unitsFunctor|unitFunctor|torus_induced|lem-sfb-torus-induced-quotient`:
  only different relative/geometric torus quotient statements; none says this.
- rg in dag/lean_names_upstream.json, Mathlib, WeilConjectures and Sheaf for
  the chosen name `torus_induced_quotient`: no pre-existing declaration.
- The exact torus definition, group-object Hom group, algSpec, tensor map
  and separability interfaces were read in their respective source modules.

Validation: prescribed scompile.py compiled the statement on the server
cleanly (only the allowed postponed proof); the delivery dry run also
compiles the final file with its proof-only finite-product tensor import.

No STATEMENT-DISPUTED flag or node fault.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
