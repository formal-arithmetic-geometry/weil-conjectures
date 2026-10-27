## Worker report

The module `Sheaf.AlgebraicGeometry.InducedUnitTorusCharacters` states
`AlgebraicGeometry.MultiplicativeType.exists_inducedUnitTorus_characters`.
There is one theorem, with proof `sorry`, and no new definitions. The node is
unchanged except for its `lean` record. No statement correction or disputed claim.

Hypotheses and conclusions, clause by clause:

- Any field k: `(k : Type u) [Field k]`. No characteristic or perfectness assumption.
- A separable closure: `(ks : Type u) [Field ks] [Algebra k ks] [IsSepClosure k ks]`.
- A finite separable field extension: `(L : Type u) [Field L] [Algebra k L]
  [FiniteDimensional k L] [Algebra.IsSeparable k L]`. The last class says every
  minimal polynomial is coprime to its derivative. Over a field this is equivalent
  to its roots in an algebraic closure being distinct, exactly the node's wording.
- The affine k-group scheme Q_L is `Q : Grp (Over (Spec (.of k)))` with
  `IsAffine Q.X.left`. Its structure morphism has both `LocallyOfFiniteType` and
  `QuasiCompact`, the recorded finite-type convention.
- It is a torus: `IsTorus Q`, using the recorded algebraic-closure splitting definition.
- Its group of R-points is `StandardGroupSchemes.affine k R ⟶ Q.X`, namely
  morphisms over Spec k from Spec R, with the existing `CategoryTheory.Hom.group`
  pointwise group structure. `e R` is a multiplicative equivalence to `(L ⊗[k] R)ˣ`.
  The quantifiers cover all commutative k-algebras in the ambient universe, including
  zero and nonreduced rings. They do not restrict R to fields or finite-type algebras.
- Naturality: for every algebra map `f : R →ₐ[k] S`, the first universal clause
  identifies precomposition with `StandardGroupSchemes.map k f` with
  `Units.map (Algebra.TensorProduct.map (AlgHom.id k L) f).toMonoidHom`.
- The embedding set E is literally `L →ₐ[k] ks`; Gamma is `ks ≃ₐ[k] ks`.
- The canonical tensor decomposition is the existential algebra equivalence
  `theta : (L ⊗[k] ks) ≃ₐ[k] ((L →ₐ[k] ks) → ks)`, followed by its exact formula
  `theta (a ⊗ₜ[k] b) σ = σ a * b`. Although bundled over k, this formula also
  forces ks-linearity for the right-factor scalar structure: apply it to
  `1 ⊗ₜ b` and use additivity. Thus it specifies the stated ks-algebra splitting
  without introducing a separate right-factor algebra instance.
- The free abelian character identification is the equivalence `chi` from
  `FreeAbelianGroup (L →ₐ[k] ks)` to the dependency's `GeometricCharacters ks Q`.
  The subsequent `chi (x+y)` clause explicitly says addition corresponds to
  pointwise multiplication of characters. The existing geometric-character
  interface is an unbundled Hom type, so the law is stated on the underlying
  morphisms; the forgetful functor from group objects is faithful.
- Equivariance is `IsConjugate γ (chi x) (chi (FreeAbelianGroup.map
  (fun σ ↦ γ.toAlgHom.comp σ) x))`. The free-group map sends the labelled basis
  element for σ to that for gamma composed with σ, with the specified left action.
- The last universal clause normalizes every basis element `FreeAbelianGroup.of σ`
  as the coordinate character on every ks-algebra R. Here p is its underlying
  k-point of Q and q the corresponding point of Q_ks. The equality
  `q.left ≫ scalarProjection Q = p.left` is the pullback characterization of
  this correspondence, not an extra restriction on test points: given p and its
  ks-algebra structure there is a unique such q by the pullback universal property.
  The left side evaluates the Laurent generator of the actual scheme character
  using `characterElement`, `q.left.appTop`, and `Scheme.ΓSpecIso`.
  The right side applies the tensor evaluation `a ⊗ r ↦ σ(a)r` to the unit
  `e R p`. By theta's displayed formula and base extension, it is exactly the
  σ-coordinate in split coordinates. Checking all test algebras specifies regular
  characters, rather than only their values on ks-rational points.

Dependency declarations read and used:

- Mathlib: `Field` (`Algebra.Field.Defs`), `Algebra` (`Algebra.Algebra.Defs`),
  `FiniteDimensional` (`LinearAlgebra.FiniteDimensional.Defs`),
  `Algebra.IsSeparable` (`FieldTheory.Separable`), `Spec` and `Spec.map`
  (`AlgebraicGeometry.Scheme`), `LocallyOfFiniteType`
  (`AlgebraicGeometry.Morphisms.FiniteType`), `QuasiCompact`
  (`AlgebraicGeometry.Morphisms.QuasiCompact`), and `CategoryTheory.GrpObj` / `Grp`
  (`CategoryTheory.Monoidal.Grp`). These imports are public transitively through
  the recorded geometry interfaces, with their actual signatures inspected.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem`, documenting and using Mathlib's
  `IsSepClosure`; the latter's full definition was also read.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `baseChange`, `IsTorus`.
- `Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality`: the recorded
  `multiplicative_character_antiduality`; its public data module supplies
  `GeometricCharacters`, `IsConjugate`, `scalarProjection`, `characterElement`.
  All these docstrings and full signatures were read. This uses the actual
  character Hom type and conjugation, without selecting a new antiequivalence.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, `multiplicative`,
  `multiplicativeGroup`, through the above public imports.
- `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`:
  `Algebra.TensorProduct.instCommRing`, `includeLeft`, `includeRight`, `ext`,
  `productMap` and its pure-tensor formula; `.map` for naturality. Tensor products
  and their algebra structure are the recorded dependency, not a private copy.
- `AlgebraicClosure` / `IsAlgClosure` (`FieldTheory.IsAlgClosed.AlgebraicClosure`
  and `.Basic`) enter through the recorded definition of `IsTorus`.

Imports of stated proof dependencies are retained as plain imports, including
localization, affine geometry, Yoneda, separability, CRT, polynomial quotient,
and tensor finite products. The three proof nodes
`lem-sfb-finite-algebra-units-affine-chart`,
`lem-zl-finite-separable-tensor-primitive-presentation`, and
`lem-sfb-split-torus-hom-matrices` have no recorded Lean declaration or Mathlib
match in the read snapshot, so there is no module of theirs to import. Their
proof steps are preserved in the theorem docstring. None is needed to type the
statement. The existing algebraic closure is used within `IsTorus`, rather than
introducing a redundant closure parameter.

Edge cases checked before writing: L=k has a singleton embedding set and Q=G_m;
C/R gives two conjugate coordinates and their permutation; finite fields give
cyclic permutation of embeddings; imperfect k still has a valid separable closure,
and only L/k is assumed separable. No positivity of a rank is imposed. The zero
ring has singleton units and singleton point group; nonreduced test rings are
covered. No rational-points-only character identification is used. The common
ambient universe is the convention already required by the recorded base-change
and character APIs; no independent smaller universe is used for test algebras.

Searches (2026-10-24):

- msearch leanfinder, `Characters of the unit torus of a finite separable field
  extension form the free abelian group on embeddings`: eight unrelated number-field
  unit/additive-character hits; no scheme-theoretic unit-torus character theorem.
- msearch loogle, `FreeAbelianGroup, AlgHom`: zero hits.
- msearch grep, `WeilRestriction|weilRestriction|inducedUnitTorus|unit.torus`: zero hits.
- msearch leansearch, `Weil restriction multiplicative group finite separable
  extension permutation characters`: eight unrelated `MulChar` and ordinary
  Galois-group hits, none representing the unit torus or its character module.
- rg on both `lean/WeilConjectures` and `lean/Sheaf` for
  `unit.torus|inducedUnitTorus|WeilRestriction|weilRestriction|lem-sfb-induced-unit-torus-characters`:
  only unrelated constant-Weil restriction maps; no existing declaration of this statement.
  Direct inspection of the character and torus modules confirmed the available
  general notions and absence of this finite-separable example.

Source checked directly: Milne PDF pp.57--59 (PDF pages 69--71), and pp.250--251
(PDF pages 262--263), using pdftotext to stdout. This confirms the represented
unit functor, scalar-extension decomposition and embedding-indexed characters.

Validation: scompile.py compiled the delivered module against current server sources
in 3.4 seconds, exit 0 and no warnings. Its preceding local attempt reported no
space left on device; the wrapper's normal server fallback succeeded.

## Second reading by Q119

I reread the node and completed module separately after compilation. This is a
second pass by this worker, not a claim of an independent agent review; the brief
forbids starting other agents and specifies the maintainer's independent review.
The fields, separable closure, finite dimension and separability match the binders.
The four properties of Q are all present. The equivalences are group equivalences,
and their explicit naturality covers every algebra map. The embedding set and
Galois group are the actual algebra-Hom and algebra-automorphism types. The free
abelian equivalence includes its addition law and full conjugation law. The
pure-tensor formula fixes theta uniquely. The final test-algebra formula fixes
labelled scheme characters and agrees with that same theta. L=k is included.
No mismatch requiring a change was found. Definitions contain no postponed data;
there is only the requested theorem proof `sorry`, with the full seven-step plan.
