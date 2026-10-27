## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFieldPicardNormBaseChange` states
`AlgebraicGeometry.Scheme.Pic.exists_finiteFieldNorm_baseChange`, with one `sorry`
and no new definitions. Its source is Stacks, Divisors, 0BCY
(`lemma-norm-invertible`), 0BD2 (`lemma-finite-locally-free-has-norm`), and 0BUT
(`lemma-finite-trivialize-invertible-upstairs`). I read those statements and proofs
in `literature/stacks-project/divisors.tex` and checked their tags against
`literature/stacks-project/tags/tags`. The declaration docstring carries all eight
steps of the node's transition-function proof, including independence of frames,
cover refinements, and arbitrary base change. No mathematical statement correction
is needed.

Hypotheses and clauses, in order:

- The field k is `(k : Type u) [Field k]`. The extension K/k is `(K : Type u)`
  with `[Field K] [Algebra k K]`; its specified embedding is `algebraMap k K`.
- Finiteness is `[Module.Finite k K]`, without any separability assumption. The
  natural-number degree d is `Module.finrank k K`. For a finite extension of
  fields this is positive; the node's d is the degree, not an additional input.
  The recorded `FieldExtension.degree` is this finrank cast to `WithTop ℕ`
  in the finite case, by its actual defining `if Module.Finite k K` branch.
- Every k-scheme is `Z : Over (Spec (CommRingCat.of k))`. Its underlying scheme
  is `Z.left` and its structure map is `Z.hom`. The extension map is
  `Spec.map (CommRingCat.ofHom (algebraMap k K))`.
- Z_K is exactly `pullback Z.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
  The projection p_Z in the degree formula is `pullback.fst Z.hom ...`.
- The node's Pic(W) is the existing `Scheme.Pic W`, whose definition is the
  subtype of the skeleton of `W.Modules` with invertible representatives. This
  is the actual set of isomorphism classes, rather than a set of chosen line
  bundles. The group's multiplication and one are respectively tensor product
  and the structure-sheaf class, as `Pic.mul_def` and `Pic.one_def` specify.
- `∃ Nm : ∀ Z : Over (Spec (CommRingCat.of k)), (Z_K).Pic →* Z.left.Pic`
  supplies one simultaneous norm family. Each `MonoidHom` preserves products
  (`map_mul`) and one (`map_one`), exactly the first two norm properties.
- For every invertible A on Z, the first conjunct, quantified over every
  `A : Z.left.Pic`, says `Nm Z (Pic.map p_Z A) = A ^ Module.finrank k K`.
  Every invertible module has its `Pic.ofIsInvertible` class, and every class
  has an invertible representative (`Pic.isInvertible_fromSkeleton`), so
  quantifying classes is equivalent to the node's quantification of modules.
  Group powers are the classes of tensor powers because the group operation
  is the existing tensor product. No independent tensor-power construction is
  introduced.
- Every k-morphism h is `h : W ⟶ Z` for `W Z : Over (Spec (.of k))`, with
  underlying morphism `h.left`. Its scalar extension is exactly
  `((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map h).left`.
  This is the chosen morphism of fibre products with the two required
  projections, not an arbitrary cartesian-square map.
- For every line F on Z_K, the second conjunct quantifies `F : (Z_K).Pic` and
  states `Pic.map h.left (Nm Z F) = Nm W (Pic.map h_K F)`. Its orientation is
  precisely `h^* Nm_Z([F]) = Nm_W([h_K^* F])`.
- There are no assumptions about smoothness, finite type, separatedness,
  reducedness, Noetherianity, flatness of h, or separability of K/k. The single
  universe parameter is the existing category-of-schemes size convention; the
  theorem is universal in that parameter and uses the full category `Over`.

Dependency declarations used and inspected:

- `Mathlib.Algebra.Field.Defs`: `Field` (commutative field).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap` (field extension).
- `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree`; its finite branch
  is expressed by `Module.finrank`, from `Mathlib.LinearAlgebra.Dimension.Finrank`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and `pullback.map`; scheme pullbacks exist by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` and the existing module tensor/tensor powers.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, public imported as the recorded
  tensor dependency. The scheme tensor and Picard multiplication already use
  the same sheafification tensor supplied upstream.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionAdjunction`.
  On isomorphism classes, the existing `Pic.map` uses `Modules.pullback`.
  Both pullback functors are left adjoint to the same module pushforward, so
  left-adjoint uniqueness identifies their values. I also read the existing
  `Scheme.Modules.tensorOrdinaryPullbackIso` in
  `Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`; no comparison or
  pullback map is redeclared in this delivery. Scalar unit normalizations
  are immaterial for equality of line classes.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  the recorded `baseChange_morphism_projections` identifies `Over.pullback`'s
  map with h_K and its prescribed projections. `moduleBaseChange` itself is
  for varying the second factor; here the first factor Z varies, so the
  correct construction is `Over.pullback`'s map.
- `WeilConjectures.AlgebraicGeometry.PicardFunctor`: `Scheme.Pic`, `Pic.map`,
  `Pic.mk`, and the isomorphism-class equality interface.
- `WeilConjectures.AlgebraicGeometry.Picard.Group`: `Pic.instCommGroup`,
  `Pic.ofIsInvertible`, `Pic.mul_def`, `Pic.one_def`.

The already recorded nodes `def-sc-picard-group`, `lem-sc-pic-group`, and
`lem-pc-pic-presheaf-functorial` have been added to `stmt_deps` under the standing
permission to add landed statement dependencies. They record exactly the class,
group-law, and class-pullback interfaces used here. No new node or dependency
module is needed; only the item's `lean` and this additive dependency list change.

Proof dependencies with recorded modules are imported without `public` unless
already public statement dependencies: finite morphisms, matrix adjugate and
determinant, finite-upstairs trivialization, sheaf-module gluing, and invertible
pullback/tensor. Mathlib's open and affine fibre-product statements are supplied
by the already imported scheme pullback modules. The one currently unstated proof
dependency `lem-sfb-norm-frame-tensor-section-gluing` has no Lean module to import;
its role is recorded in the eight-step proof docstring. It is not needed to type
this statement, so it does not require a dependency module for this delivery.

Edge cases checked against the source and the actual signature:

- Empty Z or W is allowed. The empty scheme has its unique line class; there is
  no `Nonempty` hypothesis on schemes or covers.
- Degree one is allowed, including K = k. No strict inequality d > 1 occurs.
- Purely inseparable finite extensions in positive characteristic are allowed.
  The determinant base-change calculation is polynomial over any ring.
- Nonreduced schemes and arbitrary nonflat morphisms are allowed. No geometric
  condition on Z, W or h is introduced by `Over` or `Pic`.
- No finite-field-cardinality condition is imposed: k and K may be infinite
  fields, with only the extension finite-dimensional.
- Preservation of both tensor product and unit is a conclusion (`→*`), not an
  input assumption. The norm is existential; no noncanonical choice of an
  arbitrary map is used to define a purported canonical construction.

Searches for existing declarations:

- `msearch.py ... leanfinder`, query: "Norm on scheme Picard groups for a finite
  field extension commutes with arbitrary base change and sends a pulled back
  invertible module to its degree tensor power". Eight hits: `Algebra.intNormAux`,
  `prod_galRestrict_eq_norm`, finite-field element-norm formulas, and relative
  ideal-norm formulas. None is a norm on scheme Picard classes.
- `msearch.py ... loogle`, query: `"Pic", "norm"`. The service returned twelve
  unrelated normal-epimorphism-category declarations; no matching Picard norm.
- `msearch.py ... grep`, query: `Picard|Pic.*[Nn]orm|[Nn]orm.*Pic`, restricted
  to `AlgebraicGeometry`. Three Mathlib hits, all comments in elliptic-curve
  Weierstrass theory about rings with trivial Picard group; no scheme Picard norm.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, first for Picard/class definitions,
  then `Pic.*\bnorm\b|\bnorm\b.*Pic|Pic.*\bNorm\b|\bNorm\b.*Pic|finiteFieldNorm`:
  no norm declaration. One relevant comment in `FieldProductSquarePower.lean`
  cites this still-unstated node in a proof, not a Lean implementation.
- `rg` for the exact item id in `lean/WeilConjectures`: no match.
- Read `PicardFunctor.lean`, `Picard/Group.lean`, `Picard/Defs.lean` and the
  dependency files listed above. These give existing scheme Picard classes,
  the tensor-product group, and pullback, but no finite-extension norm.
- Read the records of `def-sc-picard-group`, `lem-sc-pic-group`, and
  `lem-pc-pic-presheaf-functorial` to reuse their landed interfaces.

Validation: `scompile.py Q19 lem-sfb-finite-field-picard-norm-base-change` compiled
both the sandbox and final library module successfully (4.5 s and 3.3 s). Both
implicit-variable options are disabled, and every line is at most 100 characters.
The theorem's proof is exactly `by sorry`.

## Second reading by Q19

I reread the source node and complete module after compilation. This is a worker
self-check; the dispatcher supplies the independent maintainer review. The field
and finite-extension hypotheses are precisely the four typeclass binders. The
norm family is outside both conjuncts, so the base-change identity uses the same
family, rather than separately chosen norms for each morphism. The source and
codomain of each norm are Picard groups of the actual chosen pullback and Z.
The first conjunct uses the first projection, not the projection to Spec K. The
second uses h_K from `Over.pullback` and reverses direction only when applying
Picard pullback. Multiplication and unit are both encoded by `MonoidHom`.
Quantification over classes preserves all invertible-module cases because every
class has an invertible representative and equality is isomorphism. No statement
mismatch or unresolved statement dispute was found. No source statement was
changed. The final report will include the delivery tool's validation result.

Delivery validation: `deliver2.py Q19 lem-sfb-finite-field-picard-norm-base-change
--no-push` printed `OK (dry run): commit 5545c91c743 passes the preflight and
compiles; nothing pushed`. The dry run staged exactly this report, the item's
node JSON, and its one Lean module.
