## Worker report

The module `Sheaf.AlgebraicGeometry.StandardGroupSchemes` formalizes the complete
node `def-sc-gm-ga`. Its namespace is
`AlgebraicGeometry.StandardGroupSchemes`. The four affine schemes, all coordinate
maps and both inclusion morphisms have concrete definitions. The module has
46 declarations; the node's `lean.declarations` enumerates them all. No other DAG
node is stated or changed, and no new independent notion is introduced.

The source read was the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/def-sc-gm-ga.md`,
the node's expanded proof, Stacks `groupoids.tex` examples
`example-multiplicative-group` (022U), `example-additive-group` (022V),
`example-roots-of-unity` (040M), and `varieties.tex`
`definition-relative-frobenius` (0CC9). There is no statement correction or dispute.

Clause-by-clause correspondence (all names below are in the namespace above):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Let k be a field | `universe u`; `variable (k : Type u) [Field k]`. No closure, finiteness, perfectness or characteristic restriction is put on k. |
| Affine spectra and their contravariant morphisms | `affine k A` is `(algSpec (.of k)).obj (op (CommAlgCat.of k A))`; `map k f` is that very functor applied to `CommAlgCat.ofHom f`. These helpers only specialize the existing functor to the coordinate presentations. |
| Commutative k-algebra tensor product and its usual multiplication | The actual Mathlib `A ⊗[k] A`, pure tensors `⊗ₜ[k]`, and its commutative algebra instances; `multiplication` uses the canonical monoidal affine-product comparison from `braidedAlgSpec`. |
| G_m = Spec k[t,t^-1] | `multiplicative k = affine k (LaurentPolynomial k)`. |
| Multiplicative comultiplication t ↦ t⊗t, counit t ↦ 1, inverse t ↦ t^-1 | `multiplicativeGroup` uses the existing `GrpObj` of Spec of the Laurent Hopf algebra. In the exact imported Mathlib source, `LaurentPolynomial.instHopfAlgebra`, its inherited `instBialgebra`, `comul_T`, `counit_T`, and `antipode_T` give precisely these values. No second Laurent Hopf algebra is defined. |
| G_a = Spec k[y] | `additive k = affine k (Polynomial k)`. |
| Additive comultiplication y ↦ y⊗1+1⊗y | `additiveComul k := Polynomial.aeval (Polynomial.X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Polynomial.X)`. |
| Additive counit y ↦ 0 and inverse y ↦ -y | `additiveCounit := Polynomial.aeval 0`; `additiveAntipode := Polynomial.aeval (-Polynomial.X)`. |
| These maps give the additive group structure | `additiveGroup_existsUnique` specifies all three fields `h.one`, `h.mul`, `h.inv` as the canonical spectrum maps of the preceding algebra maps. `additiveGroup` selects that uniquely specified structure. |
| n ≥ 1 | The μ_n group structure, Laurent quotient and inclusion have `(n : ℕ) [NeZero n]`, equivalent to n ≥ 1 for natural numbers. |
| μ_n = Spec k[t]/(t^n-1) | `rootsIdeal k n := Ideal.span {Polynomial.X ^ n - 1}`; `rootsAlgebra` is the actual ideal quotient; `roots k n := affine k (rootsAlgebra k n)`. |
| μ_n is a subgroup of G_m via the coordinate quotient | `rootsCoordinateUnit` has value the class of X and inverse its (n-1)-st power; `rootsQuotient` is `LaurentPolynomial.eval₂` with this unit and the k-algebra coefficient map; `rootsInclusion` is its contravariant Spec map. The coordinate ring is the polynomial quotient in the node, not a Laurent quotient substituted for it. |
| The quotient inclusion is a closed subgroup inclusion | `roots_isClosedSubgroupScheme` uses the dependency's exact `IsClosedSubgroupScheme`. The group law is fixed by `rootsComul`, `rootsCounit`, `rootsAntipode`, with coordinate images x⊗x, 1, x^(n-1). `rootsRelations` supplies only the ideal-killing proofs for the actual `Ideal.Quotient.liftₐ` construction. |
| char k = p > 0 | The α_p group law, closed subgroup and kernel theorems have `(p : ℕ) [NeZero p] [CharP k p]`. Primality follows from k being a field; it is not a separately imposed assumption. |
| α_p = Spec k[y]/(y^p) | `alphaIdeal k p := Ideal.span {Polynomial.X ^ p}`; `alphaAlgebra` is the actual quotient; `alpha k p := affine k (alphaAlgebra k p)`. |
| α_p is a closed subgroup of G_a by the displayed quotient surjection | `alphaQuotient` is `Ideal.Quotient.mkₐ k (alphaIdeal k p)`; `alphaInclusion` is its Spec map; `alpha_isClosedSubgroupScheme` states the exact recorded closed subgroup predicate. `alphaComul`, `alphaCounit`, `alphaAntipode` have images ybar⊗1+1⊗ybar, 0, -ybar. |
| Both coordinate maps are surjections | `quotient_surjective` asserts `Function.Surjective` for each actual quotient map. The closed subgroup predicate includes the dependency's `IsClosedImmersion` on the underlying scheme morphism. |
| F:G_a→G_a has k-algebra coordinate map z ↦ y^p fixing k | `frobeniusCoordinates k p := Polynomial.aeval (Polynomial.X ^ p)` is an actual k-algebra homomorphism; `frobenius k p` is its canonical spectrum morphism. `frobenius_isMonHom` records compatibility with the additive group laws. |
| α_p is the kernel in the recorded group-scheme sense | `alpha_isFrobeniusKernel` gives an isomorphism from this specific quotient scheme to `GrpObj.ker (frobenius k p)` and the equation `e.hom ≫ GrpObj.kerι ... = alphaInclusion k p`. Thus it identifies the specified subgroup inclusion as well as the underlying scheme. |
| Relative, rather than absolute, Frobenius | The coefficient-fixing `Polynomial.aeval` map is precisely the node's coordinate identification of the target twist with the affine line. No claim that absolute Frobenius fixes k is used. The source and final kernel proof docstring explain the tensor presentation without assuming k perfect. |

Definitions and postponed proofs:

- All scheme and algebra data are explicit `Spec`, polynomial/Laurent substitutions,
  quotients, tensor comparisons and quotient lifts. The unit for Laurent substitution
  explicitly has inverse x^(n-1).
- `additiveGroup`, `rootsGroup`, and `alphaGroup` use the unique-existence theorem
  immediately preceding each. These statements fix EVERY group data field: identity,
  multiplication and inverse. Thus the group object is determined up to equality;
  this is the allowance in AGENTS.md §5 for data selected from a theorem determining
  the object, not a choice from a mere `Nonempty` assertion. No unspecified group law,
  coordinate map or inclusion is chosen. Proof irrelevance gives uniqueness once
  the operations are fixed.
- The twelve postponed theorems are `additiveGroup_existsUnique`, `rootsRelations`,
  `rootsGroup_existsUnique`, `alphaRelations`, `alphaGroup_existsUnique`,
  `rootsCoordinate_inverse`, `rootsLaurent_commutes`, `quotient_surjective`,
  `roots_isClosedSubgroupScheme`, `alpha_isClosedSubgroupScheme`,
  `frobenius_isMonHom`, and `alpha_isFrobeniusKernel`. Each verifies a clause or
  construction in THIS definition node, has `(blueprint: def-sc-gm-ga)` and its
  natural-language proof in its docstring, and has proof exactly `by sorry`.
  Nothing is proved in this stage.

Dependency declarations inspected and used:

| Dependency | Exact declaration and module |
| --- | --- |
| `def-weil-field` (mathlib leaf) | `Field`, `Mathlib.Algebra.Field.Defs`. |
| `def-weil-affine-spectrum` | `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`; their k-algebra specialization is `algSpec`, `Mathlib.AlgebraicGeometry.Group.Affine`. |
| `def-weil-polynomial-ring` | `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`; canonical substitutions `Polynomial.aeval`, `Mathlib.Algebra.Polynomial.AlgebraMap`. |
| `def-weil-laurent-polynomial-ring` (mathlib leaf) | `LaurentPolynomial`, `Polynomial.toLaurent`, `LaurentPolynomial.T`, `LaurentPolynomial.eval₂`, `Mathlib.Algebra.Polynomial.Laurent`. This item needs the exact abstract Laurent ring, not its optional rational-function realization. |
| `def-weil-pbc-algebra-hom-quotient` (mathlib leaf) | `AlgHom`, `Mathlib.Algebra.Algebra.Hom`; `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`, `Ideal.Quotient.liftₐ`, `Mathlib.RingTheory.Ideal.Quotient.Operations`. |
| `lem-weil-pbc-algebra-tensor-pushout-universal-property` (mathlib leaf) | `Algebra.TensorProduct.instCommRing`, `instAlgebra`, `tmul_mul_tmul`, `includeLeft`, `includeRight`, `ext`, `Mathlib.RingTheory.TensorProduct.Basic`; `productMap`, `productMap_apply_tmul`, `productMap_left`, `productMap_right`, `Mathlib.RingTheory.TensorProduct.Maps`. The statements and universal-property implementation were read, and these are the tensor algebra structures used in the coordinate formulas. |
| `def-sc-group-scheme` | `CategoryTheory.GrpObj` and its actual three data fields, `Mathlib.CategoryTheory.Monoidal.Grp` (which imports the monoid fields); `IsMonHom`, `Mathlib.CategoryTheory.Monoidal.Mon`; `GrpObj.ker`, `GrpObj.kerι`, `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`. The group-scheme dependency explicitly documents this specialization in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. |
| `def-sc-group-scheme-subgroup` | `AlgebraicGeometry.IsClosedSubgroupScheme`, extending the exact `IsSubgroupScheme` with injectivity on all algebra points and a closed immersion, `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. |
| `def-weil-closed-immersion` | `AlgebraicGeometry.IsClosedImmersion`, `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`. |
| Proof dependency `lem-weil-pbc-fibre-product-affine-spectra` | `AlgebraicGeometry.pullbackSpecIso`, `Mathlib.AlgebraicGeometry.Pullbacks`, used by the canonical `braidedAlgSpec` multiplication comparison. |
| Proof dependency `def-weil-ring-frobenius` | `frobenius`, `iterateFrobenius` and naturality, `Mathlib.Algebra.CharP.Frobenius` (imported for the proof stage). The coefficient-fixing relative coordinate map here is an aeval, not the absolute Frobenius of the polynomial ring. |

Edge cases checked before writing:

- n=1 is included: the class of X equals 1, the inverse formula x^(n-1)=x^0=1
  is correct, and μ_1 is the trivial subgroup.
- n=0 is outside the node's μ_n clause, so no group law or inclusion is asserted
  at n=0. The underlying quotient algebra may still be formed.
- No primality-to-characteristic restriction is imposed on n: p dividing n is
  allowed. The quotient retains nilpotents, so μ_p is not silently replaced by
  its points or reduced subscheme.
- Characteristic two is included; the alpha inverse is -y=y there. Positive
  characteristic comes from the pair `NeZero p`, `CharP k p`; characteristic zero
  does not supply that pair.
- Imperfect fields are included. The Frobenius coordinate map fixes coefficients
  by its AlgHom type; it does not use an inverse Frobenius on k. The kernel uses
  the tensor-product quotient calculation and retains all nilpotents.
- The point tests in the recorded subgroup predicate include arbitrary
  commutative k-algebras, including nonreduced ones. No reducedness assumption
  or field-only point test appears.
- u is arbitrary, and all coordinate algebras remain in `Type u`; no independent
  smaller universe is introduced for test algebras.

Searches made for the existing notion:

- `msearch.py leansearch`: "Multiplicative and additive group schemes Laurent
  polynomial Spec and polynomial Spec roots of unity Frobenius kernel" returned
  eight results, including `AffineScheme`, root-of-unity element predicates and
  polynomial Frobenius identities, but no definition of these four group schemes.
- `msearch.py leanfinder`: "Multiplicative and additive affine group schemes with
  finite subgroup schemes roots of unity and alpha p" returned eight results,
  including `AffineSpace`, root data and cyclotomic characters, but no match.
- `msearch.py loogle`: `LaurentPolynomial.instHopfAlgebra` returned the exact
  Laurent Hopf algebra instance, which is reused. An earlier broad query
  `LaurentPolynomial, Polynomial, TensorProduct, IsGroupScheme` had no hits and
  reported that `IsGroupScheme` is not a known identifier; the actual group
  notion was then located and read as `GrpObj`.
- `msearch.py grep` in `AlgebraicGeometry` for
  `multiplicativeGroup|additiveGroup|rootsOfUnity|FrobeniusKernel` returned no hits;
  the earlier `LaurentPolynomial|IsGroupScheme|IsSubgroupScheme` query also had none.
- Direct `rg` in Mathlib located and read the Laurent Hopf and bialgebra
  implementations, the affine-group functor and all dependency interfaces.
  A search for Polynomial Hopf instances found none for the additive polynomial
  comultiplication (the symmetric algebra material is a different carrier).
- Direct `rg` in `WeilConjectures/` and `lean/Sheaf/` for the group scheme names,
  root-of-unity/Frobenius-kernel terminology and Laurent/Polynomial Hopf instances
  found subgroup predicates, étale G_m and μ_n sheaves, Kummer computations,
  and affine-line material, but no exact scheme definitions for this node.
  The source's `EtaleCohomology/Purity/Smooth/AffineLine.lean` explicitly says
  G_m is carried as an open-complement datum there, not a Mathlib scheme.
- `rg` for `def-sc-gm-ga` in upstream `WeilConjectures/` found no declaration;
  `dag/lean_names_upstream.json` has no StandardGroupSchemes declarations.
  These are new owning-node constructions, not duplicates of the sheaf notions.

Validation: `scompile.py NY def-sc-gm-ga .../StandardGroupSchemes.lean` compiled
both the sandbox and library forms cleanly. The prescribed delivery dry run is
run after the final file and node record are written; its exact outcome is saved
in `dryrun.log` in this sandbox. No push or independent second-reading section
is supplied by the worker.

## Second reading by NY

I independently opened the item JSON, the complete delivered module, every
statement-dependency node and its recorded interface, the current blueprint
definition and proof, and the Stacks source paragraphs. No repair note exists
for this item. There is one module, no new node, no dependency repair module,
and no statement_change requiring a citer audit.

My list of the mathematical data, hypotheses and clauses, with their Lean
counterparts (names are in `AlgebraicGeometry.StandardGroupSchemes`):

| Item read from the node | Lean rendering and verdict |
| --- | --- |
| An arbitrary field k | `variable (k : Type u) [Field k]`, with arbitrary `u`. Exact; no algebraic closure, perfectness, finiteness or characteristic restriction. |
| Affine spectra, contravariant coordinate maps and products over k | `affine` and `map` specialize Mathlib's `algSpec (.of k)`; `multiplication` uses its canonical lax monoidal comparison; `identitySection` uses its unit comparison. Exact: I read `algSpec_obj_hom`, `algSpec_map_left`, `braidedAlgSpec`, `μ_algSpec_left`, and `pullbackSpecIso` to check the orientation and the product identification. |
| G_m = Spec k[t,t^-1] | `multiplicative` uses the actual `LaurentPolynomial k`. Exact; the dependency records this abstract Laurent ring as its ring realization, and this item needs no embedding into rational functions. |
| Multiplicative operations t ↦ t⊗t, 1, t^-1 | `multiplicativeGroup` reuses `instGrpObjSpecAsOverSpec` for the Laurent Hopf algebra. Exact: I read its bialgebra/monoid component and the Hopf functor, plus `LaurentPolynomial.comul_T`, `counit_T`, `antipode_T`. At exponent 1 these give exactly the three specified maps. |
| G_a = Spec k[y] | `additive := affine k (Polynomial k)`. Exact. |
| Additive operations y ↦ y⊗1+1⊗y, 0, -y | `additiveComul`, `additiveCounit`, `additiveAntipode` are the three `Polynomial.aeval` maps. `additiveGroup_existsUnique` fixes `one`, `mul`, `inv` to their spectra and `additiveGroup` chooses that uniquely specified structure. Exact. |
| n ≥ 1 and μ_n = Spec k[t]/(t^n-1) | `(n : ℕ) [NeZero n]` on the structure and inclusion; `rootsIdeal`, `rootsAlgebra`, `roots`. Exact: nonzero naturals are precisely the positive naturals. No condition on whether the characteristic divides n. |
| The quotient μ_n → G_m | `rootsCoordinateUnit` has the residue of X as value and its (n-1)-st power as inverse. `rootsQuotient` evaluates Laurent polynomials at this explicit unit and `rootsInclusion` applies `map`. Exact canonical coordinate quotient, with the polynomial quotient as target. |
| The induced roots-of-unity group operations | `rootsComul`, `rootsCounit`, `rootsAntipode` descend x⊗x, 1, x^(n-1) via `Ideal.Quotient.liftₐ`; `rootsRelations` only supplies the vanishing proofs. `rootsGroup_existsUnique` fixes all group data. Exact. |
| char k = p > 0 and α_p = Spec k[y]/(y^p) | `(p : ℕ) [NeZero p] [CharP k p]`; `alphaIdeal`, `alphaAlgebra`, `alpha`. Exact: in a field positive characteristic is prime, so no extra primality or perfectness hypothesis is needed. |
| The quotient α_p → G_a | `alphaQuotient` is `Ideal.Quotient.mkₐ`; `alphaInclusion` is its Spec map. Exact. |
| The induced additive structure on α_p | `alphaComul`, `alphaCounit`, `alphaAntipode` descend ybar⊗1+1⊗ybar, 0, -ybar. `alphaRelations` states exactly the well-definedness; `alphaGroup_existsUnique` fixes the three operations. Exact in characteristic p. |
| Both coordinate maps are surjective | `quotient_surjective` asserts surjectivity of the actual `rootsQuotient` and `alphaQuotient`. Exact; the latter holds for every exponent, so its lack of a characteristic binder is appropriate. |
| Both inclusions are closed subgroup schemes | `roots_isClosedSubgroupScheme` and `alpha_isClosedSubgroupScheme` use the recorded `AlgebraicGeometry.IsClosedSubgroupScheme`. Exact: I read its extension of `IsSubgroupScheme`, `IsMonHom`, its arbitrary-algebra injectivity test, and `IsClosedImmersion i.left`. No field-points-only substitute is used. |
| F is the coefficient-fixing group map z ↦ y^p | `frobeniusCoordinates` is `Polynomial.aeval (Polynomial.X ^ p)`; `frobenius` applies Spec; `frobenius_isMonHom` states the homomorphism property in positive characteristic. Exact. |
| α_p is the scheme-theoretic kernel, with this inclusion | `alpha_isFrobeniusKernel` supplies `e : alpha k p ≅ GrpObj.ker (frobenius k p)` and `e.hom ≫ GrpObj.kerι ... = alphaInclusion k p`. Exact: I read `GrpObj.ker` as the pullback against the target's unit, and `kerι` as its first projection. Together with the subgroup theorem and the homomorphism theorem this identifies the specified subgroup, not merely an abstract isomorphic scheme. |
| F is relative Frobenius in the coordinate identification | The AlgHom fixes k and sends X to X^p; this is precisely the convention explicitly given in the node. Exact over imperfect fields as well; the source's twist is the base change along Frobenius of k, not an assertion that absolute Frobenius fixes k. |

Source checks: Stacks `groupoids.tex`, `example-multiplicative-group`
(022U), `example-additive-group` (022V), and `example-roots-of-unity`
(040M) give these coordinate formulas over Z and their base changes to any
base scheme. The node deliberately specifies n≥1. Stacks `varieties.tex`,
`definition-relative-frobenius` (0CC9), assumes a prime p and a base of
characteristic p; the present field hypotheses imply those conditions.
The twist calculation in the node uses the balancing relation
ac⊗b=a⊗c^p b and is valid without surjectivity of Frobenius on k.

Dependency review: I opened `GrpObj`/`MonObj` and confirmed their only data
fields are `one`, `mul`, `inv`; their other fields are laws in Prop. The
three unique-existence choices therefore determine their objects up to
equality and satisfy the no-hollow-data rule. All coordinate data and unit
data are explicit. I also read the actual signatures of `Spec`, `Spec.map`,
`Polynomial`, `LaurentPolynomial`, `Polynomial.aeval`, the quotient lifts,
the algebra tensor inclusions/productMap/ext, `IsClosedImmersion`, and the
affine product isomorphism. These are the dependency notions, not private
versions. Every postponed theorem belongs to a verification in this same
definition node, has proof exactly `by sorry`, and has a source/proof
docstring; no theorem has been proved in stage 2.

Edge cases: n=1 yields inverse x^0=1 and the trivial μ_1; n=0 is excluded
only where the node excludes it. All characteristics are allowed for G_m,
G_a and μ_n, including characteristic dividing n, with nilpotents retained.
For α_p, p=0 is excluded and p=1 is impossible for a field with CharP k p;
characteristic two and imperfect fields are included. The quotient algebras
are not reduced by construction. Test algebras in the subgroup predicate
include the zero ring, hence empty affine test schemes; there is no
Nontrivial R condition. No independent scheme or index family is quantified
here, so an empty index family or arbitrary empty base scheme is not an
omitted case. All constructions live in the arbitrary universe of k; no
extra equality or smaller test-algebra universe is imposed.

Independent duplicate searches, using different terminology from the worker:

- LeanSearch: `Affine line group object from primitive polynomial generator
  and finite infinitesimal subgroup` returned eight unrelated algebraic or
  affine-equivalence results, no match.
- Loogle: `Polynomial, Coalgebra` returned zero results.
- LeanFinder: `Spec of the quotient by X^p is the kernel of the additive power
  map in characteristic p` returned perfect-closure and polynomial-root
  results, no group-scheme or kernel construction.
- Direct rg on Mathlib, upstream WeilConjectures, and this project's
  lean/Sheaf searched `primitive.*polynomial`, `polynomial.*(hopf|bialgebra)`,
  `frobenius.?kernel`, `roots.?of.?unity.*scheme`, `multiplicative.?group.?scheme`,
  `additive.?group.?scheme`, and `StandardGroupSchemes`. The Laurent Hopf
  structure is reused. I followed the upstream hit in
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`: its `zeroSection`,
  `neg`, `add` are maps on relative affine space, with no GrpObj instance or
  polynomial-spectrum group/subgroup declaration for this item. Existing
  roots-of-unity sheaves are sheaves, not these affine group schemes.
  The upstream name index contains no owning declarations for this node.

Mismatch and repair: the final theorem's docstring supplied the kernel
tensor-product calculation but omitted the last part of the node's proof,
the explicit isomorphism from the Frobenius twist to k[z]. I appended the
two coordinate maps, their balancing-relation inverse check, the additive
compatibility and the resulting relative Frobenius substitution (H8).
No mathematical signature, definition, node statement or dependency changed.
The recorded `lean.statement` remains `def multiplicative : Over (Spec (.of k))`,
verbatim equal to the delivery parser's signature. All variables and universe
parameters are bound; no local notation or local instance enters a statement.

Validation: the prescribed scompile.py compiled the final sandbox and library
forms cleanly, in 8.5 and 9.2 seconds respectively, without warnings.
