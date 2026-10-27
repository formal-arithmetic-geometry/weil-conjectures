## Worker report

The delivery states `AlgebraicGeometry.AffineClassComparison.affine_algebraClass_evaluation_comparison`.
Its sole proof is `sorry`. `Compatible` spells out the conclusion; the separate definition node
packages concrete canonical maps and their representative equations. All definitions contain real
terms. The theorem quantifies over a realization system with its normalization and proves existence
of such a system together with every comparison law, so none of these laws is an extra hypothesis.

Hypotheses and clauses:

- A commutative base ring is `(B : Type u) [CommRing B]`; an algebra is
  `(C : Type u) [CommRing C] [Algebra B C]`. `zeroComplex B (ModuleCat.of B C)` is C[0].
- `DerivedCategory.IsPseudoCoherent (zeroComplex B (ModuleCat.of B C))` and
  `(∃ t : ℤ, T.IsGE t)` are exactly the finite-free
  bounded-above representative and the vanishing below some integer. `invertible` and `localization_invertible`
  state invertibility for exactly E=C[0]. The naturality assertion uses arbitrary derived inputs as the node requests;
  this also follows the source's general K,L formulation in 0A6H(3)(a).
- `Realizations.F` and `factor` express termwise associated sheaf on derived objects.
  `tensor` and the `Normalized` conjuncts labeled `tensor_natural`,
  `totalTensor_normalized`, and `tensor_normalized` fix the tensor
  comparison by the pure-tensor ordinary map and its K-flat localization square. They do not
  substitute an unspecified isomorphism for that normalization.
- `hom` abbreviates the recorded ordinary module RHom. `sheafHom` uses the recorded ringed-site
  RHom. `evaluation` and `transpose` restore the tensor order used by the node, because
  Mathlib's closed structure takes E tensor RHom, whereas the node writes RHom tensor E.
- `gamma` is the actual evaluation transpose. `invertible` says that arrow is invertible,
  hence gives the requested canonical derived isomorphism; `evaluation_eq` states its evaluation
  equation. `naturality` quantifies over actual derived morphisms in both arguments.
- `algebraMultiplication` is ordinary multiplication followed by the lax localization
  tensorator and the degree-zero tensor identification. `classMap` transposes multiplication
  followed by xi. `sheafAlgebraMultiplication B C` is independently built from the actual
  ordinary sheaf-algebra product and the localization tensor map. `zeroRealization` identifies
  F(C[0]) with tilde C[0] through `s.factor` and the single-complex comparison.
  `sheafClassMap` transposes this transported sheaf product followed by F(xi).
  `class_eq` specializes E=C[0] and mu=algebraMultiplication B C, asserting gamma composed
  with realized m_xi equals that actual sheaf-algebra class map.
- `scalar_eq` records every B-scalar square. `algebraScalar` is ordinary multiplication by c,
  placed in degree zero; `algebraScalar_eq` is the precomposition square for every c in C.
  Naturality also includes scalar endomorphisms in the first argument.
- Affine opens use every ring map `φ : B →+* D` with
  `IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))`. The derived extension is the existing
  normalized `ModuleCat.ordinaryDerivedExtendScalars φ`, not an arbitrary functor.
- `rho` is a natural isomorphism of functors, the `pullbackTotal_normalized` conjunct pins its ordinary
  termwise map to the unit-normalized tilde/pullback map, and the `rho_normalized` conjunct uses the original
  recorded pullback counit. the `rho_tensor` conjunct gives tensor compatibility with a canonical monoidal
  pullback model, constrained by the `pullbackMonoidal_normalized` conjunct.
- `localization` is lambda, defined as the transpose of extended evaluation with the normalized
  scalar-extension tensorator. `localization_invertible` asserts invertibility under precisely
  the pseudo-coherent/bounded-below hypotheses and affine-open assumption.
- `openHom` is the evaluation-defined open restriction of RHom; `restriction_invertible`
  makes it the open-Hom isomorphism. `restriction_eq` gives the complete gamma/lambda/rho
  square with the contravariant inverse rho and covariant forward rho in its Hom target.
- `localization_class` gives lambda after extension of m_xi equals the multiplication transpose
  over D on the extended object. `zeroComparison` is the canonical counit map to the ordinary
  extended degree-zero module. `zero_invertible` justifies the identification with C_D[0].
  `baseChangedMultiplication` is actual multiplication of D tensor_B C, using φ.toAlgebra.
  `algebra_multiplication` identifies that multiplication, and `algebra_class` explicitly
  states the node's equality on C_D[0], including xi_D and all changes of source.
- The `extensionComp_normalized` conjunct fixes successive extension by the ordinary associator and
  counits; the `rho_comp` conjunct uses the original canonical derived pullback composition.
  `successive_localization` gives the successive lambda square. Combining this with
  `restriction_eq`, `localization_class`, and `algebra_class` gives the successive gamma and
  algebra-class diagrams, with their canonical composition identifications.

Dependencies used (read full signatures and docstrings):

- `WeilConjectures.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, `Qh`,
  `HasDerivedCategory`, the degree-zero single and localization comparison; TStructure: `IsGE`.
- `WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  `AlgebraicGeometry.exists_affineQCohDerivedEquivalence`, termwise tilde factorization.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: the recorded sheaf K-flat notions and
  public `CategoryTheory.MorphismProperty.kFlat`, used for ordinary module representatives.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, and public generic `derivedInternalHom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: `ordinaryDerivedExtendScalars`,
  its normalized monoidal structure, and the original universal-pair counit.
- `WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom`:
  `schemeDerivedTensorHomEquiv`, with its representative evaluation normalization.
- `WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition`:
  `recordedPullbackData`, its original counit and object equation,
  `recordedDerivedPullbackComposition`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel`:
  `IsDerivedPullbackMonoidalModel`; the shared scheme derived tensor is used throughout.
- `WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor`: `affine_tilde_tensor`.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`:
  `Scheme.Modules.exists_tensorPullback_tilde_iso`.
- The stated proof dependencies are imported privately, including the affine K-flat/total
  tensor lemmas, affine RHom quasi-coherence, ringed closed adjunction, flatness and exactness,
  open K-injective/Hom restriction, and derived pullback composition.

Edge cases checked: the zero ring and empty affine open are allowed; C need not be flat over B;
there is no perfectness, Noetherianity, finite-type or nonempty-spectrum hypothesis. T=0 and xi=0
are allowed, and the integer bound is arbitrary, not restricted to nonnegative values. Identity
ring maps and successive restrictions use the same representative maps. The site coefficient
universe stays u and the sheaf localization universe stays w, independent of the ordinary-module
small-Hom universe u; no equality between u and w is imposed. Quantification over all schemes
provides the existing localization convention also needed by the original pullback composition,
not an added geometric hypothesis.

Searches: msearch LeanFinder queried the affine derived Hom/evaluation/algebra-class/open
restriction statement (8 unrelated affine chart hits); LeanSearch queried affine derived Hom
localization (derived category and localization primitives, no exact statement); Loogle initially
reported unknown unqualified MonoidalClosed, then the qualified curry query returned the exact
Mathlib curry, injectivity and transpose identities. Mathlib grep for affine evaluation/algebra
classes returned only affine-map interpolation. The new definition node stores the further
LeanSearch, Loogle and Mathlib grep responses verbatim, plus the project/DAG searches. Direct rg
in WeilConjectures, Sheaf and dag/lean_names_upstream.json found no AffineClassComparison system
or exact theorem. The surrounding `relativeDualizingAffineTilde` defines just the affine functor,
and its specialized diagonal multiplication differs from the general C[0] construction here.
No existing dependency record needed replacement. No statement correction or disputed statement.

## New nodes

`def-trf-affine-algebra-class-comparison-data` defines the canonical comparison system and the
actual evaluation/multiplication transposes used by this theorem. Its source is the affine
computations of Stacks 06Z0, 08DW, 08DX and 0A6H, normalized by 01I8/01I9 and 08J9, with the
multiplication interpretation of 0E2U. The node cites every recorded constituent it uses. Searches
found the component constructions but no node or declaration supplying this complete normalized
system. No new existence theorem is hidden in a definition: the sole existence assertion is the
assigned item's theorem. All maps are real constructions or fields constrained by explicit
representative equations.

## Second reading by Q61

I reread the node beside both files in a separate self-audit; no second agent was started, as the
worker brief forbids delegation. The maintainer supplies the independent delivery review.
I checked the evaluation tensor order and inserted the canonical derived braiding explicitly;
checked rho's source/target and its inverse in the contravariant Hom argument; checked that
lambda's class equation includes the ordinary base-changed algebra and the nonflat-source
multiplication; checked the common u,w convention and retained the original pullback counits.
The degree-zero identification was expanded to `zeroComparison`, `zero_invertible`,
`algebra_multiplication`, and `algebra_class` so the ordinary C_D[0] clause is explicit.
The composition clauses specify the ordinary associator normalization, rather than only
asserting abstract isomorphisms. All module and declaration docstrings identify the owning node;
only the named theorem has `sorry`. No clause is replaced by equality of independently chosen
isomorphisms. Compilation and delivery preflight are recorded by the prescribed wrappers.
Profiling found unnecessary generated structure helper declarations expensive; size/injectivity
helper generation is disabled for the comparison-data record without altering its data.

The data-only `Realizations` record has a separate conjunction `Normalized` for all
of representative, tensor and successive-restriction equations; `Compatible.normalized`
requires precisely these equations. This avoids generating expensive recursors over
large dependent proof fields and does not omit any normalization.

Elaboration checks also specify both source and target product objects explicitly for
contravariant RHom maps. The inverse degree-zero comparison maps C_D[0] back to
L(C[0]) before precomposition, while the covariant target comparison goes forward.

The previous validation concerned the returned head. The repair is recompiled and
preflighted by the prescribed wrappers; only the named main theorem is postponed.

## Repair of returned head 6efd92ff7f15

The maintainer's H3 finding was correct: the earlier sheafClassMap was defined using
s.tensor followed by F(mu), so class_eq merely expressed functoriality of transposition.
It did not identify realized module multiplication with the actual sheaf-algebra product.

1. `ordinaryTensorIso` is the same uniquely pure-tensor-normalized ordinary tilde map,
   packaged with its existing IsIso proof. `sheafAlgebraMultiplication B C` uses its inverse
   followed by tilde of `LinearMap.mul' B C`, placed in degree zero and preceded by
   `pullbackTensorModelMap`. It contains no realization system, F or s.tensor.
2. `sheafZeroComplex` is actual tilde C[0]. `zeroRealization` is s.factor followed by the
   natural single/termwise-tilde comparison. `sheafClassMap` transports the independent
   sheaf multiplication through this isomorphism, follows by F(xi), and transposes.
3. `Compatible.class_eq` now takes B,C,T,xi and fixes E=C[0] and
   mu=algebraMultiplication B C. Its right side is the actual sheaf product transpose.
   This preserves the nontrivial comparison needed to match relativeDualizingClassMap
   in parent lem-trf-affine-relative-dualizing-comparison step 4.
4. The definition node now describes this independent ordinary and derived sheaf product
   and its transport. Declaration docstrings and theorem proof step 5 explicitly include
   the pure-tensor multiplication comparison. The original item's TeX is unchanged.

I compared the retained packet with the current read clone: the original item still has
no landed Lean record there; the retained node differs only by the permitted lean record
and added definition dependency. The prescribed source lookup reports the returned data
module unavailable on current main. Delivery wrappers refresh and base the repaired packet
on current sheaf-dag. No live source or repository Git state is edited directly.

Second reading of the repair: the right side of class_eq has no use of s.tensor or F(mu).
Only zeroRealization uses s.factor; the product itself is fixed by ordinary multiplication.
For C nonflat over B, the derived-to-ordinary product still uses the lax localization arrow,
so no flatness assumption was introduced. The zero-ring, empty-open, T=0 and xi=0 cases
remain admitted. All other comparison, scalar and successive-restriction clauses remain.

The normalization conditions are retained as an explicit conjunction in `Normalized`,
avoiding generated record eliminators; `Compatible.normalized` requires the entire conjunction.
The termwise tilde functor retains its original definition. The algebra-specific actual sheaf
product, degree-zero realization and class transpose are declarations in the item's theorem
module, listed in its lean.declarations and carrying its blueprint tag. The definition node's
text specifies this independent-product convention; its module holds the general realization
system and module class transpose. No new module or independent node is needed for this repair.

Repair validation: scompile.py returned success for both complete modules, with no errors
or unexpected warnings. The theorem-module library check completed in 18.6 seconds;
the wrapper also successfully checked the sandbox module and the comparison-data overlay.
Only the main named theorem is sorry; every new helper definition contains actual data.
