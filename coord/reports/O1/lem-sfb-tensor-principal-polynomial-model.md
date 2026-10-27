## Worker report

Stage 2, group O1, 2026-10-23. The delivery states
`AlgebraicGeometry.TensorPrincipalPolynomialModel.exists_model` in
`Sheaf.AlgebraicGeometry.TensorPrincipalPolynomialModel`. Its only theorem proof is
`sorry`. Three helpers in the same namespace have actual construction data:
`coefficientMap` is `MvPolynomial.map`, `specialization` is `MvPolynomial.eval₂Hom`,
and `linearPolynomial` is the displayed finite sum. They belong to the assigned
node's explicitly specified construction, and are all listed in `lean.declarations`;
there are no new nodes or repaired dependency modules.

The inherited ending concerned a stage-1 unchanged-split delivery. The live node
has the accepted Q128 split but no `lean` field, and `coord/queue.tsv` lists it in
stage 2. The handoff rule at the beginning of `coord/brief-stage2.md` explicitly
allows recording its Lean statement. No accepted split, statement, dependency,
source or review field is changed: only `lean` is added.

Hypothesis and clause correspondence, reading the node and final file together:

- The commutative ring A and commutative A-algebras B,C are exactly
  `(A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
  [Algebra A C]`. No finiteness, flatness, nonzero, reducedness, or field hypothesis
  is present. A common ambient universe is used for the rings and affine schemes;
  it can be enlarged for any given collection of rings. `autoImplicit` is false.
- D is Mathlib's `B ⊗[A] C`, with its standard commutative-ring instance from
  `Mathlib.RingTheory.TensorProduct.Basic`. Its multiplication on pure tensors is
  `Algebra.TensorProduct.tmul_mul_tmul`, and its unit is `1 ⊗ₜ[A] 1` (`one_def`).
  No second module tensor product or tensor-ring structure is defined.
- j is the actual canonical ring map
  `(Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C)`, whose value is
  `b ⊗ₜ[A] 1`. It is used in the ring square, universal property, scheme square
  and image identity.
- The index n and families are `∃ (n : ℕ) (b : Fin n → B) (c : Fin n → C)`;
  nonnegativity is built into ℕ. `Fin n` indexes the node's list 1,...,n without
  imposing n>0. The first conjunct is `g = ∑ i, b i ⊗ₜ[A] c i`.
- R and S are `MvPolynomial (Fin n) A` and `MvPolynomial (Fin n) C` throughout.
  They are not existentially chosen algebras or unspecified polynomial models.
- The coefficient map phi_n is `coefficientMap A C n`, definitionally
  `MvPolynomial.map (algebraMap A C)`; h is `linearPolynomial c`, definitionally
  `∑ i, MvPolynomial.C (c i) * MvPolynomial.X i`.
- e is `(MvPolynomial.aeval b).toRingHom`, the evaluation extending A→B. k is
  `specialization (A := A) (C := C) b`, defined by `eval₂Hom` with coefficient
  map `Algebra.TensorProduct.includeRight.toRingHom` and variable values
  `b i ⊗ₜ[A] (1 : C)`. Thus its constants really go to `1 ⊗ₜ[A] c`.
- The second conjunct states `specialization ... (linearPolynomial c) = g`.
  The third is the equality of ring-hom composites `k.comp phi_n = j.comp e`.
- The pushout clause quantifies over `(E : Type (max u v)) [CommRing E]`, arbitrary
  `u : S →+* E`, `v : B →+* E` and precisely the compatibility
  `u.comp phi_n = v.comp e`. The independent universe v permits arbitrary large
  test rings; `max u v` avoids an accidentally undersized test universe. No
  A-algebra structure on E is assumed. The conclusion is `∃! w : D →+* E` with
  `w.comp k = u`, `w.comp j = v`, and
  `∀ (x : B) (y : C), w (x ⊗ₜ[A] y) = v x * u (MvPolynomial.C y)`.
  The node's u(c) is the restriction to constant polynomials. The formula is
  included in the predicate of `∃!`; it is also forced by the two composites,
  because x⊗y=j(x)k(C(y)). Thus the uniqueness has exactly the ring-pushout meaning.
- The cartesian square is the actual `CategoryTheory.IsPullback` with ordered
  arrows `Spec.map k`, `Spec.map j`, `Spec.map phi_n`, `Spec.map e`, each ring
  map bundled by `CommRingCat.ofHom`. This is a square of schemes, not just a
  pullback of their point sets, nor an unspecified isomorphism.
- D_H(a) is the existing `PrimeSpectrum.basicOpen a`, coerced to a set of prime
  ideals. Its definition is exactly `{p | a ∉ p.asIdeal}`. The penultimate
  conjunct is `(Spec.map k).base ⁻¹' D_S(h) = D_D(g)`.
- The last conjunct is `(Spec.map j).base '' D_D(g) =
  (Spec.map e).base ⁻¹' ((Spec.map phi_n).base '' D_S(h))`.
  These are the alpha,q,beta,f_n of the node with the correct contravariant
  directions. Set images and inverse images are explicit, with no openness
  assumption substituted for the required equality.

Dependencies read and used, including their signatures and docstrings:

- def-weil-pbc-module-tensor-product: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, and `TensorProduct.ext'` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic`; imported through
  `Mathlib.RingTheory.TensorProduct.Basic`. The latter supplies the multiplication,
  commutative ring and both canonical inclusions of the SAME tensor product.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` and `Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`, as recorded by its existing Lean attachment.
  Read `PrimeSpectrum.comap` in `RingTheory/Spectrum/Prime/RingHom.lean` and
  `PrimeSpectrum.basicOpen` in `.../Topology.lean` for the point-set interpretation.
- def-weil-pbc-mv-polynomial-ring: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`; `MvPolynomial.aeval` and `eval₂Hom` and
  coefficientwise `map` in `.Eval`; `MvPolynomial.algHom_ext` in `.Basic`.
  The module publicly imports `.Eval`, which exposes `.Basic`.
- def-pc-fibre-product: recorded `CategoryTheory.Limits.pullback`, its projections
  and universal map in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  the equivalent universal-square interface `CategoryTheory.IsPullback` is used
  from `...Pullback.IsPullback.Defs`. It includes commutativity and the limit
  property of the specified cone. The plain proof import `.Pullbacks` also loads
  the chosen scheme pullbacks from the dependency's Mathlib match.
- Proof-only dependencies: `AlgebraicGeometry.pullbackSpecIso` and its projection
  formulas in `Mathlib.AlgebraicGeometry.Pullbacks`, and
  `AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback` in
  `Mathlib.AlgebraicGeometry.PullbackCarrier`. Both modules are plain imports,
  as prescribed for proof dependencies. The theorem docstring gives all seven
  steps of the accepted natural-language proof and the corresponding node ids.

Source and edge cases:

Read the affine paragraph of Stacks Tag 0F31 in `more-morphisms.tex:21755-21784`.
Stacks A' is our B, Stacks B is our C: variables are specialized into B and the
linear polynomial has C coefficients. No surrounding openness condition is a
hypothesis of this algebraic construction. The node isolates the construction
used inside that argument, not the larger contradiction argument.

For n=0, `Fin 0` is empty, the sum and h are 0, and MvPolynomial has no variables.
For g=0 that empty expansion is permitted; both principal opens are empty and both
set identities hold. Zero rings and zero tensor products are allowed because all
structures are CommRing rather than Nontrivial/IsDomain, and their spectra are
empty. With A=B=ℤ and C=ℤ[x], g=1⊗x, n=1, b=1 and c=x gives h=x*t and the displayed
square and images have the specified directions. With C=A, k is evaluation into
B⊗_A A and the image equality reduces to pullback of the same principal open.
The universal target E has only a commutative-ring assumption: its common
A-algebra structure is deduced in the proof from compatibility, not smuggled
into the statement. No source or statement correction, dispute, or node fault
was found.

Searches actually executed with msearch.py for this group and item:

- LeanFinder: “Every element of a tensor product of commutative algebras is a
  finite linear polynomial specialization whose evaluation square is a pushout
  and gives the base change identity for principal open images”. Eight hits:
  standard open immersion base change, exists_fg_and_mem_baseChange,
  SurjectiveOnStalks.exists_mul_eq_tmul, CommRingCat.isPushout_tensorProduct,
  CodescendsAlong.algebraMap_tensorProduct, PrimeSpectrum.tensorProductTo,
  CommRingCat.tensorProdIsoPushout, and an injectivity auxiliary. No exact match.
- Loogle: `"MvPolynomial", "IsPushout"`. Four hits, the two coefficient-extension
  pushouts and two fraction-field versions. Read TensorProduct/MvPolynomial:178;
  this is the coefficient-extension square, not evaluation at the selected b_i,
  and has neither the linear h nor the spectrum identities of our statement.
- Mathlib grep: `MvPolynomial.*[Pp]ushout|[Pp]ushout.*MvPolynomial|
  tensorPrincipalPolynomial|tensor_principal_polynomial`. Seven hits, in
  Algebraic/Integral, Algebra/Category/Ring/Topology, and TensorProduct/MvPolynomial.
  No entire construction. Read CommRingCat.isPushout_tensorProduct in
  Algebra/Category/Ring/Constructions:116: it is the generic tensor pushout only.
- LeanSearch: “A tensor principal open is the pullback of a finite linear
  polynomial principal open with image equal to the inverse image of the
  polynomial spectrum image”. Eight hits, including pullbackSpecIso, ordinary
  basic-open transport and the tensor spectrum point map, not this construction.
- Direct rg over the complete `lean/WeilConjectures` and `lean/Sheaf` source trees
  for tensor/principal/polynomial, polynomial pushout/specialization and the
  blueprint id found related polynomial and Rees modules, but no declaration
  stating this item. The blueprint id has no existing upstream match. Name
  searches for `TensorPrincipalPolynomialModel` and its lower-camel form in
  both libraries and dag/lean_names_upstream.json found no prior declaration.
- Read PolynomialLaw.exists_lift at RingTheory/PolynomialLaw/Basic:452: it produces
  an arbitrary polynomial-tensor lift, rather than the required linear polynomial,
  evaluated-variable square, and two image identities. It is not an exact match.

The initial server compile exposed noncomputability of Mathlib's polynomial data
and an unresolved coefficient-type argument in a spectrum expression. Definitions
are now explicitly noncomputable, with real data, and C is explicitly specified
for each specialization. The repaired module compiled cleanly as both sandbox
and library module. A final compile with autoImplicit disabled and the explicit
max-universe test ring, then deliver2.py dry run and push, follows this report.

## Second reading by O1

This is a separate second pass by the assigned worker, not a claim of independent
agent review: the dispatcher explicitly forbids starting another agent. The
maintainer's independent review reads the delivery.

I reread the whole node and final Lean file together. The only binders are the
three rings, their commutative-ring and A-algebra structures, g, the finite
witnesses, and the unrestricted compatible target ring maps. The finite witnesses
are shared by every conjunct; no clause picks an unrelated expansion. The three
helper definitions reduce directly to the maps and polynomial introduced in the
node. The raw tensor type is unchanged from the dependency. The pushout formula
uses u on a constant polynomial, rather than an ill-typed direct use on C.
The four scheme arrows in IsPullback are Spec(k), Spec(j), Spec(phi), Spec(e),
so the corners are D,S,B,R. Both image formulas use exactly those arrows.
`PrimeSpectrum.basicOpen` is the defined D(a), including nilpotent and zero cases.
I checked that no merely topological pullback replaced the scheme assertion,
that `∃!` includes both ring-map composites and the tensor formula, and that no
flatness or finite-type binder appeared. I changed E's universe to max u v during
this pass to keep all large test rings available, and disabled autoImplicit to
validate the explicit-binder rule. All helpers and the theorem have source and
blueprint docstrings; all seven accepted proof steps are in the theorem docstring.
Only the node's Lean record is changed, and its recorded signature is extracted
verbatim from the final file. No new mathematical mismatch remains.

Final validation: the prescribed scompile.py passed for the final module with
`autoImplicit false` and E in `Type (max u v)`, as both sandbox and named library
module, with no errors or unexpected warnings. The prescribed deliver2.py dry run
exited 0 and printed `OK (dry run): commit a66a7c193eb passes the preflight and
compiles; nothing pushed`. Its staged files were exactly the item module, item
node, and this report. The final delivery invocation reruns those gates and pushes.
