## Worker report

Module: `Sheaf.AlgebraicGeometry.SchemeTangentSpace`. It defines the tangent space at an
arbitrary scheme point, its canonical residue-field vector space, and the differential when
the induced residue-field map is an isomorphism. There is no new theorem or `sorry` in this
module; definitions select data from the named dependency theorems whose proofs await stage 3.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`, with explicit `universe u`.
- X a scheme over k: `(X : Scheme.{u}) (p : X ⟶ Spec (.of k))`. The explicit structure map
  agrees with both recorded dependency signatures. No finiteness, rationality, smoothness,
  closedness of x, separability, or characteristic assumption is imposed.
- A point x and its residue field: `(x : X)` and `K := X.residueField x`. This is Mathlib's
  field quotient of the stalk by its maximal ideal.
- Dual numbers and spectrum: `Spec (.of (DualNumber K))`, where Mathlib defines DualNumber
  as `TrivSqZeroExt K K`, and epsilon as `TrivSqZeroExt.inr 1`.
- Tangent vector theta is a morphism from that spectrum to X: the subtype underlying
  `schemeTangentSpace` has ambient type `Spec (.of (DualNumber K)) ⟶ X`.
- The closed point is Spec of epsilon mapping to zero: `c` uses `TrivSqZeroExt.fstHom`.
  Its restriction equals the canonical point: `c ≫ θ = X.fromSpecResidueField x`.
- Theta is a morphism over k: `θ ≫ p = q ≫ X.fromSpecResidueField x ≫ p`, where `q` is
  Spec of the coefficient inclusion `TrivSqZeroExt.inlHom`. This is the commuting triangle
  in the Stacks definition, not an added hypothesis on X or x.
- Canonical addition and zero: `schemeTangentSpaceAddCommGroup` is exactly
  `Classical.choose (exists_tangentVectors_vectorSpace k X p x).2.2.2`. Its specification
  sets zero to `q ≫ b` and addition to `s ≫ Θ`, where the unique gluing Θ is provided by
  that theorem, `E = Spec (.of (TrivSqZeroExt K (Fin 2 → K)))`, j_i is Spec of coordinate
  projection, and s is Spec of the sum of the two projections. Thus E has the stated
  three-element basis with all products of infinitesimals zero, and the sum sends both
  epsilon coordinates to epsilon, exactly as the node requires.
- Scalar multiplication and vector-space axioms: `schemeTangentSpaceModule` selects the
  module from `Classical.choose_spec` of the same group-existence proposition. Its
  specification is `(t • θ).val = m t ≫ θ.val`, where `m t` is Spec of
  `TrivSqZeroExt.map (t • LinearMap.id)`. This fixes epsilon mapping to t epsilon;
  `AddCommGroup` and `Module K` carry the axioms. No arbitrary vector-space data are supplied
  as additional parameters: the existential specification fixes all operations canonically.
- A morphism f of k-schemes: X, Y, pX, pY, f, and `hf : f ≫ pY = pX`.
- y=f(x): the target point is literally `f x`.
- Residue-field map an isomorphism: `he : Function.Bijective (f.residueFieldMap x).hom`.
  `RingEquiv.ofBijective` packages exactly that induced isomorphism, with no chosen unrelated
  field identification.
- The differential is residue-field linear: `schemeTangentMap` returns a linear map with
  scalars `X.residueField x`. The target action is `Module.compHom ... e.symm.toRingHom`,
  transporting the canonical target action to these scalars. Its data are chosen from
  `exists_tangentMap_linear k X Y pX pY f hf x he`, whose specification says
  `(L θ).val = d ≫ θ.val ≫ f`, with d the spectrum of the inverse field identification
  extended coefficientwise to dual numbers. This is exactly theta mapping to f composed
  with theta after identifying residue fields. The instance selections here are
  definitionally the same selections in the dependency theorem.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions`: a convention-only node, no declaration/import; scheme
  morphisms are Mathlib `AlgebraicGeometry.Scheme` and category morphisms as it specifies.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec` and `Spec.map`.
- `def-sc-dual-numbers`: `Mathlib.Algebra.DualNumber`, `DualNumber`.
- `lem-sc-tangent-space-vector-space`: `Sheaf.AlgebraicGeometry.TangentVectorsVectorSpace`,
  `AlgebraicGeometry.exists_tangentVectors_vectorSpace`. Read the complete theorem and its
  docstring, including the pushout, unique gluing, base compatibility, and operation formulas.
- `lem-sc-tangent-map-linear`: `Sheaf.AlgebraicGeometry.TangentMapLinear`,
  `AlgebraicGeometry.exists_tangentMap_linear`. Read the complete theorem and docstring,
  including all local instance selections, scalar transport, and postcomposition formula.

The module imports only `Sheaf.AlgebraicGeometry.TangentMapLinear`, which transitively imports
all the required declarations. No dependency needs replacement and no new node is needed.

Source check: local Stacks files are absent on this machine. Read the source directly at
[0B2B](https://stacks.math.columbia.edu/tag/0B2B),
[0B2C](https://stacks.math.columbia.edu/tag/0B2C), and
[0B2F](https://stacks.math.columbia.edu/tag/0B2F). These give respectively the operations,
the tangent-space definition, and the linear differential with equal residue fields.

Edge cases checked before writing: empty X has no x, so the definition imposes no excluded
case; Spec k at its unique point has only the constant tangent vector; the affine line at
its origin has vectors t mapping to a epsilon, with addition a+b and scaling lambda a.
Nonclosed points and transcendental residue fields are allowed. The over-k equation is
necessary even at a prescribed closed point of the test spectrum: a ring map on coefficients
can contain a derivation. The identity f gives the identity differential; t mapping to t^2
at the origin gives zero in every characteristic, including characteristic 2. A nonbijective
residue-field map is excluded exactly by the node's differential clause, not by the tangent
space definition. Universe u is arbitrary; no fixed cardinal bound is imposed.

Searches performed with `/home/ubuntu/weil-launcher/msearch.py C1 def-sc-scheme-tangent-space`:

- LeanFinder: `tangent space of a scheme over a field at an arbitrary point using residue
  field dual numbers`: eight hits, all residue-field point constructions; no tangent space.
- Loogle: `tangentSpaceAt, DualNumber`: no hits, unknown identifier tangentSpaceAt.
- grep: `tangentSpace|TangentSpace` under Mathlib/AlgebraicGeometry: no hits.
- LeanSearch: `tangent space of a scheme at a point from dual number morphisms`: service
  unavailable (Internal Server Error); no result obtained.
- `rg -n 'tangentSpace|TangentSpace|def-sc-scheme-tangent-space'` over the upstream
  WeilConjectures source and project lean/Sheaf: upstream `tangentSpaceAt` in
  Picard/Jacobian.lean only covers k-rational points; its group/module construction is at a
  group-scheme unit. Read its full definition and docstring (lines 690–702). It does not
  give this arbitrary residue-field notion. Project hits supply the two dependency theorems
  used here; neither is a named definition of the tangent space or differential.
- Read Mathlib signatures/docstrings of residueField, residueFieldMap, fromSpecResidueField,
  Spec, Spec.map and DualNumber. No existing exact definition was found.

Server validation: `scompile.py C1 def-sc-scheme-tangent-space` on this module succeeded
(exit code 0, 2.5 seconds), with no warning. Every variable and universe is explicitly bound.
No statement correction, disputed statement, new node, or dependency fault was found.

## Second reading by C1

Independent reading of the sandbox node and all 74 lines of SchemeTangentSpace.lean,
with the six dependency nodes and the source declarations open. Verdict: the Lean
renders every clause of the node; no mathematical or implementation change is needed.
The node copy has no statement_change. This delivery has no new nodes or dependency
modules, so H12/H13 add no further delivered objects to review.

Source: the local literature directory has no Stacks .tex checkout. I read the actual
varieties.tex section-tangent-spaces from
https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
including the introductory solid diagram and definition-dual-numbers,
lemma-tangent-space, definition-tangent-space, and lemma-map-tangent-spaces.
I also checked the rendered tags 0B2B, 0B2C, and 0B2F. The section assumes only a
scheme morphism and an arbitrary point; specializing its base to Spec k gives this
node. No finiteness, closed-point, separability, or smoothness restriction is implicit.
The additional cotangent-duality assertion in 0B2F is not a clause of this definition
node; its postcomposition differential and linearity are the clauses being rendered.

My object/hypothesis/conclusion checklist, with its Lean counterpart and verdict:

- Field k: `(k : Type u) [Field k]`. Exact, with arbitrary explicitly bound u.
- Scheme X over k: `(X : Scheme.{u}) (p : X ⟶ Spec (.of k))`. Exact structure
  morphism, compatible with the explicit p binders of both recorded dependencies.
  No scheme-property instance appears.
- Arbitrary point x: `(x : X)`. Exact, with no rationality or closedness predicate.
- Residue field kappa(x): `X.residueField x`. I read residueField and its Field
  instance in Mathlib.AlgebraicGeometry.ResidueField: it is the residue field of
  the structure-sheaf stalk, not global sections or a chosen extension field.
- Dual-number ring and spectrum: `DualNumber K` and `Spec (.of (DualNumber K))`.
  Mathlib.Algebra.DualNumber defines this as TrivSqZeroExt K K, with epsilon
  `inr 1`; it has the required two-dimensional K-module and square-zero epsilon.
  Mathlib's Spec and Spec.map are the recorded contravariant affine-spectrum
  construction, which I read in Scheme.lean.
- Tangent vector: the subtype's underlying morphism `θ : Spec (.of (DualNumber K))
  ⟶ X`. Exact object and direction; no replacement by a cotangent dual.
- Prescribed closed point: `c ≫ θ = X.fromSpecResidueField x`, with c the Spec
  of fstHom. I read fstHom and fromSpecResidueField: the former kills epsilon,
  and the latter is Spec of the stalk residue quotient followed by fromSpecStalk.
  Exact canonical point, with equality of morphisms, not only underlying points.
- Morphism over k: `θ ≫ p = q ≫ X.fromSpecResidueField x ≫ p`, q the Spec of
  inlHom. The source diagram's vertical test-scheme map is precisely this
  coefficient-based structure map when S = Spec k. Exact commuting triangle.
- Canonical addition: schemeTangentSpaceAddCommGroup chooses the additive group
  from `(exists_tangentVectors_vectorSpace k X p x).2.2.2`. Reading that theorem
  against lem-sc-tangent-space-vector-space confirms its subtype T is
  definitionally this schemeTangentSpace. Its E is TrivSqZeroExt K (Fin 2 → K),
  hence basis 1, epsilon_1, epsilon_2 with every infinitesimal product zero.
  Its j 0/j 1 are the two coordinate projections, its s is their sum, its
  IsPushout and unique-gluing clause supply exactly the required Theta, and its
  addition specification is `(θ₁ + θ₂).val = s ≫ Θ`. Exact; choice does not
  discard this specification or introduce a freely supplied operation.
- Zero and vector-space axioms: that same witness specifies `(0 : T).val = q ≫ b`
  and packages AddCommGroup T and Module K T. Exact canonical zero and axioms.
- Scalar multiplication: schemeTangentSpaceModule chooses the module from the
  specification of the same chosen group. Its scalar specification is
  `(t • θ).val = m t ≫ θ.val`. I read TrivSqZeroExt.map: it fixes inl and
  acts on inr by the given linear map, so `t • LinearMap.id` sends epsilon
  to t epsilon. Exact scalar action, coherent with the chosen additive group.
- Morphism f over k and y=f(x): schemeTangentMap binds pX, pY, f and
  `hf : f ≫ pY = pX`, and uses `(f x)` as the target point. Exact.
- Induced residue-field isomorphism: `he : Function.Bijective
  (f.residueFieldMap x).hom`. I read residueFieldMap: it is induced by f's
  local stalk map, in direction kappa(y) to kappa(x). RingEquiv.ofBijective
  packages exactly its being an isomorphism; no arbitrary identification is added.
- Differential formula and linearity: the result is a linear map over
  `X.residueField x`; `Module.compHom ... e.symm.toRingHom` transports target
  scalars from kappa(y). The chosen exists_tangentMap_linear witness has
  `(L θ).val = d ≫ θ.val ≫ f`, d being Spec of DualNumber.mapRingHom of the
  inverse residue-field isomorphism. Thus d goes from the target test spectrum
  to the source test spectrum, the correct contravariant direction. Exact
  postcomposition after identification. I checked that all four group/module
  selections in that theorem are the same terms as these named instances.

Dependency audit: def-weil-pbc-scheme-conventions explicitly fixes no new notion;
its convention record adds no hidden hypothesis. The three Mathlib leaves for
residue fields, spectra, and dual numbers are used directly. Both landed tangent
lemmas were read in full against their node statements, including their operation
and differential specifications and their stage-3 proof docstrings. They are usable
without replacement. There is no private alternate definition of a dependency.

Edge cases: the empty scheme admits no x, as in the source. For X = Spec k the
triangle forces the sole tangent vector, giving the zero vector space. For A^1 at
its origin the ring map sends the coordinate to a epsilon; the two projections and
sum give (a+b) epsilon and scaling gives lambda a epsilon. Nonclosed points and
transcendental or inseparable residue extensions remain admissible. Zero scaling
and characteristic 2 require no division and are covered. The identity differential
is postcomposition by the identity with the induced field identification. There is
no variable n or index set in the item; Fin 2 only models the specified binary sum.
Every universe and binder is explicit. Mathlib schemes and their rings live in the
same universe u here; u is arbitrary and any smaller field/scheme presentation can
be lifted to a common universe, so this imposes no fixed cardinal bound.

Independent searches, with different wording from the worker's queries:

- LeanFinder via msearch.py: `relative tangent vectors scheme point dual numbers
  residue field differential`. Eight algebra-extension/Kaehler hits, including
  Algebra.Extension.infinitesimal and Algebra.Extension.CotangentSpace; none defines
  the scheme-point dual-number morphism subtype.
- Loogle via msearch.py: `DualNumber, AlgebraicGeometry.Scheme`. Zero hits.
- LeanSearch via msearch.py: `scheme relative tangent vectors at a non rational
  point`. Service unavailable (Internal Server Error); no search verdict claimed.
- rg for tangentSpace, TangentSpace, tangentVector, TangentVector and schemeTangent
  in Mathlib/AlgebraicGeometry, upstream WeilConjectures/AlgebraicGeometry, and
  project lean/Sheaf/AlgebraicGeometry. Mathlib has no match; project hits are
  the two used dependency lemmas. Upstream tangentSpaceAt in Picard/Jacobian.lean
  was opened at lines 686–710: it takes a k-rational point of an Over object,
  not an arbitrary scheme point with its residue field. Its group instances
  specialize further to the unit of a group scheme.
- I also opened upstream TangentSpace.lean in full and searched GroupScheme/Lie.lean
  definitions to check alternate names. tangentSheaf/tangentSheafAlong are sheaf
  duals of differentials; infPoints, tangentGroup and differential in Lie.lean
  are group-scheme notions. None is this arbitrary-point tangent space or map.

H5/H6/H8/H9: all four delivered declarations have source/blueprint docstrings;
there are no theorems to prove and no sorry in the module. Every chosen datum is
supplied by a named dependency theorem with a complete operation specification.
The sole import is used, the namespace has no Sheaf prefix, and lines fit 100
characters. The node's lean.statement is verbatim the schemeTangentSpace signature.
No mismatch was found; the only change is this independent reading report.

Validation: scompile.py C1 def-sc-scheme-tangent-space on SchemeTangentSpace.lean
compiled cleanly in 2.6 seconds, exit code 0, with no warnings.
