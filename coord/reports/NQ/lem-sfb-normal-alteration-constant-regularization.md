## Worker report

The module `Sheaf.AlgebraicGeometry.NormalAlterationConstantRegularization` states
`AlgebraicGeometry.exists_normal_alteration_constant_regularization`, with `sorry` as its
whole proof. It introduces no definitions or further nodes. The node statement and all its
other fields are unchanged; only `lean` is recorded. The declaration docstring includes all
sixteen original proof steps with their cited nodes.

### Hypotheses and clauses

- A field k is `(k : Type u) [Field k]`. The schemes Y and S and their structure morphisms
  are `(Y S : Scheme.{u})`, `pY`, `pS`. Explicit structure morphisms are used because this
  statement compares several scheme and scalar morphisms.
- Integrality of Y and S is `[IsIntegral Y] [IsIntegral S]`; normality is `hYnormal` and
  `hSnormal`, requiring each local ring to be a domain and integrally closed. Projectivity
  is `[IsHProjective pY] [IsHProjective pS]`, exactly the node's finite projective-space
  embedding convention. These instances imply properness, locally finite type and
  quasi-compactness, so finite type is included without an extra assumption.
- Geometric integrality of Y/k is `[GeometricallyIntegral pY]`.
- The alteration is `b : S ⟶ Y`, `[IsProper b] [Surjective b]`, `hb : b ≫ pY = pS`,
  and `hbfinite`, a dense open U of Y on which `b ∣_ U` is finite. No smoothness,
  separability, faithfulness or projectivity of b is assumed.
- The finite groups H and J have independent universes v and w, `Group` and `Finite`
  instances. The quotient is `ρ : J →* H` with `hρ : Function.Surjective ρ`.
- Actions are monoid homomorphisms `σk : H →* (k ≃+* k)`, `σY : H →* Aut Y`,
  `σS : J →* Aut S`. The equations hY and hS give the compatibility with the field
  action, using inverse field automorphisms under contravariant Spec; heq is equivariance
  of b through ρ. This is the convention used in the landed consumer
  `exists_equivariant_single_curve_nodal_reduction`.
- The inclusion k(Y) → k(S) is an `Algebra Y.functionField S.functionField` with hfield
  equating its map to the transported stalk map of b at the generic point. The proof
  hgeneric says b maps the generic point to the generic point; it follows from the
  alteration hypotheses, and serves only to type this canonical map. Every alteration
  supplies this uniquely determined field structure; neither an arbitrary inclusion nor
  an extra mathematical restriction is introduced.
- A = ker ρ is `ρ.ker` everywhere. The hypothesis `hinsep` supplies an intermediate
  field K whose members are exactly the elements fixed by A in S.functionField, and
  `IsPurelyInseparable Y.functionField K`. Thus the fixed-field inclusion uses b.
- The finite extension e/k is existential `e : Type u`, `Field e`, `Algebra k e`,
  `Module.Finite k e`. Its J-action is γ; the following elementwise equation says γ
  extends the given action of J through ρ on k.
- The fixed constant field e^A/k is an intermediate field of e characterized by
  `∀ a : ρ.ker, γ a.val z = z`, with `IsPurelyInseparable k K`.
- B is existential `Scheme.{u}` with `IsIntegral B`, structure morphism pB to Spec e,
  `IsHProjective pB`, `GeometricallyIntegral pB`, and the displayed local-ring normality
  assertion. Finite type again follows from H-projectivity.
- The required q is `q : B ⟶ S`; its structure equation identifies its composite to
  Spec k with the e-structure followed by Spec of k → e. The conjunction
  `IsFinite q ∧ Surjective q ∧ UniversallyInjective q` is precisely finite, surjective,
  radicial, in the universally injective convention expressly allowed by the node.
- The J-action τ on B is a monoid homomorphism to Aut B. The pB equation makes it
  compatible with γ on e; the q equation is J-equivariance to the given action on S.
- The composite B → Y is `q ≫ b`, and is required to satisfy `IsHProjective (q ≫ b)`.
  The H in H-projective imposes no condition on the finite group H.
- The inclusion k(S) → k(B) has an existential Algebra structure with its map equated
  to the generic-stalk map of q, using hq. Its finiteness and pure inseparability are
  `Module.Finite S.functionField B.functionField` and
  `IsPurelyInseparable S.functionField B.functionField`.
- The Y.functionField-algebra structure on B.functionField is the composite inclusion,
  fixed by `IsScalarTower Y.functionField S.functionField B.functionField`. The
  intermediate field characterized by the actual function-field automorphisms of τ on
  `ρ.ker` is thus k(B)^A with the prescribed inclusion of k(Y); it is required to be
  purely inseparable over Y.functionField.
- The structural e → k(B) is an Algebra structure whose spectrum map is required to
  equal `B.fromSpecFunctionField ≫ pB`. Its k-algebra structure is the composite through
  e, specified by `IsScalarTower k e B.functionField`. The equality
  `Set.range (algebraMap e B.functionField) = {z | IsAlgebraic k z}` says exactly that
  e identifies with the algebraic closure of k inside k(B). It asserts the entire
  relative algebraic closure, not merely that e consists of algebraic elements.
- If `topologicalKrullDim Y = 0`, `IsIso pB` identifies B with Spec e by its own
  structure morphism. Its already-stated equivariance makes this identification
  equivariant. Literal equality of schemes is not needed to express B = Spec e.

### Dependency declarations

The recorded dependency declarations and their full signatures/docstrings were read.
The following are the interfaces used, directly or through their public imports:

- `def-weil-field`: Field.
- `def-pc-integral-scheme`: Mathlib.AlgebraicGeometry.Properties / AlgebraicGeometry.IsIntegral.
- `def-weil-proper-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Proper / AlgebraicGeometry.IsProper.
- `def-weil-finite-type-morphism`: Mathlib.AlgebraicGeometry.Morphisms.FiniteType / AlgebraicGeometry.LocallyOfFiniteType.
- `def-pc-geometrically-irreducible`: Mathlib.AlgebraicGeometry.Geometrically.Integral / AlgebraicGeometry.GeometricallyIntegral.
- `def-kun-projective`: WeilConjectures.AlgebraicGeometry.Morphisms.Projective / AlgebraicGeometry.IsHProjective.
- `def-weil-finite-integral-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Finite / AlgebraicGeometry.IsFinite.
- `def-weil-surjective-morphism`: Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap / AlgebraicGeometry.Surjective.
- `def-sc-function-field`: WeilConjectures.AlgebraicGeometry.FunctionField / AlgebraicGeometry.Scheme.functionFieldOfComponents.
- `def-pc-field-extension`: Mathlib.Algebra.Algebra.Defs / Algebra.
- `def-pc-field-tower`: Sheaf.FieldTheory.FieldTower / FieldExtension.degree.
- `def-weil-pbc-reduced-normalization`: Sheaf.AlgebraicGeometry.ReducedNormalization / AlgebraicGeometry.Scheme.reducedNormalization.
- `def-weil-radicial-morphism`: Mathlib/AlgebraicGeometry/Morphisms/UniversallyInjective.lean / AlgebraicGeometry.UniversallyInjective.
- `def-kun-topological-krull-dimension`: Mathlib.Topology.KrullDimension / topologicalKrullDim.

For the integral-scheme clause of def-sc-function-field, the recorded module expressly
reuses Mathlib `Scheme.functionField`, rather than the product over arbitrary components.
For def-pc-field-tower the module docstring expressly uses `Module.Finite` and
`IsPurelyInseparable` for its finiteness and inseparability clauses. No dependency repair
is necessary. `Scheme.functionFieldAut` is reused from
`WeilConjectures.AlgebraicGeometry.StalkAut`; its fixed elements express the actions
induced by the actual scheme automorphisms. All already-recorded proof-dependency modules
are imported, privately unless also used for the statement; their sixteen-step plan is
retained verbatim in the theorem docstring. The reduced-normalization dependency is a
proof construction, so the existential conclusion does not prescribe it as additional data.

### Edge cases and source reading

Empty schemes are excluded by the stated integrality assumptions, as in the node.
Trivial groups, kernels and nonfaithful actions are allowed; there are no injectivity
requirements on any action. H and J have independent universes; finite extensions and
normalizations can be represented in the same universe as the original schemes.
Characteristic zero is included: Mathlib's IsPurelyInseparable then forces equality of
the extension, without requiring positive characteristic or supplying a characteristic
parameter. In positive characteristic the predicate allows element-dependent p-powers;
no uniform exponent is added. In dimension zero the conclusion uses the structural
isomorphism pB, without imposing any dimension hypothesis in the general case.

Read de Jong's publisher PDF, Lemma 5.5 and proof, printed p. 614:
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf . Its preparation and Stein
factorization give precisely the source route expanded in this node's proof. No
statement discrepancy or counterexample was found. The source explicitly allows group
actions; the node's explicit root-orbit construction retains semilinear actions.

### Searches and validation

- `msearch.py ... leanfinder` with query "Equivariant regularization of constants of a
  normal projective alteration by a finite purely inseparable radicial cover": eight
  hits, all normalization constructions; none states this result.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.IsNormal, IsPurelyInseparable, FixedPoints.subfield`: no hits
  (IsNormal is not a declaration). Normality therefore uses the established local-ring
  form, also used by NormalSteinConstantField and the consumer.
- `msearch.py ... loogle` with `IsPurelyInseparable, Module.Finite`: no combined hit.
- `msearch.py ... grep` with `alteration|constant.regularization|constantRegularization`
  in Mathlib/AlgebraicGeometry: no hits.
- `rg` of `constant.regularization|constantRegularization|normal_alteration|NormalAlteration|
  normalAlteration` in Sheaf and WeilConjectures found only the consumer's proof plan.
  Further searches for alterations, field actions, fixed fields and canonical field
  algebras located the reused consumer, NormalSteinConstantField, StalkAut and
  LocalDimensionFormula interfaces. No existing theorem states the requested result.
- The exact node-id grep in WeilConjectures found no upstream declaration.
- `scompile.py --source Sheaf.AlgebraicGeometry.NormalAlterationConstantRegularization`
  confirmed no such current-server module before its creation.
- `scompile.py NQ lem-sfb-normal-alteration-constant-regularization <module>` compiled
  both sandbox and library names against the server's published build, cleanly
  (3.2 seconds and 2.8 seconds); no errors or warnings were printed.

The previous dispatcher message's NM merge corresponds to the local ledger's stage-1
landing, and this node has no local Lean attachment. This packet is a stage-2 statement
with a genuine Lean delta, rather than an unchanged stage-1 resubmission.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
