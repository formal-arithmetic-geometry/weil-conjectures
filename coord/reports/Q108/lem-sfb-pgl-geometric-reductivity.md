## Worker report

This repaired packet states the three clauses of
`lem-sfb-pgl-geometric-reductivity` in
`lean/Sheaf/RepresentationTheory/PGLGeometricReductivity.lean`, with exactly
three theorem proofs `sorry`. All declarations are in
`AlgebraicGeometry.AffinePGL`. The mathematical statement, proof plan, and
proof dependencies of the node are unchanged. Its statement dependencies gain
Q117's landed `def-sfb-affine-pgl-action`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Field in every characteristic: `{k : Type u} [Field k]`. There is no
  characteristic, perfectness, or algebraic-closure restriction.
- Positive rank: `{r : ℕ}` and `_hr : 1 ≤ r` in all three theorems.
- Commutative k-algebras: `{E F : Type u}` with their `CommRing` and
  `Algebra k` instances. The common universe is the convention of the reused
  `AffinePGL.Action` interface, as explicitly required by the return.
- Rational PGL action: `D : Action k E r` and `D' : Action k F r` are Q117's
  actual natural GL actions on all scheme-valued points, with unit,
  multiplication, naturality, and trivial scalar action. Yoneda and descent
  along the fppf epimorphism GL -> PGL identify these with rational scheme
  actions, hence with the coactions in the node. No line linearization is used.
- The invariant ring is Q117's `D.invariants`, an intersection of equalizers
  of evaluations on all translated scheme-valued points. This is the coaction
  equalizer, including nilpotents; it is not just invariance under G(k).
- Finite generation of E: `[Algebra.FiniteType k E]`.
- Finite generation of E^G: `invariants_finiteType` concludes
  `letI := D.constants.toAlgebra; Algebra.FiniteType k D.invariants`.
  Thus the base algebra structure is induced by Q117's specified restriction
  `D.constants : k →+* D.invariants`, not an arbitrary coefficient map.
- Surjective equivariant map of finitely generated algebras: both finite-type
  instances, `f : E →ₐ[k] F`, `hf : Function.Surjective f`, and
  `heq : D.IsEquivariant D' f`.
- The helper `Action.IsEquivariant` says that Spec f commutes with `act` on
  every test scheme T and every GL matrix g. It quantifies x and y with
  `y.left ≫ Spec.map f = x.left` and requires the same equality after acting.
  Every y has exactly this x because f is a k-algebra map. This formulation
  supplies neither an arbitrary map nor an additional lifting hypothesis.
- Given invariant b: `(b : F) (hb : b ∈ D'.invariants)`.
- Positive-power invariant lift: `exists_invariant_power_lift` concludes
  `∃ (N : ℕ) (_ : 0 < N) (a : E), a ∈ D.invariants ∧ f a = b ^ N`.
- Nonnegative gradings: `𝒜 : ℕ → Submodule k E`,
  `ℬ : ℕ → Submodule k F`, `[GradedAlgebra 𝒜] [GradedAlgebra ℬ]`.
  These are Mathlib's internal direct-sum algebra gradings; no standard grading
  or condition E_0 = k is imposed.
- Degree-preserving actions: `hD : D.PreservesDegrees 𝒜` and its F analogue.
  `IsGradingTranslate 𝒜 T a x y` is the graph of the canonical grading G_m
  action: for e of degree n, `evaluation y e = a^n * evaluation x e`.
  `Action.PreservesDegrees` says that `D.act T g` preserves this graph, exactly
  commutation with the grading action, over every T and every global unit a.
- The grading graph is total and single-valued: for any x, a, and e = sum e_n,
  define the new evaluation as sum a^n evaluation(x,e_n). Unique decomposition
  makes it well-defined; graded multiplication and degree-zero constants make
  it a k-algebra homomorphism. The affine adjunction gives its unique point y.
  Thus the graph formulation does not make commutation vacuous or introduce
  a choice of action. The Laurent-polynomial universal unit detects degree
  even over finite fields, and all nonreduced tests are included.
- Graded map: `hgraded : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ n`.
- Homogeneous b of degree d: `(d : ℕ)` and `hbd : b ∈ ℬ d`.
- Homogeneous lift: `exists_homogeneous_invariant_power_lift` concludes
  `∃ (N : ℕ) (_ : 0 < N) (a : E),
  a ∈ D.invariants ∧ a ∈ 𝒜 (N * d) ∧ f a = b ^ N`.

Dependency declarations read and used:

- `def-weil-field` has Mathlib match `Field`,
  `Mathlib.Algebra.Field.Defs`; it extends `CommRing` and `DivisionRing`.
- `def-sfb-affine-pgl-action` records
  `Sheaf.AlgebraicGeometry.AffinePGLAction`. Its full module and docstrings
  were read, including `AffinePGL.affineOver`, `Action`, `evaluation`,
  `Action.invariants`, `Action.constants_mem`, and `Action.constants`.
  These exact declarations are used, not a private replacement.
- Its `PGLLinearization.Matrices` comes from
  `Sheaf.AlgebraicGeometry.PGLLinearizedPolarization`; the natural GL/scalar
  scheme-test interface there was read as well.
- `Algebra.FiniteType`, `Mathlib.RingTheory.FiniteType`; and
  `RingHom.toAlgebra`, `Mathlib.Algebra.Algebra.Defs`, whose coefficient map
  is definitionally the given ring homomorphism.
- `GradedAlgebra`, `Mathlib.RingTheory.GradedAlgebra.Basic`, the existing
  internal grading and decomposition, with no additional grading definition.

The proof-only imports are retained from the returned packet. They cover the
recorded Mathlib matches for field-module flatness, tensor exactness, affine
Noetherianity, finite-module ACC, finite submodules, integral adjoining, and
Artin--Tate. The five proof nodes on PGL structure, Haboush, finite
subrepresentations, submersiveness, and the subring criterion still have no
recorded Lean modules to import. The finite-generation theorem's docstring
retains all twelve proof steps, and the two power-lifting docstrings retain
their complete arguments.

Source re-read: [Alper arXiv:1005.2398v3](https://arxiv.org/pdf/1005.2398),
Lemma 9.2.5(3), Theorems 9.7.5--9.7.6, and Theorem 6.3.3. The homogeneous
refinement is the component-projection argument of proof step 3 of the node.
There is no mathematical statement correction and no disputed assertion.

Edge cases checked: r=1 gives the trivial group, r=0 is excluded explicitly;
the zero algebra is allowed; b=0 admits N=1 and a=0; d=0 remains degree zero;
no reducedness excludes nilpotents; all finite fields and all characteristics
are included. In degree zero the grading action multiplies by a^0=1.
The grading tests include Spec of Laurent polynomials and arbitrary nonreduced
schemes, so a finite field does not identify different degrees.

Searches made with the prescribed msearch.py wrapper:

- leanfinder, `Finite generation and invariant power lifting for rational
  projective linear group actions on affine algebras`: 8 hits, including
  `Algebra.IsInvariant.isIntegral`, `Algebra.IsInvariant.isIntegral_of_profinite`,
  and abstract fixed-field and projectivization facts. No exact theorem.
- loogle, `GradedAlgebra.proj, Algebra.FiniteType, RingHom.toAlgebra`: 0 hits
  for this combined query. The definitions were separately read in source.
- grep, `IsGradingTranslate|gradingAction|PreservesDegrees|geometricallyReductive`
  in Mathlib/RingTheory: 0 hits.
- leansearch, `Scheme action preserving grading commutes with multiplicative
  group scaling homogeneous elements`: 8 hits on `GradedMonoid.GMulAction`
  and `SetLike.gmulAction`; no scheme-valued grading-commutation predicate.
- rg in the project and upstream source for these helper names and the item id:
  abstract equivariance predicates, no exact helper or reductivity statement.
  Q117's landed affine action was found by the node and module searches and
  reused. The new helpers express equivariance and grading commutation on it;
  they do not define another PGL action or invariant ring.

## Returned-delivery repair

The return on immutable head `7f0a3265bd1a` identifies H12/H4: the former new
`def-sfb-pgl-algebra-action` duplicates Q117's landed
`def-sfb-affine-pgl-action`. Repaired exactly as requested:

1. Removed `dag/nodes/sec-six-functors-basics/def-sfb-pgl-algebra-action.json`
   and `lean/Sheaf/RepresentationTheory/PGLAlgebraAction.lean` from the packet.
2. Replaced that statement dependency by `def-sfb-affine-pgl-action` and
   imported its recorded module directly.
3. Restated all three theorems on `AffinePGL.Action k E r` and `D.invariants`,
   in common universe u. Finite type uses `D.constants.toAlgebra`.
4. Added the three fully defined helpers `Action.IsEquivariant`,
   `IsGradingTranslate`, and `Action.PreservesDegrees` in the item's own module,
   with source/blueprint docstrings and entries in `lean.declarations`.

The initial prescribed dry run of the saved packet passed at `32a9941366a`, but
that packet still had the duplicate identified by the independent return.
This repair changes the Lean interface substantively; it is not an unchanged
re-push. Comparing the retained packet with current live node records shows
that the item still has no landed module, Q117's action is landed and usable,
and the item's JSON changes only `lean` and the added action `stmt_deps`.
The existing Q117 definition node and module are not edited.

The five current citers continue to use the identical mathematical result:
`lem-sfb-git-orbit-closure-dimension`,
`lem-sfb-projective-pgl-stable-quotient`,
`lem-sfb-affine-pgl-finite-stabilizer-quotient`,
`lem-sfb-projective-pgl-invariant-quotient`, and
`lem-sfb-affine-pgl-quotient-orbit-topology`.
In particular Q117's affine finite-stabilizer quotient now uses the same action
and invariant ring as this theorem. No unrecorded action-comparison theorem is
needed.

## Second reading by Q108

This is the dispatcher's single-worker repair self-check; the maintainer's
independent review remains the independent reading. With the node, Q117's
full action module, and the repaired module open, checked each binder and clause
against the correspondence above. The mismatch found was the duplicated action
and invariant-ring interface, now removed. The three theorems use the exact
landed action and equalizer invariants; equivariance has the contravariant Spec
orientation; degree preservation commutes with the total canonical grading
G_m action. The constants map fixes the finite-type algebra structure.
The original three conclusions and all mathematical hypotheses are retained.
No new definition node or dependency module remains in this packet.

Validation: scompile.py compiled the repaired file in sandbox and library mode
with no errors or warnings (2.8 seconds and 1.9 seconds). The file starts with
`module`, uses `autoImplicit false`, explicitly binds universe u and every
variable, and contains exactly three named sorry proofs. Every declaration has
a source and blueprint docstring; the primary JSON signature is copied
verbatim from the file. Final dry-run and delivery results are recorded below.

Final repaired-packet dry run passed: `52746c1f0c1`, preflight and per-file
compilation OK. The final local self-check also passed: one module, one node,
exact recorded signature, no line over 100 characters, exactly three sorry
proofs, and only the authorized lean/stmt_deps fields changed.
