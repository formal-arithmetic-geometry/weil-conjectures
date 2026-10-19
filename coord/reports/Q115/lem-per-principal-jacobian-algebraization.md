## Worker report

The module `Sheaf.RingTheory.PrincipalJacobianAlgebraization` states
`AlgebraicGeometry.principalJacobianAlgebraization` with `sorry`. It defines no new
notion. The only extra statement dependency is the already landed
`def-per-completed-polynomial-conormal`, whose module and complete declaration
signatures/docstrings were read. The original mathematical statement is unchanged.

Hypothesis and conclusion correspondence:

- Commutative Noetherian base A: `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
- The chosen principal generator: `(a : A)` and `Ideal.span {a}` throughout.
- A nonnegative finite variable count: `(r : ℕ)` and variable set `Fin r`.
- P is the principal-adic completion of A[x_1,...,x_r]:
  `rigPolynomialCompletion (Ideal.span {a}) r`, definitionally
  `AdicCompletion ((Ideal.span {a}).map (algebraMap A (MvPolynomial (Fin r) A)))
  (MvPolynomial (Fin r) A)`.
- The ideal J and exact quotient E: `(J : Ideal (rigPolynomialCompletion
  (Ideal.span {a}) r))` and `rigPolynomialCompletion (Ideal.span {a}) r ⧸ J`.
  E is written explicitly, so there is no additional quotient map or arbitrary model.
- E is (a)-adically complete: the displayed `IsAdicComplete (Ideal.span {a}) E`
  instance binder. This is completeness for powers acting through the canonical
  A-algebra structure, equivalently for the extended ideal in E.
- The conormal and continuous derivative: `rigJacobianDifferential r
  (Ideal.span {a}) J` has domain `J.Cotangent = J/J²` and codomain `Fin r → E`.
  This is the canonical arrow induced from the unique filtration-preserving
  extensions of `MvPolynomial.pderiv`, not an arbitrary linear map. For finite
  `Fin r`, the function module is exactly the finite direct sum E^{⊕r}.
- A common nonnegative annihilating exponent: `(c : ℕ)`. The `hkernel` hypothesis
  is `(Ideal.span {a}) ^ c • delta.ker ≤ ⊥`. The `hcoker` hypothesis is the same
  vanishing condition on the top submodule of `(Fin r → E) ⧸ delta.range`.
  Because `(a)^c = (a^c)`, these mean precisely that a^c kills respectively the
  kernel and cokernel. Restricting the canonical differential to A-linear scalars
  leaves the underlying kernel, range and cokernel unchanged.
- A finite type commutative A-algebra C: the existential binders for
  `C : Type u`, `CommRing C`, `Algebra A C`, and
  `RingHom.FiniteType (algebraMap A C)`.
- An A-algebra isomorphism from its (a)-adic completion to E:
  `Nonempty (AdicCompletion ((Ideal.span {a}).map (algebraMap A C)) C ≃ₐ[A] E)`.
  There is no added etaleness or smoothness conclusion. Finite type A-algebras
  have representatives in the base universe, as quotients of a finite-variable
  polynomial ring over A; choosing `Type u` loses no algebraization.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, all ideals finitely
  generated. Source signature/docstring read.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`. This is the dependency's
  finite-support polynomial construction, used through `rigPolynomialCompletion`.
  Its source definition and the recorded evaluation/uniqueness descriptions were read.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete` and the canonical algebra structures. The compatible-sequence
  definition and Hausdorff/precomplete class signature were read.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` applied to `algebraMap A C`.
  The definition is exactly `Algebra.FiniteType` for the induced algebra structure;
  both source definitions were read. This uses the dependency's recorded main name.
- `Sheaf.RingTheory.CompletedPolynomialConormal`:
  `AlgebraicGeometry.rigPolynomialCompletion` and
  `AlgebraicGeometry.rigJacobianDifferential`, with the existing uniquely determined
  continuous partial derivatives and induced conormal map. The entire module was read.

The module imports every currently stated proof dependency. In particular it imports
`Sheaf.RingTheory.ConormalTorsionAlgebraization` and the published
`WeilConjectures.RingTheory.AdicCompletionNoetherian` (source obtained with
`scompile.py --source`), together with the Mathlib completion, finite type,
Noetherian-surjective-image and matrix-adjugate modules recorded on the proof leaves.
`lem-per-completed-cotangent-transitivity` and
`lem-per-principal-adic-homomorphism-lift` currently have neither a Lean record nor
Mathlib match, so have no module to import. They are proof-only dependencies; neither
is needed to formulate this statement. The nine-step proof docstring retains them
and all other steps from the node, rather than replacing the proof by the downstream
general-ideal algebraization theorem.

Source comparison: restricted.tex, Tag 0ALS says principal-ideal rig-etale complete
algebras are algebraizable; Tag 0AJU(3) says precisely that a common ideal power kills
the two homology modules, i.e. kernel and cokernel of this two-term conormal
presentation. Both source passages were opened and read. This confirms the node's
formulation without a statement correction.

Edge cases checked before writing:

- r = 0: `Fin 0 → E` is the zero module; the kernel condition is then the torsion
  condition on J/J² and the cokernel condition is automatic. No positivity assumption.
- c = 0: `(a)^0 = ⊤`; both homology modules must vanish, including a = 0.
- a = 0 with c > 0: the completion is the ordinary polynomial ring; its quotient
  already has a finite type algebraization. The hypotheses permit this case.
- a a unit: P is the zero ring, hence so is E. The zero finite type A-algebra
  provides a model. No nontriviality assumption is present.
- J = ⊤, zero base rings, and zero quotients are permitted; all ring typeclasses
  are `CommRing` with no `Nontrivial` assumption.
- No independent smaller universe for test objects is used. All universes and
  variables are explicit under `set_option autoImplicit false`.

Searches made:

- `msearch.py ... leanfinder` query: "A finite type algebra whose principal adic
  completion is a complete quotient of restricted polynomials with torsion Jacobian
  kernel and cokernel". Eight results: completion algebra structures, Weierstrass
  quotient equivalence, formally smooth adic lifting, complete implies henselian,
  finite presentation and completion evaluation. No algebraization statement matches.
- `msearch.py ... loogle` query `AdicCompletion, MvPolynomial.pderiv`:
  zero hits.
- `msearch.py ... grep` query `pderiv|derivation|Derivation` in
  `RingTheory/AdicCompletion`: zero hits.
- Direct `rg` in the upstream `WeilConjectures` for the item id, principal Jacobian
  algebraization and `exists_finiteType_algebraization`: no match. Direct search
  for completed polynomial/conormal/derivative notions located no upstream version.
- Direct `rg` in `lean/Sheaf` located the exact reusable completed conormal
  definition in `CompletedPolynomialConormal.lean`, the general-ideal
  `RigEtaleJacobianAlgebraization.lean`, and
  `ConormalTorsionAlgebraization.lean`. The general-ideal theorem also concludes
  etaleness away from the ideal and cites this item in its proof; it is not an exact
  match and cannot replace this node without a proof dependency cycle. The conormal
  torsion theorem starts from a quotient of a completed finite type model, a different
  hypothesis. Neither is a duplicate of this statement.
- Direct searches of `dag/lean_names_upstream.json`, Mathlib and upstream sources
  found no `principalJacobianAlgebraization` declaration. The canonical completed
  conormal definition already has its own DAG node, so it is cited, not copied.

Validation: `scompile.py Q115 lem-per-principal-jacobian-algebraization` compiled
this one file cleanly in both sandbox and library module contexts, each about
three seconds, without errors or warnings. No statement fault or
STATEMENT-DISPUTED issue was found. No dependency module or new node is needed.

## Second reading by Q115

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
