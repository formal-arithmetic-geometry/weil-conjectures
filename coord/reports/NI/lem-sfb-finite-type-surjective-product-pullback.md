## Worker report

The module `Sheaf.RingTheory.FiniteTypeSurjectiveProductPullback` states
`AlgHom.finiteType_productPullbackSubalgebra`, with its proof left as `sorry`.
The helper `AlgHom.productPullbackSubalgebra` is a real construction from Mathlib's
`AlgHom.equalizer`, not a second general equalizer definition. Its two maps send
`(q, c)` to `(ψ i q)_i` and `(φ i (c i))_i`. Thus equality in their target product
is precisely the node's coordinatewise equality. Its subalgebra supplies the
componentwise commutative-ring operations and the diagonal R-algebra structure.
This helper belongs to the cartesian ring explicitly introduced in this node;
it is listed in `lean.declarations` and has the same source and blueprint tag.
No new independent notion or dependency module is needed.

Source checked directly: `literature/stacks-project/more-algebra.tex`,
`lemma-formal-consequence` (Tag 08NI, lines 364–393) and
`lemma-fibre-product-finite-type` (Tag 00IT, lines 325–362). Tag 08NI has exactly
the finite set, Noetherian base, finite type Q/A_i/B_i and coordinatewise
surjectivity assumptions. The node renames A_i/B_i to C_i/D_i. Its explicit
cartesian subset realizes the source's ring P. The docstring includes all five
accepted proof steps: empty set and projection surjectivity; induction and
regrouping; explicit product algebra generators; two module generators; Artin–Tate.

Hypothesis and clause correspondence:

- The commutative Noetherian ring R is `(R : Type uR) [CommRing R]
  [IsNoetherianRing R]`.
- The finite set I is `(I : Type uI) [_root_.Finite I]`. The qualification avoids
  the distinct notion `AlgHom.Finite`. Neither an enumeration nor nonemptiness
  is required.
- The commutative R-algebra Q is `(Q : Type uQ) [CommRing Q] [Algebra R Q]`;
  its finite type hypothesis is `[Algebra.FiniteType R Q]`.
- The families C_i and D_i are `(C : I → Type uC) (D : I → Type uD)` with
  `[∀ i : I, CommRing (C i)]`, `[∀ i : I, CommRing (D i)]`,
  `[∀ i : I, Algebra R (C i)]`, `[∀ i : I, Algebra R (D i)]`, and the two
  coordinatewise `Algebra.FiniteType` instance families. All Q/C_i/D_i finite
  type assumptions are retained.
- The R-algebra homomorphisms are `φ : ∀ i : I, C i →ₐ[R] D i` and
  `ψ : ∀ i : I, Q →ₐ[R] D i`.
- Surjectivity is exactly `hφ : ∀ i : I, Function.Surjective (φ i)` and
  `hψ : ∀ i : I, Function.Surjective (ψ i)`. There is no assumption that
  `Q → Π i, D i` is surjective.
- T is `productPullbackSubalgebra R I Q C D φ ψ`, the subalgebra of
  `Q × ∀ i : I, C i` described above. Its membership means equality of the two
  D-valued functions, equivalent to `∀ i, ψ i q = φ i (c i)`.
- The main conclusion is `Algebra.FiniteType R
  (productPullbackSubalgebra R I Q C D φ ψ)`.
- The final sentence is the second conjunct:
  `IsEmpty I → Subsingleton (∀ i : I, C i) ∧
  Nonempty (productPullbackSubalgebra R I Q C D φ ψ ≃ₐ[R] Q)`.
  The product is inhabited by its zero element, so `Subsingleton` expresses
  precisely the one-element ring. The algebra equivalence expresses T ≅ Q.
  Its inverse is q ↦ (q, the unique empty function), as described in the proof.

Dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, in
  `Mathlib.RingTheory.Noetherian.Defs`, signature and docstring read at lines
  192–204; every ideal is finitely generated.
- `def-weil-pbc-finite-type-algebra`: imported its recorded module
  `Mathlib.RingTheory.FiniteType`. Its `mathlib_match` is `Algebra.FiniteType`,
  whose full signature and docstring at lines 37–40 were read and used.
  The lean record points to `RingHom.FiniteType` (lines 215–222), the same
  notion for a bare ring map. Our explicit R-algebras use the recorded
  `Algebra.FiniteType` match directly, so no dependency repair or duplicate
  definition is required; `RingHom.finiteType_algebraMap` gives the equivalence.
- Proof dependency `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, lines 116–119, imported privately.
- Proof dependency `lem-sfb-artin-tate-subalgebra-finite-type`: its Mathlib match
  `fg_of_fg_of_fg`, `Mathlib.RingTheory.Adjoin.Tower`, full signature and
  docstring read at lines 138–154, imported privately. The docstring explains
  its application to the subalgebra P of B.
- The public construction imports are `Mathlib.Algebra.Algebra.Pi`
  (`AlgHom.pi`, `Pi.evalAlgHom`), `Mathlib.Algebra.Algebra.Prod`
  (`AlgHom.fst`, `AlgHom.snd`) and
  `Mathlib.Algebra.Algebra.Subalgebra.Basic` (`AlgHom.equalizer`). Their full
  definitions and docstrings were read. No dependency's notion is redefined.

Edge cases checked before writing:

- Empty I: both target product functions are uniquely determined, so the
  equality constraint is vacuous. The product C_i is the one-element ring;
  first projection identifies the equalizer with Q. The statement includes
  both clauses explicitly and permits empty I.
- Singleton I: this is the ordinary fibre product of two surjections.
- Multiple identical ψ_i (e.g. Q=C_i=D_i=k with all maps identity): the map
  from Q to the product D_i need not be onto. T still identifies with Q,
  and our assumptions do not exclude this case.
- All D_i zero: T is the full product Q × Π C_i, finite type. Zero rings and
  a zero base are permitted: there is no Nontrivial or domain assumption.
- R→Q and R→C_i need not be injective. All scalar maps are the given algebra
  structures, never inferred inclusions.
- uR/uI/uQ/uC/uD are separately bound universes; there is no equal-universe
  assumption on rings or restriction on the size of the finite index set.

Searches actually run (logged `msearch.py NI
lem-sfb-finite-type-surjective-product-pullback`, 2026-10-24):

- LeanFinder: "A finite product pullback of finite type algebras over a
  Noetherian ring along coordinatewise surjective maps is finite type".
  Eight hits, including `Algebra.FiniteType.prod`, finite-presentation Pi
  and finite type of surjections; none states this subalgebra finite-type result.
- Loogle: `Algebra.FiniteType, "pullback"`. Zero hits.
- LeanSearch: "Finite type of a pullback of a finite product of surjective
  algebra maps over a Noetherian ring". Eight hits, including finite type of
  quotients, ring-map finite type, and scheme base-change results; no exact match.
- Mathlib grep:
  `(pullback|equalizer|fiberProduct).*(FiniteType|finiteType|finite_type)|`
  `(FiniteType|finiteType|finite_type).*(pullback|equalizer|fiberProduct)`.
  Seven hits, all scheme finite-type base-change results; no exact algebra match.
- Direct rg of the named Mathlib algebra files found the existing equalizer,
  product projection and Pi algebra-hom constructors; these are reused.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for finite type and
  pullback/fibre-product wording found scheme or module results, none stating
  this ring lemma. Direct grep of the node id under `lean/WeilConjectures`
  returned no hits. Search for the two proposed declaration names found no
  existing declaration. Search for `AlgHom.equalizer` found other applications
  (invariants, deformations, descent), not this coordinate product construction.

The node statement, stmt_deps, proof and proof_deps are unchanged. Only its
`lean` field changes. There are no statement faults or STATEMENT-DISPUTED claims.
All variables are bound explicitly and `autoImplicit` is disabled.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
