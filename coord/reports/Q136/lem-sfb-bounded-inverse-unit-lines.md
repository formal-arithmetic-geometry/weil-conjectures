## Worker report

The module `Sheaf.RingTheory.BoundedInverseUnitLines` states
`Units.finite_boundedInverse_scalarOrbits`, with its sole proof `sorry`.
The node's statement, dependencies, and eight-step proof are unchanged; only `lean`
is attached. There are no definitions, new nodes, or dependency repairs.

The statement matches each hypothesis and clause as follows:

- The algebraically closed field is `(F : Type u) [Field F] [IsAlgClosed F]`.
  These are exactly the Mathlib notions recorded by `def-weil-field` and
  `def-weil-algebraic-closure`. No algebraicity over a further field is required:
  the node assumes an algebraically closed field, not a specified algebraic closure.
- The commutative unital algebra is `(A : Type v) [CommRing A] [Algebra F A]`.
  `Algebra.algebraMap` is a unital ring homomorphism, and `Algebra.smul_def'`
  identifies scalar multiplication with multiplication through this homomorphism.
- The domain condition is `[IsDomain A]`. Together with `CommRing A` this is the
  usual integral-domain condition, including `Nontrivial A` and no zero divisors.
- The vector subspaces are `(V W : Submodule F A)`. Their finite dimensions are
  `[FiniteDimensional F V] [FiniteDimensional F W]`, the recorded Mathlib notion
  for `def-weil-finite-dimensional-subspace`. The ambient algebra need not be
  finite-dimensional or finitely generated; no such assumption is present.
- Units and their inverses are the existing `Aˣ` and its group inverse. The set
  `{a : Aˣ | (a : A) ∈ V ∧ ((a⁻¹ : Aˣ) : A) ∈ W}` states both membership clauses.
  In particular the inverse belongs to `A`, rather than to a fraction field.
- `MulAction.orbitRel Fˣ Aˣ` is the existing scalar-orbit equivalence relation.
  The canonical Mathlib action `Units.mulAction'` lifts the action of `Fˣ` on
  `A`; `Units.val_smul` and `Units.smul_def` identify its value with
  `algebraMap F A (c : F) * (a : A)`. Thus quotient equality means exactly
  multiplication by a nonzero scalar, as in the node. `orbitRel` uses the reverse
  orientation (`a = c • a'`), which is the same equivalence relation because
  `c⁻¹` also belongs to `Fˣ`.
- `Quotient.mk (MulAction.orbitRel Fˣ Aˣ) '' ...` is the set of those equivalence
  classes which contain a bounded-inverse unit. This image is precisely the
  quotient of the displayed subset by the restriction of the ambient relation:
  two elements have the same image exactly when they are equivalent. Hence
  `Set.Finite` of this image asserts exactly finiteness of the node's quotient.
  There is no finiteness assertion about all units or about all scalar orbits.
- Independent universe binders `u v` permit every field/algebra size in the node.
  All variables and universes are explicitly bound and both auto-implicit
  options are disabled. The statement has no `let`, extra witnesses, or choices.

Dependencies read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, line 180 and its docstring.
- `def-weil-algebraic-closure`: the `mathlib_match` explicitly identifies
  `IsAlgClosed` in `Mathlib.FieldTheory.IsAlgClosed.Basic`, lines 58-63;
  its splitting-polynomial definition and `exists_root` explain the agreement
  with the root formulation. The algebraic-closure construction itself is not
  needed for this node's assumptions.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional` in
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, lines 73-76, an abbreviation
  for `Module.Finite` (finite spanning set).
- The standard orbit and scalar-action interfaces were read in
  `Mathlib.GroupTheory.GroupAction.Defs` (`orbit`, `mem_orbit_iff`, `orbitRel`,
  `orbitRel_apply`) and `Mathlib.Algebra.Group.Action.Units` (`Units.mulAction'`,
  `Units.val_smul`, `Units.smul_def`). No private replacement is introduced.

The proof dependencies are retained as plain imports, with public imports reserved
for the statement's notions. They provide: closed immersions (Mathlib's
`Morphisms.ClosedImmersion`), properness and affine/proper finiteness
(`Morphisms.Proper`), the Jacobson property (`Morphisms.FiniteType`), closed
immersion/properness criteria (`ZariskisMainTheorem`), residue fields of closed
points (`AlgClosed.Basic`), finite fibres (`Morphisms.QuasiFinite`), standard Proj
opens (`ProjectiveSpectrum.Basic`), projective-space properness
(`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`), and the relative-Proj
closed immersion (`WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`).
The theorem docstring carries all eight proof steps and their named DAG inputs.

Source and edge cases:

I read the node's agent-formulated statement and complete incidence proof, together
with Milne's Proposition 12.48 and proof on printed pp. 246-247 in
`literature/milne-algebraic-groups_iAG2017.pdf`. Milne states the product-unit
factorization; this node is explicitly an auxiliary algebraic lemma, not a claim
that Milne states this exact formulation. The projective construction only uses
finite coordinates in V and W and thus imposes no finite generation on A.

Before writing the signature, checked `V = 0` and `W = 0`: the bounded-unit set
is empty since units in a nonzero ring cannot vanish. For `A = F`, any nonempty
set in question has one orbit. For `F[t]` its units are constants, again at most
one orbit. For Laurent polynomials and subspaces spanned by finitely many
monomials, only finitely many exponents satisfy both bounds. Infinitely generated
algebras are admitted. No characteristic restriction occurs. The domain and
algebraic-closure hypotheses are substantial: `F[ε]/(ε²)` has infinitely many
classes `1 + c ε` with both bounds the full two-dimensional space, and over
`R ⊂ C` the full two-dimensional space has infinitely many scalar classes of
units. Both counterexamples are excluded by the corresponding existing binders.
No node fault or STATEMENT-DISPUTED issue was found.

Searches performed on 2026-10-24 (the wrapper's exact queries and results are in
`searches.jsonl`):

- LeanSearch: `Finitely many lines of units in finite dimensional subspaces with
  bounded inverses over an algebraically closed field`. Eight results, including
  `FiniteDimensional.isUnit`, `instFiniteUnits`, and `FiniteDimensional`;
  none states bounded-inverse scalar-orbit finiteness for arbitrary domain A.
- LeanFinder: `In a domain over an algebraically closed field, units in a finite
  dimensional subspace whose inverses lie in another finite dimensional subspace
  have finitely many scalar classes`. Eight results on class groups, finite
  dimensionality and invertibility; no matching statement.
- Loogle: `Submodule, "IsUnit", "Finite"`. Zero hits.
- Mathlib grep through msearch: `Rosenlicht|bounded.*inverse|[Uu]nit.*[Ll]ines|finite.*span.*singleton`.
  Sixteen hits, concerning unrelated noetherian/Artinian finiteness, ideals,
  affine spans, integration and bounded linear inverses; no match.
- Direct `rg` on the specified live `lean/WeilConjectures` and `lean/Sheaf`,
  by `Rosenlicht`, bounded inverses, unit lines and scalar classes, found no
  implementation. The Rosenlicht mention in `NormalLineBundlePowerLinearization`
  is contextual, not this lemma. An exact item-id search of `lean/WeilConjectures`
  and a declaration-name search of both trees and `dag/lean_names_upstream.json`
  found no pre-existing declaration with this name or statement.

Validation: the prescribed `scompile.py Q136 lem-sfb-bounded-inverse-unit-lines`
compiled the delivered module in both sandbox and library module contexts with
exit code zero, no errors and no disallowed warnings. The first pass took 17.2 s
and the library pass 2.0 s, each below the unchanged 60 s limit.

## Second reading by Q136

No second reading by another worker: this dispatcher brief requires this worker
to deliver directly and prohibits starting other agents. The maintainer supplies
the independent review. In a final self-check I reread the exact node statement
against the file: algebraic closure, domain nontriviality, both finite-dimensional
subspaces, both unit membership clauses, the canonical nonzero-scalar relation,
and finiteness of the subset's quotient are all present. The orbit quotient image
has exactly the restricted relation, including the empty cases; no statement
correction or additional node is needed.
