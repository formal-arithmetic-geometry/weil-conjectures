## What changed

The original theorem has a complete Lean proof from two smaller public statements. It first
proves that the property `IsZero (R^q h_* constant(A))` contains zero, respects isomorphisms,
and is closed under short exact extensions. Exactness uses the already-proved arbitrary-ring
constant-sheaf instances and `ShortExact.map_exact_of_isHomological` from the source library.
It then applies finite-module induction to every finite submodule and passes to their union.
The bound and the noninjective-prime hypotheses are inherited through the subtype inclusion
by explicit Lean arguments. No existing declaration signature or definition changed.

Added proof imports:
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`;
- `Sheaf.Algebra.FiniteTorsionExtensionInduction`;
- `Sheaf.AlgebraicGeometry.SmoothBaseChange.ConstantFiniteSubmoduleVanishing`.

All three delivered modules compile without warnings through `lcompile.py --all`. The
new finite theorem is purely algebraic; the other new theorem contains no prime hypothesis
and isolates the colimit/universe part. Neither restates the item.

## Proved and sorry left

Closed the direct hole in
`AlgebraicGeometry.Etale.isZero_higherDirectImage_constant_of_prime_vanishing`
(node `lem-sbc-torsion-constant-prime-devissage`). No direct `sorry` remains in the item.

Added two holes:
- `ModuleCat.finite_torsion_property_of_prime`
  (`lem-sbc-finite-torsion-extension-induction`);
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_constant_of_finite_submodules`
  (`lem-sbc-constant-finite-submodule-vanishing`).

This is a decomposition, not an axiom-free proof: one hole closed and two holes added,
so the delivery's net hole change is minus one before any effects of pruning. The item
still depends on the two explicitly named `sorry` theorems. Each is in its own module,
with a source, a full proof in words, and a matching node. No arbitrary data is selected
from either theorem, and no definition contains a hole.

## No longer needed

Removed these direct proof imports from the item:
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`;
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit`;
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`;
- `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`.

`lem-weil-pbc-derived-functor-long-exact` and its FullLongExactSequence module are not
needed by this proof: middle exactness follows from the proved distinguished-triangle
interface in every integer degree. `lem-sc-coprime-torsion-decomposition` is not needed:
apply the finite abelian structure theorem to finite submodules directly, without first
decomposing the whole module into primary components.

The finite abelian structure theorem (`lem-sbc-finitely-generated-abelian-group-structure`)
is still needed by the new algebraic node. The filtered-colimit cohomology, higher direct
image colimit, and presheaf formula nodes are still needed below the new union node;
they have been moved below that argument, not declared globally unnecessary. Their
modules may also be reached by other targets, so no whole-library pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The stated decomposition lemmas do not directly supply the categorical finite-module
induction needed in the original proof. The new algebraic theorem isolates the missing
glue (prime-power short exact sequences, finite-sum assembly and integer-linear transport).
The existing higher-direct-image colimit interface takes `J : Type`, whereas the
finitely generated submodule index for this item lies in `Type (u+1)`. The cohomology
interface also has a smaller index universe. One cannot simply apply either interface
to this index. The new union theorem explicitly retains this universe obligation and
its proof explains how the finite-cover argument extends; it does not assert that a
large index can be shrunk to Type 0.

The local literature clone lacks the Stacks source texts. Read the official Tag 0F08
and Tag 0739 pages online and read Mathlib's finite-group structure theorem directly.
The new proofs are marked agent-written elaborations of those arguments. LeanSearch
returned Internal Server Error and is recorded as unavailable, never as a negative search.
Blueprint searches for finite subgroups and finite abelian groups found no matching node.
No unit-level route or target statement was changed; this is the same cyclic-coefficient
reduction below the universal datum unit.

## New nodes

`lem-sbc-finite-torsion-extension-induction`, in
`lean/Sheaf/Algebra/FiniteTorsionExtensionInduction.lean`, states an abstract algebraic
extension induction for a finite integer module, with the original relevant-prime
condition. It handles zero modules, annihilator 1, and exponent-zero summands.

`lem-sbc-constant-finite-submodule-vanishing`, in
`lean/Sheaf/AlgebraicGeometry/SmoothBaseChange/ConstantFiniteSubmoduleVanishing.lean`,
states vanishing from all finite submodules of a bounded torsion module. Its index
universe is explicit in the proof obligation; negative degrees vanish separately.


## Second reading by W3

1. Compared every delivered module with the read-only repository. The item is the only
existing module; its theorem signature is byte for byte unchanged. There are no changed
definitions or other existing declarations. The other two modules are new statements,
declared above and in their nodes. No change record is needed. Verdict: pass.

2. Compiled all three modules with lcompile.py --all, with no errors or warnings.
Searched the files for forbidden declarations and hidden holes: only the two named
public theorem holes listed above remain; there are no definitions or selected witnesses.
Scratch copies with #print axioms show only propext, Classical.choice, Quot.sound and
sorryAx for all three delivered theorems. The target is a genuine reduction, not an
axiom-free proof. Verdict: pass as a decomposition.

3. Read both split statements and their full docstring arguments, and independently
checked Stacks Tags 0F08 and 0739 and Mathlib's finite abelian group decomposition.
For the algebraic lemma tested zero modules, n=1, Z/4 with n=4, mixed Z/2 + Z/3
with n=6, extraneous prime divisors, and exponent-zero summands. Noninjectivity is
only requested for primes actually occurring in nonzero summands. For the union lemma,
every cyclic submodule is finite because n is nonzero; zero modules, n=1, q=0 and
negative q are covered. Its larger index universe is a real obligation, explicitly
retained in the proof, not an illicit specialization of the Type-0 theorem.
These are independent algebraic and colimit parts, neither a renamed target.
Independent msearch queries used composition factors/finite length and directed unions
of constant finite coefficients; results supply ingredients, not either full statement.
The rg search through Sheaf and WeilConjectures likewise found no duplicate statement.
Neither hole can be closed in a few minutes with these interfaces. Verdict: pass.

4. Read the proof from its conclusion upward. The extension step already uses proved
exactness and the distinguished-triangle interface, avoiding an unnecessary holed
long-exact-sequence theorem. The finite-submodule route avoids primary decomposition
of the whole module. The No longer needed section accounts for all six old direct
proof dependencies: two are eliminated and four are retained below the new nodes.
Read dag/units/sk-lem-universal-datum.json: no unit statement, step, or realized field
is altered, and the cyclic-coefficient reduction remains below the same unit.
All new proof imports are plain imports; public imports supply signature types.
Verdict: pass.

5. Compared the Lean declarations with the three node records and checked their
proof/proof_deps/proof_origin. Only those three permitted fields of the existing node
changed. Both new nodes include source, natural-language proof, recorded searches,
status split, created, blueprint provenance, chapter/unit and matching lean records.
Their proof_deps are exactly the unions of their proof-step uses. Verdict: pass.

Repairs: rewrote the item's obsolete primary-decomposition docstring to explain its
actual extension/finite-submodule proof; removed one extra blank line; added plain
proof imports of Mathlib.GroupTheory.FiniteAbelian.Basic to the algebraic module and
Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf to the union module, matching
the dependencies their nodes plan to use. No proof term or statement was changed.
