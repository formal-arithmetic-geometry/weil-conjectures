## What changed

Proved the complete body of
`AlgebraicGeometry.Scheme.FiniteEtale.arithmeticLiftFibrePath`, with its signature and
all existing public definitions unchanged. Added proved private helpers for continuous
restriction of automorphisms, restriction of paths, its torsor bijection, constant-cover
sections and their labels, finite-model naturality, pullback coherence, and the fully
faithful comparison with stalk paths. Added private proof imports of PathTransport and
Prorepresentability from the adopted source library. No adopted source file was changed.

Isolated the genuine source result Stacks 0BTX (the arithmetic fundamental-group exact
sequence) as `ArithmeticExactSequence.lean`, with its embedding convention from 0BNE.
This is strictly smaller than the assigned theorem: it contains none of the moved-point
path bijection, finite-model normalization, conjugation, lift change, or stalk comparison.
Its natural-language proof is the first four steps of the original node, with the
extension of the embedding formula to all finite etale algebras explained explicitly.
The new quotient is determined uniquely by its constant-cover characterization; no
arbitrary data is defined by choosing an unspecified witness from an unproved existence.

The revised route obtains a pre-existing path from the proved source theorem
`CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor` and identifies its
restriction by sections of constant covers. Thus it avoids reconstructing a natural
path by descending all morphisms and all comparison equations. Only object descent is
needed for injectivity of geometric restriction. Pullback coherence is proved first for
arbitrary scheme maps, preventing expensive unfolding of the concrete scheme limit.

Validation: both sandbox modules compile together through `lcompile.py --all`; the
assigned module has no holes. Existing public imports and signatures are preserved.
The exact-sequence statement was checked for X₀ = Spec K, L = K, finite L/K, arbitrary
geometric-point field Ω, and finite etale product algebras (a map to L selects a field
factor). The chosen i need not be the separately installed L-algebra structure on Ω.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.FiniteEtale.arithmeticLiftFibrePath`.
All finite-model, conjugation, lift-change, bijectivity, continuity of j, injectivity of
j, and stalk-transport proofs are complete Lean proofs.

Added one hole:
`AlgebraicGeometry.Scheme.FiniteEtale.arithmetic_exactSequence`. The packet also contains compiled finite-stage quotient construction helpers (`normalConstantQuotient`, `constantQuotientLimit`, and finite-algebra factorization), which reduce the remaining work to the geometric kernel and finite-stage compatibility argument.
(blueprint `lem-wf-arithmetic-exact-sequence`), in the new module
`Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticExactSequence`.
This is the only `sorry` in the packet. The item itself has zero `sorry`.
One upper hole closed and one strictly smaller source lemma added: this is a
**decomposition**, with net hole change zero, rather than a sorry-free proof of the
arithmetic exact sequence. No hole is inside a definition or a private declaration.

## No longer needed

Removed private proof imports from the item:

- `Sheaf.AlgebraicGeometry.FundamentalGroup.AlgebraicFieldLimit`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.CategoryTheory.Galois.AutProfinite`
- `Sheaf.CategoryTheory.Galois.GaloisTransitive`
- `WeilConjectures.FieldTheory.EtaleFieldGaloisClassification`
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected`
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`

The original Functoriality private import was also removed as redundant with the
preserved public Restriction import. Basic and Connected are similarly available
through Restriction. FLCFiber is not used: the public arithmeticStalk is already the
existing stalk restricted to FLC. The stalk proof uses the supplied equivalence and
canonical comparison directly; it does not invoke FiberEquivalence.

The arithmetic quotient and kernel dependencies of original proof steps 1–4 now
belong to the new exact-sequence node. They are not globally pruned: in particular,
`lem-wf-pi1-algebraic-field-limit`, `lem-exc-galois-krull-finite-limit`,
`lem-exc-etale-field-galois-classification`, `lem-galois-transitive`,
`lem-galois-aut-profinite`, and `thm-galois-fundamental` remain in that node's plan.
Their old tool-use approvals were removed from the parent's list when no longer used
directly; no new approvals were added.

The parent's finite-model path-construction steps 6–8 and surjectivity argument in
step 11 are replaced by the generic path-restriction torsor argument. Descent of all
morphisms, eventual equality of descended morphisms, and descent of inverse equations
are not needed for the path proof. The object clause of
`lem-wf-finite-etale-field-limit-descent` remains needed for j's injectivity.
No module is withdrawn, and no source-library declaration or proved dependency is
removed. Global module pruning: none.

## Where the brief, the DAG or earlier work was wrong

No false statement or target-signature error was found. The original twelve-step plan
is valid but longer than necessary for the path clauses. The proved source-library
fibre-functor isomorphism theorem allows the alternate torsor construction. Its
Mathlib-named analogue is not publicly available in the pinned imports, so the proof
imports the adopted source Prorepresentability module explicitly.

The exact-sequence result is a separate lemma in Stacks (0BTX); extracting it does not
restate the whole assigned theorem. It leaves a specific, independent mathematical
result for subsequent proof, with the original finite-Galois/stabilizer plan retained.
The node's unit has no realized statement or proof step that this change bypasses.

## New nodes

`lem-wf-arithmetic-exact-sequence`, under
`dag/nodes/sec-algebraic-groups-lie-algebras/`, states the continuous surjective
constant-cover quotient and its geometric kernel. Its Lean module is
`Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticExactSequence`. It retains the
first four source proof steps and their declared dependencies. The whole-blueprint
search for “arithmetic exact sequence” returned no matching imported node; the finite-
field-only HomotopyExactSequence source module is not a match for perfect K and
arbitrary algebraic closure L. LeanFinder, Loogle, and Mathlib grep searches found
only generic Galois-category tools. The parent node's proof, dependencies, and origin
now follow the compiled proof. No existing statement, definition, or Lean attachment
was changed, so no change record or consumer adaptation is required.

Finite-stage verification was rerun after the last import cleanup.

The exact-sequence proof was advanced during this session: regular finite normal
constant covers are identified with finite Galois groups; `fibreMultiplier` derives
left multiplication from naturality, `normalConstantQuotient` is continuous, finite
algebra maps factor through a finite normal stage, and `constantQuotientLimit` is assembled
using the continuous Galois inverse-limit equivalence. The remaining theorem body is
exactly the compatibility of this quotient with all finite etale covers and the kernel
identification using the algebraic-field-limit fundamental-group theorem.

The finite-stage construction was checked against the pinned Mathlib API: `Normal.algHomEquivAut` supplies the deck-group identification, `fiberConstantCoverEquiv_fiber_map` supplies precomposition, and `InfiniteGalois.continuousMulEquivToLimit` supplies the Krull inverse limit. The remaining kernel step is precisely the statement that compatible finite-stage restrictions are the geometric base-change image; no finite-stage quotient declaration is left holed.

The global DAG checker was run as an informational consistency check; its pre-existing repository-wide warnings are unrelated to this packet. The packet-specific JSON parses, import-direction checks pass, all Lean lines are within the style limit, and the exact-sequence module has exactly one intentional public `sorry`.

Change record: `coord/changes/arithmetic-lift-fibre-path-proof-imports.md`.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
