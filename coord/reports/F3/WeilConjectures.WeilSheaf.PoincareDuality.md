## What changed

The signatures and visibility of all existing declarations in
`WeilConjectures.WeilSheaf.PoincareDuality` are unchanged. Two ingredient proofs now compile
from smaller, explicitly stated obligations.

For `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant`, negative degrees are
proved directly by the lower bound for a right derived functor on a degree-zero sheaf.
For the upper bound, smooth base change bounds the dimension of the geometric fiber;
`Etale.hasUniformDirectImageVanishingLE_two_mul` supplies the finite-coefficient bound.
The proof transports it through the etale/pro-etale comparison, applies the new constant-adic
coefficient lemma, and transports vanishing through the derived forgetful functor from Weil
sheaves and then through global sections. Properness is not used.

For `AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_baseChangeField`, the proof
constructs an isomorphism between algebraic closures over the base field, proves the
Frobenius power formula using the finite-field cardinality formula, constructs the geometric
fiber isomorphism using pullback associativity, and proves its Frobenius conjugacy by both
pullback projections. It applies the constructed cohomology equivalence and the separate
operator-compatibility lemma.

The new definition `AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso`
constructs the underlying equivalence without a new hole. It identifies Weil cohomology after
forgetting Frobenius with homology of derived global sections, using exact global sections
at the geometric point and the derived forgetful comparison. An exact pushforward equivalence
along the geometric isomorphism, its unit isomorphism, and the composition isomorphism for
derived global sections give the required equivalence. Its data are actual compositions of
library isomorphisms, not a witness chosen from an unproved existence theorem.

Four proof-only imports were added to the item: `Sheaf.WeilSheaf.AdicFiniteCoefficientBound`,
`Sheaf.WeilSheaf.CohomologyGeometricConjugacy`,
`WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing`,
`WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`. Existing public imports stay.
Two existing broad blueprint nodes have their proof routes updated only in the affected
clauses. No existing definition or statement changed; no forced adaptations or change records.

Validation: all four delivered modules compile through `lcompile.py`. A declaration-table
comparison confirms all seven existing declaration signatures are unchanged. The five node
records have matching proof dependencies, and each new Lean attachment matches its signature.

## Proved and sorry left

Closed two of the item's three original holes, both by decomposition:

- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant`.
- `AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_baseChangeField`.

The actual underlying linear equivalence is constructed in the new sorry-free definition
`AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso`
(node `def-pod-cohomology-geometric-equivalence`).

One original hole remains unchanged:

- `AlgebraicGeometry.WeilSheaf.exists_traceCup_isPerfect`: the trace and perfect-pairing
  ingredient of `thm-weil-poincare-duality` and `prop-poincare-pairing`, using the original
  `sk-cor-trace`, `sk-thm-derived-duality`, `sk-thm-transport`, and `sk-thm-frobenius` route.

Two new holes remain, each in its own module with its source and proof in words:

- `AlgebraicGeometry.ProEtale.isLE_rightDerivedFunctor_adicLowerStar_unit_of_finite_bound`
  (node `lem-pod-adic-unit-direct-image-finite-bound`). Still needs the comparison of the
  actual continuous integral constant sheaf with its torsion inverse system, compatibility
  of direct image with that realization, and passage to rational and algebraically closed
  coefficients. The library proves the range for abstract normalized towers in
  `WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange`, but its input is not yet
  connected to the actual `AdicSheaf.unit` used here. The target is explicitly a geometric point (`s` is an isomorphism).
  This lemma assumes the finite bound;
  it contains neither the dimension argument nor the negative-degree argument.
- `AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso_map_frobenius`
  (node `lem-pod-cohomology-geometric-conjugacy`). Still needs the coherence of the specified
  derived-global-section comparisons with the Frobenius transport and its iterates.
  The geometric isomorphism, its conjugacy, and the cohomology equivalence itself are
  already constructed. This lemma only asserts operator compatibility for that map.
  Isolated Lean checks prove composition of the constant-unit maps directly by
  `Mod.hom_ext` and `adicConstantSheafToLowerStar_comp`, and composition of their global
  section transports by `globalSectionsLowerStarIso_comp` and naturality. The remaining
  work is their derived coherence and compatibility with
  `IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso`, followed by homology.

This closes two upper holes and adds two lower holes: a decomposition, with net hole change
zero. No claim of an axiom-free proof of Poincare duality is made.

## No longer needed

No original import was removed and no entire existing node or module becomes unnecessary.
The second reader removed three redundant imports: the added proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` from the item,
`Mathlib.FieldTheory.IsAlgClosed.Basic` from `AdicFiniteCoefficientBound`, and
`WeilConjectures.WeilSheaf.Constant` from `CohomologyGeometricEquivalence`. Each remains
available through another retained import, so this removes direct import edges only;
no module is globally pruned.
The ordinary smooth range proof does not use the compact-support detour through
`lem-coef-integral-compact-support`, `lem-pod-point-sections-derived-reduction`,
`lem-pod-dvr-complex-amplitude-mod-uniformizer`, or proper/compact coincidence. Those nodes
remain needed for other clauses of `prop-cohomological-finiteness`, so they are not globally
pruned. The new coefficient-bound lemma concerns only the constant unit; no arbitrary-lisse
lattice selection, general constructibility theorem, trace map, duality, or tensor product
of Weil complexes is imported for these two reductions.

## Where the brief, the DAG or earlier work was wrong

The three ingredient statements in this source module have no exact `lean` attachment in
the corresponding broad Poincare blueprint nodes. The existing source proofs provide the
assembly and leave exactly these three ingredients open; the DAG's broad finiteness node
covers additional compact-support and degree-zero claims. Its other clauses and dependencies
were retained when updating the implemented smooth ordinary range.

The existing adic direct-image finiteness theorem gives an unspecified upper bound, which
cannot establish the required sharp bound `2*d`. Abstract normalized-tower realization gives
the sharp range but does not by itself identify the concrete continuous coefficient sheaf.
This is the reason for the new coefficient bridge.

Importing the smooth-dimension extension introduces a self-over-Spec instance represented by
`Spec.map (algebraMap k k)` rather than the identity representation used when the existing
cohomology definitions were elaborated. The range proof explicitly supplies the identity
self-over structure locally. No global instance or existing definition was changed.

The trace-isomorphism module imports `WeilSheaf.Finiteness`, which imports this item. It cannot
be imported here as a shortcut without an import cycle; the Finiteness module is held by F1,
and no change of our interface forces an adaptation of it. Moreover, its existential
degreewise perfect pairings do not supply the graded-commutative cup structure required
here: in odd middle degree, arbitrary invariant perfect pairings need not be alternating.

LeanSearch was attempted for both new obligations and returned an internal-server error.
The actual searches, including this unavailability, are recorded alongside successful
LeanFinder/Loogle and Mathlib grep searches. Blueprint searches for the two combined notions
returned no existing duplicate. The local checkout has literature lists and node texts but
not the full blueprint source documents; the source locations are those recorded by the
existing nodes. Milne's online LEC was checked for Theorems 15.1 and 19.2.

## New nodes

`lem-pod-adic-unit-direct-image-finite-bound` is the finite-to-adic coefficient step of the
ordinary range proof. Its source is the finite-level and rationalization argument in
`prop-cohomological-finiteness`, Steps 5-7, with the constant-sheaf inverse-limit argument of
Milne LEC, Theorems 15.1 and 19.2. Its target is a geometric point, avoiding an
unneeded general relative coefficient comparison. The bound is a hypothesis; smooth dimension is established
in the item. Empty schemes, bound zero, and a geometric point cause no edge-case failure.

`def-pod-cohomology-geometric-equivalence` records the actual linear equivalence induced by
an isomorphism of geometric fibers. It has no proof hole and fixes the specific map used
by the operator lemma. It serves the canonical identification in the base-change clause
of `thm-weil-poincare-duality` and does not change any old definition.

`lem-pod-cohomology-geometric-conjugacy` is the operator-transport step of that base-change
clause. It takes an arbitrary geometric isomorphism with a conjugacy equation, and proves
compatibility for the already constructed map; it does not assert the existence of that
isomorphism or construct the field embedding. Negative degrees and empty schemes are
trivial cases; exponent zero is also covered whenever its conjugacy hypothesis holds.

## Second reading by F3

1. Compared the complete item with the repository version, then independently compared
   all seven declarations with `stage3_delivery.decl_table`. Every existing statement
   is byte-for-byte identical, with the same declaration kind, visibility, and docstring.
   Only two theorem bodies, the module explanation, and proof-only imports change.
   No existing definition or target statement changes, and no adaptation is delivered.
   Checked the two existing node records field by field: their statements, statement
   dependencies, and unit assignments are unchanged. Verdict: passes.
2. Compiled all four delivered modules through `lcompile.py --all`, and inspected every
   declaration and every `sorry`. The item has exactly its original named trace-cup hole;
   the two added holes are exactly the two named theorems listed above. There is no
   hollow definition, custom axiom, unsafe declaration, external implementation, or
   skipped kernel check. The new equivalence is a composition of explicit library
   isomorphisms, not a chosen witness of an open existence theorem. The independent
   axiom check uses scratch copies with `#print axioms` for all delivered declarations;
   the output contains only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`. The new equivalence itself has no syntactic hole but inherits
   `sorryAx` from library comparisons; it is not claimed to be axiom-free. Verdict: passes
   as a decomposition, not an axiom-free proof of the item.
3. Read both new theorem signatures and their complete proof docstrings. The coefficient
   obligation is only passage from the assumed finite bound to the constant adic unit;
   the item proves nonnegativity, the dimension bound, finite-coefficient vanishing,
   and the transports to Weil cohomology. Its target is a geometric point, not an
   unrestricted relative base. The coefficient sheaf in `Adic.Module` is defined using
   locally finite continuous functions; the finite-extension passage concerns that
   definition. The conjugacy obligation concerns the specified equivalence only; the
   item actually constructs the geometric isomorphism and proves conjugacy on both
   projections. Neither new theorem restates an original ingredient. Empty schemes,
   degree zero, negative degrees, the identity field extension, and r=0 whenever its
   conjugacy hypothesis holds give no counterexample. Repeated searches with different
   words via LeanFinder, Loogle, Mathlib grep, and `rg` in both library roots found no
   duplicate. Reviewed the nearby proper finite-coefficient bound and normalized-tower
   range theorem: neither supplies the missing concrete coefficient comparison. The
   conjugacy coherence is not a few-minute consequence of the existing composition
   lemmas because it also passes through the specified derived forgetful comparison.
   Milne LEC Theorems 15.1 and 19.2 were independently checked at
   https://www.jmilne.org/math/CourseNotes/LEC.pdf. Verdict: both true, needed, and
   strictly part of the original argument; neither newly added hole was closed.
4. Read the complete source module, retained proof dependencies, the two unit records
   `sk-lem-finite` and `sk-thm-poincare-duality`, including their `realized` fields (empty
   in this snapshot). The ordinary range follows their finite cohomological-dimension
   and coefficient-extension steps; Frobenius base change follows their finite-field
   operator convention. The trace/duality route remains open and untouched. The broad
   finiteness node still covers compact support and degree zero, so its other existing
   dependencies remain required: none is globally pruned. Removed the three redundant
   imports enumerated under No longer needed. A trial private import of CohomologyExact
   failed because the actual public definition needs its exact-sections instance;
   retained its public import as a construction dependency. Verdict: route preserved,
   no shorter applicable library result found, imports pruned.
5. Matched the three new Lean signatures against their node attachments and checked
   that every proof dependency exists and is the union of the steps' uses. Corrected
   the equivalence node's empty proof/proof_origin to describe its actual construction,
   including the exact-point-sections dependency, and matched its signature in the delivery parser's `def` format. Existing broad-node proof routes keep their unimplemented clauses as well
   as the implemented reductions. Verdict: node records agree with this partial work.

Second reading changed only redundant imports, the equivalence node's construction
metadata, and this report. No mathematical statement or existing definition changed.
Two original holes are closed by two lower obligations, giving net zero holes, with
no entire module pruned.
