## What changed

Proved `AlgebraicGeometry.IsCurve.assertions_iff_disjoint_open_prime` from a
geometric biproduct decomposition and a general finite-sum comparison lemma.
Its signature and original docstring are unchanged. All added imports in the
original module are proof-only imports.

The geometric decomposition `AlgebraicGeometry.Etale.disjointOpenExtension_biproduct_iso`
is fully proved, for arbitrary schemes and commutative coefficient rings. Inside
the union, the counits induce a biproduct map. Restriction to a component kills
the other summands and makes that map invertible. Jointly surjective restriction
then proves it invertible globally; composition isomorphisms and preservation
of biproducts transport the decomposition to X. The proof covers the empty family.

The original theorem also proves that every component is constructible, using
Noetherianity of the curve and the existing open-closed constructibility theorem,
and that every component is killed by r, using additivity of pullback and extension
by zero. No definition or existing statement changed. The DAG now records this route.

## Proved and sorry left

Proved without a local sorry:
- `AlgebraicGeometry.IsCurve.assertions_iff_disjoint_open_prime`
  (`lem-pbc-q1-disjoint-open-prime-assertions`), conditional on the analytic lemma below.
- `AlgebraicGeometry.Etale.disjointOpenExtension_biproduct_iso`
  (`lem-pbc-t2-disjoint-open-extension-biproduct`).

The only sorry in this delivery is
`AlgebraicGeometry.IsCurve.assertions_iff_of_prime_biproduct_iso`
(`lem-pbc-t2-prime-biproduct-assertions`), in its own new module
`Sheaf.AlgebraicGeometry.Curve.PrimeBiproductAssertions`. This is the analytic part
of the old plan: the eight predicates for an arbitrary finite biproduct of
constructible sheaves killed by one prime, including transport along an isomorphism.
It has no opens or disjointness hypothesis and is independent of the geometric
lemma. Its docstring and node give the argument for all eight conditions and the
exceptional primary/invertible torsion cases. Edge cases checked mathematically:
empty family, zero summands, zero coefficient ring, characteristic zero,
characteristic equal to r, and distinct positive characteristic.

All three delivery modules compile locally without warnings. The geometric
lemma's axioms were checked separately with `#print axioms`.

## No longer needed

None of the original module's public imports can be removed: Assertions and open
extension by zero occur in its public statement. No original proof dependency
is claimed pruned from the transitive closure. The geometric stalk and cohomology
arguments are now owned by the respective new nodes, rather than restated in the
parent. Unneeded trial imports in the new modules were removed, including direct
imports of Mathlib's preadditive biproduct and ModuleCat abelian modules and the
source's universe-shrinking limits module. No unit statement or unit proof step
was bypassed.

The following old direct `proof_deps` are no longer used directly by the parent:
- `def-weil-pbc-eight-curve-assertions`
- `def-weil-pbc-etale-cohomology`
- `def-weil-pbc-geometric-stalks`
- `def-weil-pbc-primary-torsion`
- `lem-weil-pbc-cohomology-pullback-functorial`
- `lemma-weil-pbc-geometric-stalk-conservative`

They remain needed in the transitive dependencies of the two helpers; none is
claimed globally pruned. During second reading the geometric helper's proof-only
import `WeilConjectures.SixFunctors.OpenClosed.Complex` was replaced by the narrower
`WeilConjectures.SixFunctors.OpenClosed.Vanishing`, and the redundant direct import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts` was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The planned mathematical route works. Existing
`RetractAssertions` uses a coefficient-converted CurveCoefficientPair with
ULift integer coefficients, so it is not directly applicable to arbitrary Λ.
The source `Reductions.of_shortExact` imports this item and cannot be imported
here without a cycle. The needed finite-biproduct instance is a non-instance
theorem in Mathlib and is enabled locally in the new modules.

LeanSearch was unavailable (Internal Server Error); semantic, Loogle and source
searches were recorded without treating service failure as an absence result.
The cited primary texts were read at [03SC](https://stacks.math.columbia.edu/tag/03SC)
and [0A5C](https://stacks.math.columbia.edu/tag/0A5C); the local literature path named
by the existing node is absent on this machine. Blueprint searches found no
existing standalone node for either new statement. The ancestor helper returned
None because the previous stage-3 node records a module as created.item; its
explicit blueprint.from identifies dense-open-localization, which is retained
as the ancestor of both new nodes.

## New nodes

`lem-pbc-t2-disjoint-open-extension-biproduct`:
`Sheaf.AlgebraicGeometry.Curve.DisjointOpenExtensionBiproduct`, the fully proved
geometric sheaf decomposition. It generalizes the old first proof step by removing
all curve and coefficient finiteness hypotheses.

`lem-pbc-t2-prime-biproduct-assertions`:
`Sheaf.AlgebraicGeometry.Curve.PrimeBiproductAssertions`, the one remaining analytic
obligation, strictly separate from the geometric decomposition. No change records
are needed because existing statements and definitions are unchanged.

## Second reading by T2

1. Compared the existing module with the repository using `diff -u`: only four
   proof-only imports and the body of `assertions_iff_disjoint_open_prime` changed.
   Its signature, hypotheses (finite Λ, algebraically closed k, reduced curve,
   constructible r-killed F, finite pairwise disjoint opens), conclusion and
   docstring are byte-for-byte unchanged. No existing definition changes.
   Both other modules and their nodes are new. Verdict: pass.

2. Compiled all three delivery files in import order through `lcompile.py`, with
   no errors or warnings. Inspected every proof. The only local sorry is the
   named, reported analytic helper, with its own docstring and node. There are
   no forbidden declarations or hollow definitions. Scratch-copy `#print axioms`
   shows only propext, Classical.choice and Quot.sound for the geometric theorem;
   the parent and analytic helper additionally use sorryAx, as reported. Verdict:
   pass for a partial proof delivery; the original theorem is not axiom-closed.

3. Read all eight actual predicates in `Curve.Assertions`. The new analytic
   theorem separates a genuine part of the argument: it has no opens, disjointness,
   curve, reducedness, finite-ring or algebraic-closedness assumption; the parent
   establishes constructibility, annihilation and the geometric isomorphism.
   The common-prime condition handles the otherwise problematic conditional C3,
   C4 and C6 in the reverse direction. Checked an empty family, singleton family,
   zero summands, zero ring, characteristic zero, characteristic r, and distinct
   positive characteristic. In the exceptional cases a summand meeting the
   conditional torsion hypothesis is zero by coprime annihilators; otherwise the
   hypotheses hold uniformly. Thus both directions hold. Its docstring gives
   the full mathematical reduction, including transport and comparison naturality.
   Repeated searches with different wording using LeanFinder, Loogle and grep;
   found general biproduct tools, but no matching finite-sum assertion theorem.
   Read `RetractAssertions`, the private iso transport in
   `ReducedConstantLowerShriekAssertions`, and the disjoint decomposition in
   `Cohomology.Clopen`: respectively a different coefficient interface, only iso
   transport, and Zariski O_X-modules. None closes the analytic obligation in a
   few minutes. Verdict: true, properly split, not a restatement or duplicate.

4. Read the geometric proof downward: joint conservativity, disjoint-range
   vanishing, biproduct identities, invertible restricted counit, and composition
   of extension by zero. It proves the empty-open case without a nonempty-family
   assumption. The parent uses precisely this isomorphism and proves the two
   hypotheses needed by the analytic helper. Public imports of the new geometric
   module supply extension by zero and the module/sheaf categorical instances
   needed in its signature. Narrowed the proof-only Complex import to Vanishing
   and removed the redundant direct Mathlib biproduct-preservation import; a
   scratch compile confirmed both removals together. Listed all six removed
   direct parent dependencies under No longer needed, distinguishing them from
   global pruning. Read `dag/units/sk-thm-p1.json` including `realized`: no unit
   statement, realized step, or cited unit is bypassed. Verdict: pass after repairs.

5. Compared the parent node against the repository: only proof, proof_deps and
   proof_origin changed. Each proof_deps list is the union of its proof-step uses.
   The parent records constructibility/annihilation, geometric decomposition,
   and analytic comparison in exactly the Lean order. Both new nodes contain
   self-contained statements, sources, proof steps, dependency lists, search
   records, origin, creation and blueprint ancestry, chapter/unit, and verbatim
   Lean signatures. Their geometric and analytic plans match the code and the
   remaining obligation. Checked the cited Stacks texts at
   https://stacks.math.columbia.edu/tag/03SC and
   https://stacks.math.columbia.edu/tag/0A5C; the unrestricted generalization is
   explicitly attributed to the agent, rather than claimed as their statement.
   Verdict: pass.

Second reading changed only the geometric helper's proof imports and this report.
The existing theorem closes its one original local sorry; the geometric helper
is additionally fully proved, and one analytic theorem remains split off.
