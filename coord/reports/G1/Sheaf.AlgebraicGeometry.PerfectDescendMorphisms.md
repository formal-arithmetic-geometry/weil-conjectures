## What changed

`Sheaf.AlgebraicGeometry.PerfectDescendMorphisms`: replaced the proof of
`AlgebraicGeometry.perfect_descend_morphisms` by a complete Lean reduction, with its original
signature unchanged. The proof lifts a morphism and its inverse, transports them to the same
stage, makes both inverse identities true at a common later stage, and constructs an `IsIso`
instance. For finitely many equalities it chooses a common upper bound of their individual
stabilization stages, including the empty-family case. Cancellation converts all conjugated
transport equations to the exact equations in the existing signature.

`Sheaf.AlgebraicGeometry.PerfectHomTransport`: added explicit canonical comparison and
conjugated Hom transport constructions, with proved identity, composition and equality-cancellation
lemmas, including compatibility with finite-stage transitions. The chosen composition family is named once as `perfectHomComposition` to avoid
repeatedly unfolding its universal-property construction during elaboration. The fixed
comparison is definitionally the expression previously defining
`perfectDescentComparison`. That old name is now an abbreviation of the shared construction,
so no separate choice or new pullback functor is introduced. The necessary public import and
alias change are recorded in `coord/changes/perfectDescentComparison-shared.md`. The original
comparison value and every existing statement remain definitionally unchanged; no downstream
module requires adaptation.

`Sheaf.AlgebraicGeometry.PerfectHomContinuity`: isolated the geometric Hom-continuity argument
from the affine calculation and quasi-compact-open induction. Its conclusion gives representatives
on cofinal tails and eventual equality of a single pair on an entire tail. It does not contain
isomorphism descent or finite simultaneous relations. The transport-coherence theorem is a
separate categorical equation, without perfectness, finite presentation or colimit hypotheses.
It is now proved from the associativity law of the fixed derived-pullback comparisons:
first prove associativity of conjugation, then transport along the projection equations,
then use composition of base-change maps and the cocone equation.

All three modules compile together through lcompile.py. The combining proof has no local holes.
The new statements were checked at the single-stage system, empty scheme, zero objects,
identity transitions and empty finite-family boundary cases; none needs an added hypothesis.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.perfect_descend_morphisms`
(node `lem-pc-perfect-descend-morphisms`). Its Lean proof is complete from the named dependencies.
This is a decomposition, not a proof independent of sorry: one original hole is closed and one
lower hole is added. The ledger net for this delivery is therefore 0 before any pruning effects.
The earlier sandbox attempt also left `AlgebraicGeometry.perfectLimitMap_stage` with sorry;
that hole has now been closed from `exists_derivedPullbackComposition`, without adding a hole.

The delivery leaves exactly this one whole-theorem hole:

- `AlgebraicGeometry.perfect_hom_continuity`, node `lem-pc-perfect-hom-continuity`, in
  `Sheaf.AlgebraicGeometry.PerfectHomContinuity`.

Every helper and construction is complete; no definition has a hole. The original module has
no remaining sorry. The complete natural-language argument and source for the remaining
hole are in its declaration docstring and DAG node. All categorical transport lemmas
are proved, including `perfectHomMap_trans` and `perfectLimitMap_stage`.

## No longer needed

Second reading also removed `Mathlib.CategoryTheory.Limits.Types.Filtered` from
`PerfectHomContinuity`: its statement and current proof do not use this import.

Removed the following proof imports from the original module:

- `Sheaf.AlgebraicGeometry.AffinePerfectHomColimit`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.DerivedAdjoint`
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle`
- `Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction`

These are relocated to the Hom-continuity subproblem, not pruned from the targets' import closure.
Their nodes (`lem-pc-affine-perfect-hom-colimit`, `lem-pc-affine-qcoh-derived-equivalence`,
`lem-pc-ringed-spaces-derived-adjoint`, `lem-pc-derived-mayer-vietoris-triangle`,
`lem-pc-perfect-affine-bounded-projective`, `lem-sc-invert-s-cohomology-induction`) and the
five-lemma node remain needed there. No module or mathematical dependency is claimed globally
pruned. The item's proof-dependency list now names only the two new auxiliary nodes.

## Where the brief, the DAG or earlier work was wrong

The module's REPAIR notice is stale: the starting comparison definition was already the fixed
counit-pinned construction, not a hollow definition. Its alias refactoring shares that exact
construction and does not choose data from an arbitrary existential theorem.

The DAG's final step is mathematically correct, but much longer than an elementary Lean step:
it needs conjugation, two inverse identities and a finite upper-bound argument. Those parts now
have explicit proofs. The earlier affine/gluing lemmas do not themselves state geometric Hom
continuity with canonical transition maps, so applying them directly does not close the original
hole. That genuine geometric step is now separately stated with the source's proof plan.

The local literature tex files are absent on this machine. Source text was read at the official
Stacks pages https://stacks.math.columbia.edu/tag/09RE and
https://stacks.math.columbia.edu/tag/0D5S. LeanSearch returned Internal Server Error for both new
statements; the node search records say unavailable. LeanFinder, Loogle and source grep were
also run; no exact Mathlib or existing project theorem was found. Blueprint searches found no
existing node for either new statement. The unit's realized arrays are empty and its route is
unchanged: the affine calculation and open induction still remain below the continuity lemma.

## New nodes

`lem-pc-perfect-hom-continuity`: cofinal-tail representatives and eventual equality for one pair
of Hom representatives, the n=0 consequence of the affine/gluing Hom-colimit argument. It is
strictly the input to the inverse and finite-family proof, not the original conclusion renamed.

`lem-pc-perfect-hom-transport`: the canonical transport constructions and compatibility of
transport through a later finite stage with transport directly to the colimit. It is a universal
composition-coherence equation, not geometric descent. Identity and composition preservation,
cancellation, composition of successive transport maps, and limit/stage compatibility
are all proved in its module; this node has no local sorry.

Change record: `coord/changes/perfectDescentComparison-shared.md`.

## Second reading by G1

1. **Visible statements and data: pass.** Compared the entire delivered original module
   with the repository using `diff -u`, then compared the theorem signature as raw text:
   `perfect_descend_morphisms` is byte for byte unchanged. The only existing data change
   is the declared `def` to `abbrev` refactoring of `perfectDescentComparison`, covered by
   `coord/changes/perfectDescentComparison-shared.md`. A scratch Lean example proves by
   `rfl` that its new value is the exact old choose/eqToIso expression. The chosen family
   comes from the pinned derived universal property; it is not an arbitrary existence
   witness. No target meaning changes, no downstream proof adaptation is needed.

2. **Proof and axioms: pass, with the reported lower hole.** Compiled all three modules
   in import order with `lcompile.py --all`; no errors or warnings. Read every transport
   proof: `cc_assoc` extracts associativity from the fixed comparison family, `tr_assoc`
   uses naturality and inverse cancellation, `trTo_assoc` handles projection equalities,
   and `perfectLimitMap_stage` uses base-change composition and the cocone equation.
   Read the main proof through both inverse identities and the finite upper-bound step.
   A scratch import printed axioms for all 15 public declarations: only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` occur. The imported foundational
   statements are not all closed, so even the locally complete helpers retain `sorryAx`.
   The only local sorry is the entire named theorem `perfect_hom_continuity`.
   No forbidden declaration, unsafe implementation, or definition hole occurs.

3. **Split statements: pass after correcting the transport node's notation.** Read
   Stacks [09RE](https://stacks.math.columbia.edu/tag/09RE), including its affine Hom
   calculation and open induction, and [0D5S](https://stacks.math.columbia.edu/tag/0D5S).
   Hom continuity has the same directed diagram and cocone, starting index, finite
   presentation (= locally finite presentation plus quasi-compact and quasi-separated),
   derived-category instances and two perfect objects as the item. Its first clause
   is surjectivity on a cofinal tail, its second is eventual equality of one pair.
   They are true consequences of the n=0 Hom comparison bijection. Inverse descent and
   simultaneous finite relations are absent and are actually proved in the main module:
   this is a genuine decomposition, not a renamed target. The single-index constant
   diagram reduces to bijectivity along canonical isomorphisms; zero objects and the
   empty scheme have singleton Hom sets; directedness and the given index exclude an
   empty index system without a new hypothesis. No linear order or antisymmetry is used.
   Transport requires neither perfectness nor a colimit; it is categorical coherence.
   Corrected its prose formula to the usual right-to-left composition convention,
   matching the Lean conjugation. The docstring gives the affine, gluing, cofinality
   and equality arguments and names the node. Repeated Mathlib searches with a different
   LeanFinder query (derived-category perfect Hom and filtered direct limit scheme base
   change), Loogle `CategoryTheory.Functor.map_comp`, and grep; only general localization
   and functoriality facts were found. Searched the current Lean library and upstream
   algebraic-geometry checkout for Hom continuity and descent: the affine dependency
   exists but does not state the geometric result. No shorter geometric theorem found.

4. **Route and pruning: pass.** The starting proof imports and old proof dependencies
   are accounted for in `No longer needed`. The six geometric/affine modules are moved
   under continuity, not globally pruned; the five-lemma dependency remains there too.
   Read `affine_perfect_hom_colimit` and `quasiCompactOpen_induction`: the former only
   handles affine module complexes and the latter supplies the stated open induction,
   so neither alone closes geometric continuity. The bounded-projective equivalence,
   Mayer--Vietoris and adjunction inputs remain on that route. The unit
   `sk-thm-picard-semicon` has empty realized statement and step arrays; no realized
   node or chapter route is bypassed. The new public import is needed in the shared
   comparison's public definition; proof-only imports remain plain. Removed the unused
   `Mathlib.CategoryTheory.Limits.Types.Filtered` import. The empty finite family in the
   main proof still has a witness because `Nonempty I` is obtained from the initial j.
   Closing the remaining geometric theorem requires a substantial affine/gluing
   development, not a short missing application.

5. **DAG and report: pass after documentation fixes.** The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`; its three steps match the Lean lift,
   inverse and finite-family arguments. Its dependencies are the two new nodes. Read
   both new records: their source, complete statements, dependency union, proof route,
   searches, creation/blueprint metadata and Lean records match the declarations.
   Transport's only proof dependency is the fixed derived-pullback composition node.
   Continuity retains the affine and quasi-compact-open induction proof plan and all
   its inputs. Corrected the gluing step's reference to the affine case from Step 2
   to Step 1. Added missing module-title and blueprint markers to the new modules.

Second-reading changes: corrected the new transport node's two composition formulas,
corrected the continuity node's step reference, removed one unused proof import, added
module-doc blueprint/title markers, and recorded this independent review. No theorem
signature or mathematical proof changed. Holes closed: `perfect_descend_morphisms` (one);
holes added: `perfect_hom_continuity` (one). Net zero: decomposition, no global pruning.
