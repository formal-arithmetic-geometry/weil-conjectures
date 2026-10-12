## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.EtaleLimitCohomologyClassDescent
with a complete Lean induction on the cohomological degree. The induction generalizes
all coefficient systems, colimit sheaves, stage cohomology diagrams and canonical cocones.
It uses two new proof-only imports: EtaleLimitCohomologyDegreeZeroDescent and
EtaleLimitCohomologyConnectingLadder. No existing signature or definition changed.
The original node now records this degree-induction proof.

The zero case applies section descent. In successor degree the ladder supplies a
cokernel coefficient system in the preceding degree and a surjective connecting map.
The proof lifts a target class, applies the induction hypothesis to the new system,
and evaluates the ladder's commuting square on the resulting representative.
This is a decomposition, not a proof free of downstream sorries.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.etale_limit_cohomology_class_descent
(lem-weil-pbc-etale-limit-cohomology-class-descent). The item's module has no sorry.

Added, each in its own module, with exactly `:= by sorry`:

- AlgebraicGeometry.Etale.etale_limit_cohomology_degree_zero_descent
  (lem-weil-pbc-etale-limit-cohomology-degree-zero-descent).
- AlgebraicGeometry.Etale.etale_limit_cohomology_connecting_ladder
  (lem-weil-pbc-etale-limit-cohomology-connecting-ladder).

Thus one upper hole is closed and two lower holes are added: net minus one.
The first is restricted to degree zero. The second constructs a smaller-degree
system and connecting maps; it asserts no stage descent for that system.
The main proof genuinely combines them by induction and two image equations.
All three sandbox modules compiled locally in import order with no warnings.
The first delivery dry run also passed the server compiles and stage-3 preflight,
except for the intentionally absent second reading.

## No longer needed

Removed all old proof-dependency imports from the item's module:

- Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
- Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
- Sheaf.AlgebraicGeometry.EtaleMayerVietoris
- Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback
- Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
- Sheaf.AlgebraicGeometry.LimitAffineTransition
- Sheaf.CategoryTheory.CohomologyColimitSites
- Sheaf.CategoryTheory.ColimitSites
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

The geometric site construction, affine restriction equivalence, cofinal tails,
and pullback functoriality remain needed in the new nodes' proofs: removing their
direct imports is not a claim that those modules leave the entire target closure.
The full higher-degree site-continuity theorem is not used as a premise, avoiding
its degree induction as an additional black box. The new route uses its source's
injective/Cech argument directly through the connecting ladder.

This branch no longer needs lem-weil-pbc-etale-mayer-vietoris,
lem-weil-pbc-etale-mayer-vietoris-pullback, lem-weil-pbc-five-lemma or
lem-weil-pbc-separated-affine-open-intersection. The two corresponding Mayer-Vietoris
modules and the full CohomologyColimitSites module are unnecessary premises on this
branch. No claim is made that other targets or the eventual-vanishing sibling
no longer use them. The statement-level imports remain unchanged.

Every old `proof_deps` entry is removed from the main node's direct proof route:

- lem-weil-pbc-inverse-image-composition
- def-weil-pbc-abelian-etale-sheaves
- def-weil-pbc-category-colimit
- def-weil-pbc-cohomology-pullback
- lem-weil-pbc-cohomology-pullback-functorial
- lem-weil-pbc-limit-affine-transition
- lem-weil-pbc-colimit-initial-full-subcategory
- lem-weil-pbc-affine-etale-site-topos
- lem-weil-pbc-affine-etale-site-colimit
- lem-weil-pbc-colimit-of-sites
- def-weil-pbc-sites-and-cohomology
- def-weil-pbc-direct-image
- def-weil-pbc-inverse-image
- lem-weil-pbc-cohomology-colimit-of-sites
- def-weil-pbc-scheme-conventions
- lem-weil-pbc-left-adjoint-preserves-colimits
- lem-weil-pbc-etale-inverse-image-restriction
- lem-weil-pbc-etale-mayer-vietoris
- lem-weil-pbc-etale-mayer-vietoris-pullback
- lem-weil-pbc-filtered-colimit-abelian-groups-exact
- lem-weil-pbc-five-lemma
- lem-weil-pbc-separated-affine-open-intersection

The Lean induction directly uses only the two new nodes. Some old entries remain
statement dependencies or ingredients of the new nodes; the list records removal
from the direct proof route, not removal from the whole library or target closure.
In particular `lem-weil-pbc-cohomology-colimit-of-sites` is no longer a premise.

## Where the brief, the DAG or earlier work was wrong

The old DAG proposed full continuity and two finite-cover Mayer-Vietoris inductions
to establish existence alone. The shorter degree induction from Stacks 09YP/0739
suffices. The new nodes retain the qcqs finite-cover work in degree-zero section
comparison and in descent of finite Cech data, rather than assume successor-degree
continuity in the acyclicity argument.

The existing generic site ladder is not directly applicable: its site diagrams,
unit-compatible pullbacks and object-cohomology endpoint identifications must first
be constructed from the scheme diagram. The new ladder records that translation
for the given Sheaf.H and cohomologyMap encoding. Existing fixed-base class descent
requires torsion and does not cover the varying unrestricted sheaves here.

Edge cases checked mathematically: n=0 uses the usual H^0 connecting map; zero
coefficients and empty schemes give the zero groups; a one-object index gives the
ordinary long exact sequence. Identity and composition laws of the original and
cokernel coefficient systems are retained explicitly. Neither new theorem asserts
or assumes finite-stage detection of zero.

The node belongs to sk-thm-p1 but is not itself one of that unit's realized statement
or steps. None of those nodes or the unit/chapter route is replaced. Sources were
checked at Stacks Tags 09YQ, 09YP, 0EXZ and 0739. LeanSearch returned an Internal
Server Error; LeanFinder, Loogle and source grep were available.

## New nodes

lem-weil-pbc-etale-limit-cohomology-degree-zero-descent states degree-zero descent
with the original coefficient and cocone identifications. Its proof is the finite
section comparison of 09YN transported through affine etale restriction, with finite
qcqs cover equalizers. It is in EtaleLimitCohomologyDegreeZeroDescent.

lem-weil-pbc-etale-limit-cohomology-connecting-ladder constructs a compatible
cokernel system in the preceding degree, a surjective limit connecting map and
commuting stage maps. Its proof uses the compatible injective-system construction
0EXZ, exactness, degree-zero Cech comparison, the acyclicity criterion and connecting
map naturality, as in 09YP/0739. It is in EtaleLimitCohomologyConnectingLadder.
There are no change records because no existing statement or definition changed.

## Second reading by F1

1. Compared the delivered main module with the repository using diff and compared
   its theorem signature byte for byte: identical. Only its imports, source/proof
   docstring and proof body differ. No existing definition changed, and the two
   additional modules are new. No change record is required. Verdict: pass.
2. Compiled all three modules locally in dependency order with lcompile.py: exit
   code zero, no warnings. Scanned the files for forbidden declarations and proof
   escapes: none. There are no definitions or arbitrary data chosen from an
   unproved existence theorem. The main proof eliminates the ladder existential
   only inside its proposition proof. Exactly the two reported public named
   theorems have `:= by sorry`. A scratch module printed axioms for all three:
   propext, Classical.choice, Quot.sound and sorryAx only. The last remains because
   the intermediate results are open. Verdict: valid decomposition, not an
   axiom-free completed target proof.
3. Read both split statements, their docstrings and nodes against Stacks 09YP,
   0739, 0EXZ and 03F9. Degree zero is a genuine special case. The ladder constructs
   a lower-degree system and surjective compatible boundary, without asserting
   descent for that system. It follows by compatible injective embeddings,
   cokernels, exact filtered colimits and Cech acyclicity. Its Cech step needs
   the full degree-zero section comparison, including equality detection, as
   explicitly recorded in its node; the new degree-zero surjectivity lemma alone
   would not suffice. Checked degree zero, zero coefficients, empty schemes and
   the one-object system. Repeated LeanFinder, Loogle and grep searches with
   different terms and read the existing generic site ladder and degree-zero
   descent modules. They require site presentations and endpoint transports
   absent from these scheme-specific inputs; fixed-base and torsion results
   likewise do not directly apply. Neither hole can be closed in a few minutes
   without substantial site transport work. Verdict: true, strictly smaller
   steps of the argument, not renamed copies of the assigned theorem.
4. Read the generalized induction from the top: the zero case uses exactly its
   special-case lemma; the successor lifts through the boundary, uses the
   induction hypothesis on the new coefficients and evaluates the commuting
   square. Both new imports are used and are proof-only. The sole public import
   is needed by the signatures. Checked sk-thm-p1 realized: this item is not a
   realized statement or step, and the unit record is unchanged. The pruning
   section now enumerates every old direct proof dependency, distinguishing
   direct removal from possible retention in downstream proofs. Verdict: pass.
5. The existing node differs only in proof, proof_deps and proof_origin, matching
   the Lean induction and its two applications. Both new nodes have matching
   Lean signatures, source, self-contained statements, proof steps, dependency
   union, origin, searches, creation and blueprint records, chapter and unit.
   Every cited dependency node exists. Verdict: pass.

Second reading changed only metadata: completed the pruning accounting, added
independent LeanFinder and Loogle search records to both new nodes, and wrote
this review. No Lean repair was needed. One original hole is closed, two are
added, and the net hole count is minus one; this delivery is a decomposition.
