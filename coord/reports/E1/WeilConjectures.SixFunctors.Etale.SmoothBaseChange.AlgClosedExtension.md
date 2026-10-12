## What changed

Replaced the sole original sorry in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` by a
compiled acyclic-module argument. The two existing declaration signatures and
all four existing public imports are unchanged. New imports are proof-only.
The proof shows n annihilates the constant sheaf, lifts it to a Z/n-module
sheaf, proves comparison simultaneously for all module sheaves by induction
on degree, and transports through the coefficient isomorphism. The successor
step uses the existing injective-effacement ladder and the right-exact five lemma.

The second reader repaired the curve corollary to keep the blueprint's route:
reduce to connected smooth curves, obtain a smooth proper compactification,
apply `IsConnectedCurve.constant_cohomology_baseChange_compatible` from the
curve-estimate chapter, and cancel the bijective map coming from the constant
sheaf comparison isomorphism. Its statement is unchanged. This uses two more
proof-only imports, Curve.ConstantInvariance and CurveCohomologyConnectedReduction.

Added three geometric-input modules under Sheaf.AlgebraicGeometry, and a node
indexing the previously unindexed existing general qcqs source declaration.
The curve node now records its actual repaired proof, retaining its old
curve-invariance and cohomology dependencies. New-node unit labels were repaired
to the item's node's unit, sk-thm-vanishing, in sec-smooth-base-change.

## Proved and sorry left

Proved relative to the named input theorems:
`AlgebraicGeometry.bijective_cohomologyMap_constantZMod`, the one original sorry.
The private `bijective_cohomologyMap_of_acyclic_modules` is a complete induction
for arbitrary n; no primality assumption was introduced. The curve corollary
is also fully proved by the required curve-estimate route. The item module has
no sorry. Its imported existing proof obligations are not claimed closed.

Three new sorry declarations remain, each exactly `:= by sorry`, with a source,
complete natural-language proof, and matching node:

- `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_algClosed_extension`
  (lem-sc-algclosed-extension-module-sections): global sections only, arbitrary
  field extension K/k from algebraically closed k, every n and every X.
- `AlgebraicGeometry.Etale.subsingleton_cohomology_upperStar_injective_algClosed_extension`
  (lem-sc-algclosed-extension-injective-acyclic): positive cohomology only of
  inverse images of injective module sheaves, with n invertible and f qcqs.
- `AlgebraicGeometry.bijective_curve_cohomologyMap_of_connected`
  (lem-sc-curve-cohomology-connected-reduction): finite-component assembly with
  comparison for all connected smooth curves as an explicit hypothesis. It
  proves no connected-curve comparison; that comes from the existing
  curve-invariance theorem in the item's real Lean proof.

The existing degree-zero comparison, effacement ladder and killed-sheaf
module-lift theorems already have complete Lean proofs. Their transitive
remaining obligations are unchanged. A scratch copy printed axioms for the
private helper, both existing declarations and all three split declarations:
only propext, Classical.choice, Quot.sound and sorryAx (open inputs).

## No longer needed

None of the old public imports, old node proof dependencies, unit statements
or realized steps were pruned. In particular thm-sc-constant-invariance and
its Curve.ConstantInvariance module are retained and actually applied by the
curve corollary. The old def-weil-pbc-etale-cohomology dependency is retained.
The additional proof imports each provide a declaration applied in a proof.
Every public import of a new module is required by its statement.

The old inline sketch for the general qcqs theorem used a smooth-subalgebra
approximation and smooth base change directly; the new assembly uses the
geometric acyclicity and section inputs instead. That sketch had no imported
modules or existing node proof_deps to prune. No source module is asserted to
leave the targets' closure. The proper/affine, Picard, Kummer and Jacobian lanes
remain in use through the existing curve-invariance module.

## Where the brief, the DAG or earlier work was wrong

The original module had no node whose lean.module indexed its general qcqs
source declaration. Its docstring references sk-prop-ext-invariance, a unit,
whose statement is for smooth separated curves. That unit cannot by itself
prove the broader qcqs statement. A new node records the exact existing qcqs
statement, without weakening it to curves or pretending it realizes that unit.

The first worker's proposed curve-node update bypassed thm-sc-constant-invariance.
Keeping unit record files untouched would not preserve that route. The second
reader repaired the Lean corollary itself to apply the existing curve theorem
and recorded its component assembly as a strictly smaller conditional lemma.
There is no renamed whole-item comparison theorem left with sorry.

The relative field-extension exchange source is Stacks 0F1C. It presently lacks
usable Lean code and remains a genuine proof obligation of the acyclicity input.
Its proof in Stacks uses smooth base change. A future implementation must avoid
an import cycle: this module is imported by the smooth-base-change theorem.
The repaired curve corollary no longer uses the general qcqs theorem, so extracting
that independently proved curve lane into a separate module would allow a future
acyclicity proof to import smooth base change without a logical circular proof.
No such import or extraction is made in this delivery.

The first worker incorrectly cited 0F0B as cohomology over a separably closed
base in the acyclicity docstring. The second reader corrected it to 03QU,
consistent with the node. 0F0B remains the correct source for the general qcqs
comparison statement, not for the base acyclicity argument.

The general ModuleAcyclicCohomologyComparison theorem has a prime binder that
is unnecessary here. Its existing degree-zero and effacement-ladder components
have no such binder; the private induction uses those components unchanged.

Independent LeanFinder, Loogle, Mathlib grep, and rg searches with different
wording found no existing scalar-extension module comparison or finite-curve
component comparison theorem. The existing sets-valued field-extension section
invariance and finite-coproduct cohomology assembly were read; neither states
the new assertions. LeanSearch was unavailable to the first worker (Internal
Server Error), which is recorded rather than treated as an empty search result.

## New nodes

lem-sc-algclosed-extension-module-sections indexes
Sheaf.AlgebraicGeometry.AlgClosedExtensionModuleSections. Its source is Stacks
0A3I with the coefficient-forgetting inverse-image and unit comparison. Edge
cases n=0, n=1, X empty and K not closed are included.

lem-sc-algclosed-extension-injective-acyclic indexes
Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic. Its proof uses the
relative field-extension exchange 0F1C, source abelian acyclicity 03FD and exact
sections over separably closed fields 03QU, plus the existing module-encoding
and inverse-image coefficient comparisons. n=0 is excluded by hn; n=1 and X
empty give zero groups.

lem-sc-curve-cohomology-connected-reduction indexes
Sheaf.AlgebraicGeometry.CurveCohomologyConnectedReduction. It is the finite
clopen-component assembly in the blueprint's first curve-invariance step.
Its hypothesis supplies the connected-curve comparisons; their proofs are
not moved into this lemma. Empty C, n=0, n=1 and q=0 are allowed. A connected
curve gives just the supplied comparison, and a disjoint union gives its product.

lem-sc-qcqs-algclosed-extension-invariance indexes the existing general source
declaration in the item module (the record indexes this delivery of the source
file; lean.existing=false is the required file-delivery convention). Its Lean proof assembles
the two geometric inputs through existing homological tools and transports the
constant coefficients. It is not substituted for the curve-estimate unit.

All node Lean signatures are copied verbatim from the delivered files. No
change record is needed: no existing statement or definition changed.

## Second reading by E1

1. Compared the item's complete diff and both existing declaration signatures
   with the repository version. Verdict: unchanged signatures and existing
   public imports; no target statement or definition changed. New imports in
   the item are plain import, including the curve-estimate route imports.
2. Compiled every delivery file in import order, and compiled a scratch copy
   with #print axioms for all relevant declarations. Verdict: complete proofs
   in the item, three listed public named sorry theorems in new modules, no
   hollow definitions or forbidden declarations, and only permitted axioms
   plus sorryAx from open inputs. The private helper is a real induction, and
   the transports use naturality of the exact canonical cohomologyMap.
3. Read both original split statements, their complete docstring proofs, and
   the primary Stacks sources 0A3I, 0F1C, 03FD and 03QU; checked n=0, n=1,
   empty X, q=0 versus positive q, and K not closed where allowed. Repeated
   three search kinds with different queries and read the existing related
   declarations. Verdict: true geometric inputs, properly smaller obligations;
   no duplicate or restatement. The added curve reduction was similarly
   checked against the finite-product assembly and small component cases.
4. Read the original proof deps and both relevant unit records. Verdict after
   repair: the curve corollary genuinely uses the curve-estimate theorem and
   compactification; no unit step or module of that lane is pruned. The general
   qcqs induction uses the existing shortest degree-zero/effacement route.
   No unused proof import or required public-signature import was found.
5. Compared every delivered node's proof, proof_deps union, source, Lean
   signature and unit label against the code and the item's original node.
   Verdict after repair: the curve node describes its actual repaired proof;
   the general node describes its actual induction and transports; split nodes
   include the module-encoding and coefficient comparisons they need. All
   referenced node ids exist. Unit realized records are unchanged, and their
   curve-estimate lane is retained rather than bypassed.

Changed on second reading: repaired the curve corollary to follow the unit
route, added the conditional connected-component reduction module and node,
corrected the acyclicity source tag, corrected new-node units and source-declaration
metadata, made node signatures verbatim, expanded missing
comparison dependencies, and rewrote the report to match the final delivery.
