## What changed

Replaced the hole in CochainComplex.exists_tensorPullback_stalk_complex_iso with a
complete Lean proof from stalkChangeOfRingsIso and a new inverse-image scalar-transport
lemma. The proof chooses the explicit ring map, derives naturality on tensor generators,
and assembles the termwise isomorphisms after proving the differential squares from he.
No existing declaration signature or definition changed.

## Proved and sorry left

Closed: CochainComplex.exists_tensorPullback_stalk_complex_iso (one hole).
Added: exists_ringed_inverseImage_stalk_scalar_transport (one hole), node
lem-pc-ringed-inverse-image-stalk-scalar-transport, in the new module
Sheaf.Algebra.Homology.InverseImageStalkScalarTransport.
This is a decomposition, not a net reduction in holes. No sorry remains in the item.
The pre-existing stalkChangeOfRingsIso hole is used, not changed or added.

## No longer needed

Removed the direct proof import Sheaf.Topology.InverseImageStalk from the item; node
lem-weil-pbc-topological-inverse-image-stalk is now used by the scalar-transport child.
The direct proof dependency def-pc-topological-inverse-image-module is likewise moved
to that child, while its module remains publicly imported for the item's signature.
No module is asserted to leave the entire target closure. The existing public imports
remain necessary for the unchanged statement. No further planned nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The planned stalk comparison requires scalar transport not supplied by the two existing
stalk lemmas. There is a scheme-specific scalar-transport lemma, but it requires a
scheme morphism and its canonical stalk map; it cannot be applied to arbitrary ringed
spaces and alpha. The new child supplies just this missing module-level argument.
Mathlib's chosen sheaf pullback and the explicitly constructed inverse image need an
adjunction-uniqueness comparison (or a direct constructed stalk calculation).
The new statement was checked on identity maps, zero modules, zero stalk rings, and
empty spaces. It imposes no flatness, boundedness, or complex hypotheses.

## New nodes

lem-pc-ringed-inverse-image-stalk-scalar-transport records scalar transport between two
tensors before the stalk-of-change-of-rings isomorphism. Its statement includes the
pure-tensor formula and additive naturality needed by the Lean proof. It is strictly
below the item: it mentions neither complexes, P, e, he, nor the stalk of changeOfRings.
The existing item node now records the compiling route. No change record is needed.

## Second reading by U1

1. Interface: compared the full item module with the repository version using diff,
   and mechanically compared the existing theorem signature byte for byte through
   its result type. It is unchanged. No existing definition, docstring, public import,
   or target statement changed. The only import replacement is private to the proof.
   The new module adds one named theorem, with no definitions or change records.
   Verdict: pass.

2. Proof: compiled both delivered modules in import order using lcompile.py --all;
   the scalar-transport module took 2.6 seconds and the item 7.7 seconds, without
   errors or unexpected warnings. Scratch copies with #print axioms showed exactly
   propext, Classical.choice, Quot.sound, and sorryAx for both declarations. The item
   has no direct sorry; the new theorem has exactly one whole named-theorem sorry.
   Neither file has forbidden declarations or hollow definitions. Read the hdelta
   argument (named hδ in Lean): hom_ext reduces to 1 tensor m, hbeta and hc give
   additive naturality, and the reversed hτ equality gives change-of-rings naturality.
   The component isomorphisms point from scalar extension to P using inverse stalks
   of e; cancelling the stalk of e_j reduces their differential squares to he and hδ.
   Verdict: valid reduction, dependent on the two open comparison theorems; not a
   sorry-free proof of the entire import closure.

3. Split: read the full scalar-transport statement, its node, and its docstring.
   It fixes the explicit k and rho, gives additive equivalences c, linear tensor
   isomorphisms beta, their formula on all pure tensors, and naturality for all module
   maps. Its balancing argument uses c(r m)=k(r)c(m); the inverse uses that k is an
   isomorphism. This is only the inverse-image scalar-transport part, and does not
   restate the complex theorem or the stalk-of-change-of-rings comparison.
   Read Stacks Tags 0098 and 008H online (the local sheaves.tex is absent), and the
   explicit inverseImageModule construction and its unit semilinearity theorem.
   Common-neighborhood germ representatives justify compatibility with those chosen
   module instances. Identity maps reduce to ordinary scalar transport; zero modules
   give zero tensors; if the source stalk ring is zero its unital map forces the
   target stalk ring to be zero; an empty X has no x. No missing flatness or
   boundedness hypothesis was found. Repeated searches with different queries:
   LeanFinder for natural semilinear inverse-image stalk equivalences, Loogle for
   "stalk", "pullback", msearch grep for scalar/stalk combinations, and rg across
   lean/Sheaf and lean/WeilConjectures. Matches were presheaf stalk comparisons,
   tilde/localization comparisons, or special scheme results, not this general
   ringed-space scalar-transport statement. No short existing proof closes the
   remaining semilinearity and tensor-transport argument. Verdict: true, needed,
   strictly smaller split with an adequate complete informal proof and matching node.

4. Route and pruning: checked the original four proof_deps against the new route.
   The module stalk functor and stalk-change-of-rings comparison are used directly;
   inverse-image module data remains in the public signature; inverse-image stalk
   comparison and inverse-image module data move under the new child. The report
   accounts for both removed direct dependencies and the removed direct private
   import. There is no claimed module pruned from the target closure. Public imports
   support the signatures; private imports supply comparisons or the open child's
   stated proof plan. Read sk-thm-picard-duality.json: realized has an empty statement
   list and one empty step list; this below-unit comparison is not a unit realization,
   and neither the unit nor its route is changed. The parent still performs the
   naturality and complex assembly itself. Verdict: pass; net holes closed is zero.

5. DAG: read both delivered node files and the repository item node. Existing node
   statement and statement dependencies are unchanged. The new parent proof records
   k, psi, rho, beta followed by tau, tensor-generator naturality, and isoOfComponents
   exactly as Lean does; proof_deps is the union of its uses. The child records the
   natural inverse-image comparisons, semilinearity, balanced tensor maps and their
   inverses, with sources, searches, creation, blueprint ancestry, chapter/unit, and
   its verbatim Lean signature. It cites no parent and introduces no circular route.
   Verdict: pass.

Changes by the second reader: appended this review and recorded independent searches
and explicit axiom checks. No Lean or DAG repair was needed. One original hole is
closed by reduction and one strictly smaller hole is added; this remains a
one-for-one decomposition, with no net hole reduction and no globally pruned module.
