## What changed

Proved `AlgebraicGeometry.Etale.finiteEtaleTrace_comp_restriction_app_of_split`
in `Sheaf.AlgebraicGeometry.FiniteEtaleTraceSplitComponent` without changing its
signature or docstring. Two fully proved private helpers identify the restriction
unit with the pullback projection and compute the trace composite on an object
localized over a split cover. The latter constructs both directions of the
pullback-pasting isomorphism, applies the localization and split properties of
`existsUnique_finiteEtaleTrace`, cancels the comparison isomorphisms, and computes
one identity summand per section. The public theorem supplies the inverses of the
component projections and evaluates at the identity object over W, using naturality
to identify that object's localization with W.

Updated the node proof to describe this explicit calculation. Its proof dependencies
are unchanged. No new public declarations, modules, or nodes were introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.finiteEtaleTrace_comp_restriction_app_of_split`
(node `lem-weil-pbc-finite-etale-trace-split-component`).
No holes remain in the delivered module; no holes were added or split off.
The proof uses the existing characterized trace family, so it still inherits any
unproved obligations of `existsUnique_finiteEtaleTrace` through that declaration.
The calculation uses no nonempty or positive-cardinality assumption; the finite
sum calculation includes an empty index type and an empty scheme.

Validation: the complete module compiles locally without warnings using lcompile.py.

## No longer needed

Removed redundant direct imports:
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

Their declarations are still used and available through the required public import
`Sheaf.AlgebraicGeometry.FiniteEtaleTrace`; no dependency nodes or modules are pruned
from the transitive closure. No additional theory is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement errors were found. The original plan's comparison can be
implemented by localizing at W.hom and evaluating at the identity object over W;
there is no need to transport the supplied coproduct cofan by pullback symmetry.
The explicit argument follows the same unit route and uses the same dependency nodes.
An alternative through the newly stated local-sum interface was considered, but its
modules were absent from the compiled snapshot. The delivered proof uses only the
available trace-characterization and localization interfaces.

## Second reading by H2

1. Visibility and statement preservation: PASS. Read the complete repository/sandbox
   diff. The existing public theorem signature is byte for byte identical, including
   universes, finite/etale instances, the arbitrary abelian sheaf and site object,
   finite index type, coproduct hypothesis, both immersion hypotheses, and component
   projection isomorphisms. Its docstring is unchanged. The only added declarations
   are private proved theorems; no definitions or public statements changed. There
   are no applicable change records. Checked the characterization against Stacks
   [Tag 03SH](https://stacks.math.columbia.edu/tag/03SH), the two properties following
   Definition 03SE: localization followed by the split sum gives precisely this
   cardinality multiple, without a constant-degree hypothesis.

2. Proof and axioms: PASS. Independently compiled the delivered module with
   lcompile.py: exit 0, no warnings (14.7 seconds). Searched the complete delivered
   Lean file for sorry, axiom, unsafe, opaque, implemented_by, extern, and kernel
   bypasses: none. Compiled a scratch copy with #print axioms for all three
   declarations. restriction_localization uses only propext, Classical.choice,
   Quot.sound. split_component_localized and the public theorem additionally use
   sorryAx from the existing characterized trace obligations. There are no new
   holes. The sole data choice already used by finiteEtaleTrace selects an entire
   uniquely characterized family, not an arbitrary witness of mere existence.
   hc.some selects a proof of IsColimit; the component inverses and both maps of
   the pullback comparison are explicitly constructed.

3. Split statements and edge cases: PASS, vacuous for split-off obligations:
   none were introduced. Read both private helper proofs. The restriction helper
   uses the actual adjunction-unit compatibility. The localized helper constructs
   both pullback-pasting maps, verifies both inverse identities and both required
   projections, applies hp.2.1 and hp.2.2 with all their hypotheses, cancels genuine
   isomorphisms, and uses section/projection identities for every summand. The
   public theorem obtains both inverse identities from the supplied IsIso
   instances and transports along the identity-object isomorphism by naturality.
   Checked J empty (empty sum and card zero), J singleton (one identity), and an
   empty base with arbitrary finite J (the zero section group). No nonempty or
   positivity premise is used. No statement merely renames the original hole.

4. Top-down route and pruning: PASS. Searched lean/Sheaf and lean/WeilConjectures,
   the upstream SixFunctors/Etale sources, and Mathlib category/geometry sources
   for trace/restriction and unit/restriction variants. A fresh LeanFinder search
   for the abelian-sheaf split trace composite returned only unrelated algebra
   results; Loogle did not recognize the unqualified adjunction lemma identifier.
   Direct Mathlib search confirms unit_leftAdjointUniq_hom_app, already used here.
   The existing local-sum interfaces concern a separately supplied characterized
   trace and do not provide a shorter established theorem for this chosen family.
   Kept the working proof. The sole public import FiniteEtaleTrace supplies the
   public signature. Both removed imports are redundant through its public import
   closure. Every old proof_deps node is still used; none can be listed as pruned.
   Read sk-thm-p1.json, including realized: this auxiliary calculation preserves
   the finite-etale trace step of the locally constant reduction and bypasses no
   realized statement or unit step.

5. Node agreement: PASS. Compared the node JSONs: only proof and proof_origin
   changed. Read all four retained dependencies and their Lean or Mathlib records:
   fibre products, abelian etale sheaves, inverse image as restriction, and trace
   existence/uniqueness. They match the constructions and hp properties used by
   the proof. proof_deps is unchanged and is the union of the proof-step uses.
   The rewritten proof describes the explicit pasting and finite-sum calculation
   accurately, including final transport from the localized identity object.
   No new nodes need additional metadata, and no unit record changes are needed.

Second-reading changes: appended this independent review and its verification
results. No Lean or DAG repair was necessary; the mathematical proof and imports
were retained. Closed 1 original hole, added 0, split off 0; no transitive module
was pruned. This is a proof of the item relative to the existing trace obligations,
not a claim that those downstream obligations are closed.
