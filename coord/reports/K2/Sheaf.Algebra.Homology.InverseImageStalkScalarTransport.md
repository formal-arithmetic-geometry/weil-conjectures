## What changed
Replaced the invalid earlier reduction with a complete Lean assembly of the original statement.
The generic tensor theorem `exists_inverseImage_stalk_scalar_transport_beta` is proved using
`TensorProduct.congr`: identity on the final ring and the supplied semilinear additive equivalence
induce a tensor equivalence. Tensor induction proves linearity over the final ring. Its pure
tensor formula is definitional. The main theorem proves bijectivity of the ring comparison
using Mathlib's presheaf stalk comparison and stalks of sheafification, and applies this tensor
result to the natural semilinear comparisons supplied by the new geometric intermediate theorem.
All existing signatures and public imports are unchanged. No adaptations are included.

## Proved and sorry left
Closed the original hole `exists_ringed_inverseImage_stalk_scalar_transport` by a complete
reduction. Proved the new general algebra theorem `exists_inverseImage_stalk_scalar_transport_beta`
without sorry. Added one hole: `exists_inverseImage_stalk_comparison_natural`, node
`lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality`. This is only the geometric
comparison of the original steps 1–2: it has no alpha, tensor extension, or beta. It supplies
semilinearity and naturality for the same existential family, so the assembly is valid.
This is a decomposition, with one original hole closed and one strictly lower hole added;
net hole count is zero. The proved algebra is independent of the geometric hole.

## No longer needed
Removed the direct proof import `Sheaf.Topology.InverseImageStalk` from the main module, replacing
it with `Mathlib.Topology.Sheaves.Sheafify` for the ring comparison proof. InverseImageStalk
remains required by the geometric intermediate module; no existing DAG node or library module
is claimed globally pruned. All three old proof dependencies remain in the closure:
`lem-weil-pbc-topological-inverse-image-stalk`, `def-pc-topological-inverse-image-module`,
and `def-weil-pbc-module-stalk` are now dependencies of the geometric helper. None is
reported as an unused node; only the direct import moved. The false arbitrary-family naturality lemma from the earlier
unlanded attempt has been discarded. No unused exploratory files are counted as pruning.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt's `inverseImage_stalk_comparison_naturality` was false: arbitrary additive
equivalences need not form a natural family. Its beta existence also did not constrain the
chosen family sufficiently. The repaired geometric theorem simultaneously supplies the same
family's semilinearity and naturality, and the proved algebra theorem requires semilinearity
explicitly. Edge cases checked mathematically: zero modules and zero rings obey the same tensor
relations; an empty source admits no point x; no flatness hypothesis is needed. The original
node's route is retained, with its geometric and algebraic parts now separated. No unit step
is bypassed, and no target statement or definition is changed.

## New nodes
`lem-pc-ringed-inverse-image-stalk-scalar-transport-beta` records the proved generic tensor
transport theorem in `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportBeta`.

`lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality` records the remaining natural
semilinear geometric comparison in `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportNaturality`.
Both records replace the rejected, unlanded attempt's records. The parent node's proof and
proof dependencies now match the actual assembly. No change record is necessary because
all changes to existing declarations are proof-only; the two helper modules are new.

## Second reading by K2

1. Compared all delivered modules with the repository. The two helper modules are new;
   the existing main declaration's signature, docstring, visibility and public imports
   are unchanged. Restored an accidental extra space before `:=` so the existing
   signature is byte for byte identical. No definition or target statement changes,
   no change records and no forced adaptations.
2. Compiled all three modules in import order using lcompile.py: no errors or warnings.
   Compiled scratch copies with `#print axioms`: the independent algebra theorem uses
   only `propext`, `Classical.choice`, `Quot.sound`; the main theorem and geometric
   helper also use `sorryAx`. Exactly one delivered sorry remains, the named public
   theorem `exists_inverseImage_stalk_comparison_natural`. No axiom, unsafe, opaque,
   extern, implemented_by, hollow definition or data chosen from an unproved
   existence theorem is added. The chosen beta family comes from the proved algebra
   theorem, so its construction does not introduce an arbitrary unproved witness.
3. Read both new statements, the inverse-image section construction and its unit
   semilinearity, the upstream stalk comparisons, and module germ laws. The geometric
   statement is true: the canonical abelian comparison transports products of germs
   via the ring comparison and is natural in module morphisms. Its existential
   family satisfies semilinearity and naturality together. It has no alpha or tensor
   products and is strictly the geometric part of the original argument, not a
   restatement of the item. The algebra theorem is proved and uses precisely the
   needed semilinearity assumption. Zero rings, zero modules, identity maps, and an
   empty source were checked mathematically; no flatness is needed. The remaining
   hole has its source, full docstring argument and matching node. Consulted Stacks
   [0098](https://stacks.math.columbia.edu/tag/0098) and
   [008H](https://stacks.math.columbia.edu/tag/008H); these give the stated stalk route.
   Fresh LeanFinder search for "stalk functor sheaf pullback unit natural isomorphism
   compatible scalar multiplication" found stalkPullbackIso and affine Tilde facts,
   not the semilinear module comparison. Loogle TensorProduct.congr confirmed the
   algebra machinery already used. Grep for stalk/germ smul and stalkPullbackIso,
   plus rg across Sheaf and the source library, found germ_smul and the existing
   abelian/ring comparisons, not a duplicate of the geometric statement. Closing
   the geometric hole needs the common-neighborhood and unit-compatibility proof;
   it is not a few-minute application of an existing declaration.
4. The main proof follows the original route: obtain the natural semilinear family,
   prove k bijective with Mathlib, and assemble objectwise tensor isomorphisms using
   the independent algebra theorem. All proof-only imports are plain imports;
   public imports supply statement vocabulary. The geometric helper retains its
   planned proof import InverseImageStalk. All old proof dependencies remain in its
   closure, as documented under No longer needed. No global module is pruned.
   The unit sk-thm-picard-duality has empty realized statement/step lists; no listed
   realization is removed or bypassed. This is a decomposition: one original hole
   closed, one strictly lower hole added, net zero; the algebra theorem is separately
   proved without sorry.
5. Checked each node's Lean statement verbatim, chapter/unit, creation/source,
   blueprint parent, searches, proof dependencies and proof origin. The parent
   records the actual reduction and the helper records the geometric remainder.
   Updated the algebra node's proof text to describe the actual TensorProduct.congr
   construction and B-linearity induction rather than a hand-written lift.

Second reading changed only the existing signature's accidental whitespace,
clarified retention of every old proof dependency in No longer needed, aligned
one new node's proof text with Lean, and added this independent review. The proofs
and helper statements needed no repair.
