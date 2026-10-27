## What changed

Proved `AlgebraicGeometry.exists_open_prescribedPoint_bertini` with its signature,
public imports and docstring unchanged. The proof specializes the existing Bertini
result to the coefficient field itself, proves its zero-scheme comparison with the
unbased-changed member, and applies it on the given open complement. Private proved
helpers establish scalar/composition naturality of tensor-section units and the
zero-locus comparisons. An isomorphism between the two pullback squares identifies
the restricted closed subscheme with the inverse-image open in the member.

The proof intersects the Bertini open and the nonzero-jet open using irreducibility
of affine coefficient space. At every point of a member it chooses either the
smooth inverse-image open over the complement or a smooth neighbourhood supplied
by its nonzero jet at the prescribed closed point. The chosen opens cover the
member, so source locality proves global smoothness.

Added two statement modules:
`Sheaf.AlgebraicGeometry.PrescribedPointNonzeroJetOpen` and
`Sheaf.AlgebraicGeometry.PrescribedPointJetSmoothNeighborhood`.
Their imports in the assigned module are private proof imports. Updated the
assigned node's proof, proof dependencies and proof origin to this assembly.
No existing definitions, statements, attributes or public imports changed;
no consumer adaptations or change record are required.

Validation: all three modules compile through lcompile.py. The final assigned
module check removes the unused-hypothesis warning without renaming its binder.
All delivered Lean lines have at most 100 characters. The source read was the
current blueprint finite-cover-curve proof, paragraph 2, Stacks Varieties Tag
0FD6 including its first-order evaluation calculation, and Algebra Tag 00TR.
The two new statements were checked on empty schemes/sets and empty coefficient
index types: the jet open permits empty S (take the whole coefficient space),
while a nonempty S and zero coefficient space cannot satisfy jet surjectivity
because the positive-dimensional jet targets are nonzero. The neighbourhood
statement is pointwise and vacuous on the empty zero scheme; it requires no
positive-dimensional ambient hypothesis when its nonzero-jet hypothesis holds.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.exists_open_prescribedPoint_bertini`
(node `lem-zl-prescribed-point-bertini-open`). No sorry remains in the assigned
module. The same-field Bertini specialization and all restriction, isomorphism,
intersection and cover arguments are proved.

Added exactly two named theorem holes:

- `AlgebraicGeometry.exists_open_prescribedPoint_nonzeroJets`
  (`lem-zl-prescribed-point-nonzero-jet-open`): only the derivative open,
  with no generation/immersion hypotheses and no smoothness conclusion.
- `AlgebraicGeometry.exists_smooth_neighborhood_of_prescribedPointJet`
  (`lem-zl-prescribed-point-jet-smooth-neighborhood`): smoothness near one
  closed point of the zero scheme of one section, from its nonzero first jet.
  It has no coefficient space or simultaneous-surjectivity hypothesis.

This is a decomposition: one original hole closed, two lower holes added, net
minus one hole closed. It is not claimed as a proof with no remaining obligations.
Each hole is the whole proof of its public theorem in a separate module and has
its source, complete proof in words, and node. No data is selected from a new
existence statement: the only new declarations with sorry are propositions.

## No longer needed

No original imports were removed, and no Lean module is withdrawn.
`lem-trf-finite-dense-open-intersection` is no longer needed by this argument:
Mathlib `nonempty_preirreducible_inter` directly intersects the two nonempty opens.
The original regularity, connected-integrality, differential dimension,
nonempty-open dimension and cotangent-dimension nodes are now used by the
nonzero-jet-open node rather than directly by the assembly. They remain needed.
The hypersurface differential criterion is retained under the pointwise
smooth-neighbourhood node. The original Bertini theorem and polynomial-domain /
irreducible-spectrum inputs remain used. No part of the unit's realized route
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The dependency declarations are sufficient to obtain Bertini away from the finite
set, but their encodings leave real glue: Bertini is formulated after arbitrary
field base change, while the assigned theorem uses the original scheme; tensor
pullbacks along a composition also require comparison. This delivery proves that
glue. The DAG's elementary jet-open step additionally requires finite-dimensional
jet targets and linearity of the chosen-frame jet map. Those arguments are
recorded explicitly in its separate node. The existing hypersurface criterion
uses a nonzero relative differential in a local frame, not prescribedPointJet;
the remaining pointwise lemma makes precisely this comparison. No mathematical
statement of the brief or existing node was weakened or marked disputed.

## New nodes

`lem-zl-prescribed-point-nonzero-jet-open` records the first two steps of the
original plan: nontrivial cotangent targets on a smooth pure-dimensional scheme
and the finite intersection of complements of the linear zero-jet loci.
It has no smoothness conclusion and does not use Bertini or an immersive system.

`lem-zl-prescribed-point-jet-smooth-neighborhood` records the closed-point
cotangent-to-relative-differential comparison and its application to the existing
hypersurface criterion. It treats a single arbitrary invertible module section
and a single point. Both nodes inherit the assigned chapter/unit and point to
paragraph 2 of the current blueprint finite-cover-curve proof. Searches of the
whole blueprint for jets and nonzero differentials found no duplicate blueprint
node; LeanFinder, Loogle, LeanSearch and source searches found no theorem matching
either obligation. Their actual search records are included in the nodes.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
