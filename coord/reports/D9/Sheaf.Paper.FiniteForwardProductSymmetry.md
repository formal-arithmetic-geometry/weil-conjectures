## What changed

Repair of returned head da58b2d38b3: removed the unused `warn.sorry` option from
FiniteForwardProductDefinitions. The landing scanner treated the option name as an
unattributed hole at line 40; this module contains no proof holes. No construction,
statement, or proof changes in this repair. Compared the retained adaptation with
current main: FiniteProductCompactification still differs only in its required import.
The delivery tool rebuilds this packet on the current sheaf-dag base.

Replaced the body of AlgebraicGeometry.ProEtale.finiteForwardProduct_symmetry with a
proof combining product compactification in both orders, a Cartesian-cone transport,
and the ordinary-product/open-extension symmetry square. The coordinate-transport statement receives all
five ordered fields and the opposite input field, from which its comparison domain is formed. The final Lean argument proves an abstract categorical pasting lemma: substitute
the two equalities, cancel the reversed output comparison, and cancel the forward
output comparison. It then applies that lemma to the actual morphisms. The theorem signature is unchanged.

Extracted the twelve existing supporting constructions verbatim to
Sheaf.Paper.FiniteForwardProductDefinitions, publicly reexported by the item.
FiniteProductCompactification imports this definitions module instead of the item;
this is necessary to import its theorem without an import cycle. The two existing
definition nodes now attach to the extracted module. No definition data is chosen
from an unproved existence theorem. The only new construction is the supplied-cone
geometry, whose fields are actual pullbacks and the supplied cone.

The two new intermediate statements isolate coordinate transport and symmetry of
an ordinary-product/open-extension normal form. They have named public theorems,
complete proof docstrings, and DAG nodes. They assert distinct parts of the argument;
neither restates the compact-support forward-product symmetry or assumes it.

Change record: coord/changes/D9-finite-forward-definitions.md.

## Proved and sorry left

Closed the existing syntactic hole in
AlgebraicGeometry.ProEtale.finiteForwardProduct_symmetry
(lem-pur-finite-forward-product-symmetry), by a complete Lean combination of the
intermediate statements and the existing product-compactification theorem.
This is a decomposition, not a complete proof without new obligations:
one upper hole closed, two lower holes added, net minus one hole.

The new holes are:

- AlgebraicGeometry.ProEtale.finiteForwardCartesianCoordinates
  (lem-pur-finite-forward-cartesian-coordinates): transport the supplied comparison
  assertion to any Cartesian cone; no symmetry is asserted.
- AlgebraicGeometry.ProEtale.finiteForwardCompactifiedSwap
  (lem-pur-finite-forward-compactified-swap): the ordinary proper product followed
  by the normalized open tensor comparison commutes with signed factor swap.

The adapted FiniteProductCompactification retains its two pre-existing holes,
AlgebraicGeometry.ProEtale.finiteProductOpenTensor_isIso and
AlgebraicGeometry.ProEtale.finiteProduct_compactification
(both on lem-pur-finite-product-compactification), untouched. They are not new holes.
The extracted definitions module has zero holes. All private helpers are proved.

## No longer needed

No mathematical node or library module is withdrawn. The existing proper-product
transpose and open-product swap remain needed in the new normal-form node. The
product-compactification theorem remains used twice by the final assembly.

Removed the following unused direct proof imports from the extracted constructions:
Sheaf.Paper.FiniteDirectImageComposition,
Sheaf.Paper.IntegralFinitePullbackComposition,
Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization,
Sheaf.Paper.DerivedPullbackTensorIso, and Sheaf.SixFunctors.OpenTensorNormalization.
Some remain imported by lower proof modules, where they are still needed.

The parent's former tool_uses entries were withdrawn because its proof now uses the
explicit intermediate statements: lem-sf-open-tensor-normalization,
lem-pur-derived-pullback-tensor-iso, def-exchange-projection,
def-weil-pbc-composite-adjunction, lem-weil-pbc-mate-pasting,
lem-weil-derived-direct-image-composition, lem-weil-derived-tensor-functorial,
lem-sfb-derived-composition-adjunction-normalization, and
lem-weil-pbc-proetale-derived-pullback-composition. This withdraws direct approvals
on this parent, not the declarations or their uses in the lower nodes.

## Where the brief, the DAG or earlier work was wrong

The DAG gave the correct mathematical decomposition, but the modules could not be
imported in the planned direction: FiniteProductCompactification imported the assigned
symmetry module for its definitions. Separating those existing constructions resolves
that cycle without changing a mathematical statement or object.

The stated comparison theorem is on Mathlib's chosen Cartesian cone. The symmetry
conclusion uses both orders on one common cone (sq and sq.flip). The exact transport
of that comparison must be exposed; it is not definitionally the swapped chosen cone.
This is the first new obligation.

The proper-product theorem uses the intrinsic coefficient presentation; the assigned
maps and compactification theorem use fixed-scalar sheaves. The second new obligation
retains the required normalization through those coefficient equivalences, the proper
counit calculation, open-unit normalization, and the two endpoint comparisons.
No projection or exchange map is inverted.

Small cases checked in the new statements: a supplied cone equal to the chosen cone
reduces coordinate transport to its premise; swapping an identical pair retains the
signed symmetry twice, not an unjustified sign-free identity; a zero input produces
zero morphisms. No Tor-amplitude, constructibility, or auxiliary boundedness is added.
The unit sk-prop-an and its affine-space induction/permutation route are unchanged.
The coordinate-transport obligation includes normalization of the chosen-compactification
forward route: etale self-comparison reflexivity is descended by full faithfulness,
and functorial identities identify the expanded chosen route with the literal forward
product. The private helper in the item is only the fully proved categorical pasting.

The new coordinate-transport node uses generic mate pasting and canonical direct-image
composition from other units as tools, for compatibility of the specified maps. It does
not replace any step of the affine-space route. The new ordinary/open swap node uses
the previously stated proper/open calculations of this unit; its pullback/tensor and
composition compatibility dependencies are the same generic tools as in the parent plan.
The maintainer can record the requisite tool approvals at review.

## Forced adaptations

Sheaf.Paper.FiniteProductCompactification was unclaimed when the extraction began;
it is now held by J7. Only its public import line is changed, from
Sheaf.Paper.FiniteForwardProductSymmetry to Sheaf.Paper.FiniteForwardProductDefinitions.
With the original import and the new proof imports the dependency graph is cyclic:
FiniteProductCompactification → FiniteForwardProductSymmetry →
FiniteForwardCompactifiedSwap → FiniteForwardProductCoordinates →
FiniteProductCompactification. Every existing declaration, signature, visibility,
attribute and proof in that adapted file is byte-identical. The import replacement
breaks precisely this cycle. All other consumers retain their declarations through
the public reexport and require no source adaptation.

## New nodes

lem-pur-finite-forward-cartesian-coordinates is in
Sheaf.Paper.FiniteForwardProductCoordinates. It constructs the geometry on a supplied
Cartesian cone and transports an already supplied compactification comparison. Its
proof uses unique cone identification, canonical pullback compositors, mate pasting,
open base change, and comparison naturality/cocycles. The statement assumes no symmetry.

lem-pur-finite-forward-compactified-swap is in
Sheaf.Paper.FiniteForwardCompactifiedSwap. It asserts the signed swap equation solely
for the ordinary-product/open-extension normal forms, with their canonical input and
output comparisons. It uses the existing proper transpose and open swap theorems.
Its conclusion contains no compact-support forward product.

Both nodes carry the same chapter/unit as the parent and source the symmetry paragraph
of literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md. LeanSearch, LeanFinder, and Mathlib grep were run
for each: the transport searches found IsPullback.isoPullback/isoIsPullback and cone
extensionality; the swap searches found externalProductSwap/Flip and elementary graded
symmetries. Their source signatures do not state these geometric derived-map equalities.
The existing proper and open statements were read before introducing either node.

## Forced adaptations

### Sheaf.Paper.FiniteProductCompactification
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
