## What changed

Replaced the whole-proof sorry of
`AlgebraicGeometry.exists_derivedBaseChange_coordinate_naturality` with a compiled
reduction. The proof constructs the transported pullback square via
`IsPullback.of_iso`, uses its `isoPullback` and proves both projection identities,
then composes two restricted coordinate transport laws. The component calculation
uses the functor associator, two substantive transport equations, associativity,
and `Functor.map_comp`.

Added private proof imports of `DerivedBaseChangeBaseCoordinates` and
`DerivedBaseChangeTopIso`. Each new module states one strictly smaller part of the
original coordinate argument: base-coordinate changes with the upper-left vertex
fixed, or upper-left vertex transport with both bases fixed. Both are statements
about arbitrary commutative squares, so their use imposes no added condition.
No existing signature, definition, public import or visibility changed.

The three delivered modules compile locally in import order without warnings.
A separate sandbox experiment in `scratchpad/lean/Sheaf/AlgebraicGeometry/TopIsoAttempt.lean`
also typechecked explicit constructions of j and k from the selected pullback
comparisons and adjunctions, with only the final transport equation unfinished.
It is not delivered: the new named theorem keeps its required whole-proof sorry.
The construction confirms j cancels L(e.hom)^* followed by R(e.hom)_* using the
inverse adjunction unit (not the counit). It is available for the next worker.
No scratch files were written outside this sandbox.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.exists_derivedBaseChange_coordinate_naturality`
(node `lem-pc-derived-base-change-coordinate-naturality`), by decomposition.
No sorry remains in the item module.

Added two whole-proof sorries:

- `AlgebraicGeometry.exists_derivedBaseChange_base_coordinates`
  (`lem-pc-derived-base-change-base-coordinates`).
- `AlgebraicGeometry.exists_derivedBaseChange_top_iso`
  (`lem-pc-derived-base-change-top-iso`).

This is a decomposition, not an axiom-free proof of coordinate naturality:
one upper hole is replaced by two restricted transport laws (net holes -1).
Each lower law has a source, a full natural-language proof, and its own module/node.

## No longer needed

No original imports removed. No modules pruned from the transitive proof closure.
The item no longer directly uses the planned nodes
`lem-pc-derived-direct-image-composition`,
`lem-pc-ringed-spaces-derived-pullback-composition`, or
`lem-pc-scheme-iso-derived-equivalence`, and
`def-pc-derived-base-change-map` as a direct proof step. The last definition still
appears in the signature and is retained through its public import and both new laws.
The first and third need not be added as direct imports: the new laws construct the
required comparisons from the pinned adjunctions and coherent pullback comparisons.
The coherent pullback node remains needed through both new laws and through
`SchemeDerivedBaseChangeMap`; it is not globally pruned. The new laws do not require
`SchemeIsoDerivedEquivalence`'s separately chosen localized equivalence or
`DerivedDirectImageCompositionUnbounded`'s nonempty unnormalized comparison.

## Where the brief, the DAG or earlier work was wrong

The planned composition and equivalence declarations supply existence, but not the
pinned mate compatibility required for the equation. The unbounded direct-image
composition theorem only gives Nonempty of a comparison; the scheme-isomorphism
theorem supplies a localization-compatible equivalence without identifying it with
the pinned derived adjunction. Using arbitrary witnesses would not justify the
base-change equation. The two new laws isolate this missing compatibility without
changing any existing interface or weakening the item.

Read Stacks Tags 08HY, 0D5S and 0D5T online: 08HY defines the mate for any commutative
square, 0D5S gives pullback composition, and 0D5T obtains direct-image composition
by right-adjoint uniqueness. The new docstrings spell out the restricted coordinate
arguments from those constructions. Checked identity isomorphisms (unit laws),
empty schemes and zero objects (natural-transformation identities). Neither new
statement assumes flatness, cartesianness, nonempty schemes or invertible exchange.

The item is not among its unit's `realized` statement/step nodes; no chapter or unit
route is bypassed. Full blueprint searches for coordinate naturality and 08HY
returned no matches. Mathlib searches returned generic `mateEquiv_hcomp`,
`mateEquiv_square`, and conjugation infrastructure; their signatures and
`Adjunction.rightAdjointUniq` were inspected. None is directly the scheme law.
LeanSearch was unavailable and that result is recorded in searches.jsonl.

## New nodes

`lem-pc-derived-base-change-base-coordinates` is the first restricted coordinate
transport: the upper-left scheme and its incoming derived pullback stay fixed.
Its two comparisons are constructed as mates and inverse-equivalence comparisons;
the equation follows after transposing and cancelling the base-coordinate units.

`lem-pc-derived-base-change-top-iso` is the second restricted transport: the two
base schemes stay fixed. It supplies j and k0, and identifies the exchanged map
with its transport through an isomorphic upper-left vertex. Its proof uses
right-adjoint conjugation, pullback associativity and counit naturality.

Both nodes inherit the item's chapter and unit and carry recorded searches and
exact Lean signatures. Change record:
`coord/changes/P1-derived-base-change-coordinate-parts.md`.

## Second reading by P1

1. Interface: PASS. Read the diff against the repository module. The sole existing
   theorem signature is byte for byte identical, including all universes, hypotheses,
   existential comparisons and its equation. Existing docstrings, definitions,
   public imports and visibility are unchanged. The only added imports of the item
   are private proof imports; the two new declarations have a change record.
2. Proof and trust: PASS as a decomposition. Independently compiled all three
   delivered modules in import order with lcompile.py, without warnings or errors.
   A scratch copy printing axioms for all three declarations shows only propext,
   Classical.choice, Quot.sound and sorryAx. The only two direct sorries are exactly
   the named whole-proof theorems listed above; no forbidden declaration, hollow
   definition or arbitrary witness selected into a definition is added. The item
   combines witnesses within a proposition proof and constructs e by isoPullback.
3. Split statements: PASS. Each is a proper part of the coordinate argument:
   the first fixes Xprime and gprime and changes only the two bases; the second
   fixes both bases and changes only the upper-left scheme. Neither restates the
   item or assumes invertible base change. The hA and hprime witnesses follow from
   commutativity and the isomorphism equations, so impose no geometric condition.
   Checked identity coordinates using the coherent unit laws, empty schemes and
   zero objects using the natural-transformation equations. Read both docstring
   arguments and Stacks 08HY, 0D5S, 0D5T; the coherent comparisons and adjunction
   mates give the stated equations. In particular j uses the inverse adjunction
   unit, with the correct functor order. Fresh leanfinder, loogle and grep queries
   used mate preservation by equivalence conjugation and pasting, mateEquiv_vcomp,
   rightAdjointUniq and conjugateIsoEquiv; read the relevant Mathlib signatures.
   Local library searches and the existing direct-image/equivalence declarations
   give no exact transport law. Generic mate laws still require constructing and
   identifying the pinned comparisons; neither remaining hole closes in a few
   minutes from an existing scheme theorem.
4. Route and pruning: PASS after report repair. The proof first constructs the
   pullback-coordinate isomorphism with Mathlib, then composes precisely the two
   smaller transport equations by whiskering, associativity and map_comp. Every
   import supplies signature data or a used theorem. The unit's realized statement
   and step lists contain neither this item nor any pruned dependency, and remain
   unchanged; the split is below the unit route. The pruning list now accounts for
   every removed old proof_deps entry, including the base-change definition's
   removal as a direct proof step; this is not removal of its signature import.
   No module is globally pruned. One upper hole closed, two lower holes added:
   net closed minus added is -1, so this is not an axiom-free completion.
5. Records: PASS. Checked all three recorded Lean signatures against their files
   and all proof_deps against the union of proof-step uses. The item records the
   actual pullback construction and composition calculation. Both new nodes have
   their source, proof, searches, split status, created metadata, blueprint origin,
   chapter, unit and exact Lean record; new module names have no existing sources.

Second reading changed the report's missing direct-dependency pruning entry and
added this independent review and search evidence. No Lean proof or signature
needed repair. The two lower transport laws remain open, as explicitly reported.
