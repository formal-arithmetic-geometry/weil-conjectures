## What changed

The existing theorem `AlgebraicGeometry.rightAdjoint_mate_oldBase_open` now has a complete
Lean proof with its signature unchanged. The proof constructs the canonical maps s and t
by `pullback.lift`, proves all projection identities, and derives q ≫ s = r by
`pullback.hom_ext`. It constructs the arrow isomorphism from the factorization equation
and invertibility of the open mate, then transports it along arbitrary q using
`Arrow.isoOfNatIso`, `Functor.mapArrow.mapIso`, and derived-pullback composition.

Two new modules state strictly separate remaining steps: invertibility of the canonical
mate along an affine open, and its pasting factorization before that mate is inverted.
The latter assumes only a qcqs morphism, not properness, flatness or finite presentation.
It retains the open mate as a factor and does not claim an arrow isomorphism on its own.
The right adjoint used for the open square is chosen only inside the theorem proof from
its universal property; no definition chooses an arbitrary existence witness.

Added private proof imports in the item: `RightAdjointMateAffineOpenIsIso`,
`RightAdjointMateOldBaseOpenFactorization`, `ProperFlatRightAdjointBaseChangeHbeta`,
and `DerivedPullbackComposition`. No existing public import, definition, statement,
instance or target signature changed. All three modules compiled together, and the
main proof compiled independently against the sandbox dependencies.

## Proved and sorry left

Closed: `AlgebraicGeometry.rightAdjoint_mate_oldBase_open`
(node `lem-sc-right-adjoint-mate-old-base-open`), the only original hole.
No sorry remains in the item module.

Added and still sorry:

- `AlgebraicGeometry.rightAdjoint_mate_affineOpen_isIso`
  (`lem-sc-right-adjoint-mate-affine-open-is-iso`). This isolates the geometric
  invertibility statement for an affine open, with no T, gV, Z, r, q, b or b prime.
- `AlgebraicGeometry.rightAdjoint_mate_oldBase_open_factorization`
  (`lem-sc-right-adjoint-mate-old-base-open-factorization`). This isolates pasting
  on U times_V T, retains the open mate without inverting it, requires only qcqs f,
  and has no arbitrary further pullback Z, r or q.

This is a decomposition: one upper hole closed and two lower holes added, net -1.
The combining proof is fully written and compiled. The pre-existing dependencies retain
their own proof status; no unsupported axiom or anonymous hole was introduced.

## No longer needed

Removed the item's private imports of `DerivedOpenRestrictionMaps` and
`ProperFlatRightAdjointRestrictionOpen`. The former provides no symbol used in the item's
statement or new proof. The latter is now a proof dependency of the new open-invertibility
node and module, rather than a direct dependency of this transport-and-assembly proof.
Neither module is claimed pruned from the targets' transitive closure: both remain below
the new open-invertibility lemma. No existing DAG node is globally pruned.

The original direct proof dependencies `def-pc-derived-base-change-map` and
`lem-sc-proper-flat-right-adjoint-restriction-open` move below the two new steps;
these old dependencies remain required within the lower argument or the statements.
The canonical mate definition and derived-pullback composition remain direct dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing proper-flat restriction theorem proves
invertibility of a restricted open-unit map. It does not literally state invertibility
of `dualityEquationBaseChangeMap` along V.ι. Identifying those maps needs the open
adjunction, direct-image comparisons, and triangle identities; the new affine-open
node records that remaining comparison explicitly.

The existing `schemeDerivedBaseChange_pasting` is the ordinary base-change law with an
upper-left morphism, rather than the required right-adjoint mate factorization. It is
retained as a tool below the new factorization, together with generic Mathlib mate
composition and right-adjoint uniqueness. Library and Mathlib searches found no exact
one-open right-adjoint comparison. LeanSearch returned Internal Server Error; LeanFinder,
Loogle and source grep supplied generic categorical and underived results only.

Read Stacks Tags 0E4J, 0ATR and 0E9S directly. Empty opens/schemes and zero complexes
cause no exceptional case: the canonical functor maps and triangle identities still
apply. No invertibility of the global/local mate or of r/q was used. The new steps
remain within the original node route; the unit's realization record is unchanged.

## New nodes

`lem-sc-right-adjoint-mate-affine-open-is-iso`, in
`lean/Sheaf/AlgebraicGeometry/RightAdjointMateAffineOpenIsIso.lean`, formalizes Tag 0E4J(2)
for the fixed canonical mate on the canonical open pullback. Its proof plan retains
`lem-sc-proper-flat-right-adjoint-restriction-open` and the direct-image comparisons.

`lem-sc-right-adjoint-mate-old-base-open-factorization`, in
`lean/Sheaf/AlgebraicGeometry/RightAdjointMateOldBaseOpenFactorization.lean`, formalizes
the composite mate equation from Tag 0ATR after the open-square scheme identifications.
It supplies endpoint comparisons and an equality with the noninvertible open mate as
an explicit intermediate factor. Open invertibility is deliberately a separate step.

Both nodes inherit chapter `sec-picard-framework`, unit `sk-thm-picard-duality`, and the
original blueprint ancestor. Each has its full signature, source, proof steps and
Mathlib search records. No change record is needed: existing interfaces are unchanged.

## Second reading by H4

1. Interfaces: PASS. Compared the delivered item with the repository using diff and
   compared the theorem signature as literal text: it is byte-for-byte identical.
   The existing docstring, public imports, definitions and visibility are unchanged.
   The other two modules are new; there are no forced adaptations or interface changes.
2. Kernel and holes: PASS as a decomposition. Independently compiled all three modules
   through lcompile.py in import order, with no errors or warnings. Scratch copies with
   explicit #print axioms for all three declarations report only propext,
   Classical.choice, Quot.sound and sorryAx. The item's proof has no sorry; the only
   two added holes are the named public theorems listed above, each with a complete
   sourced proof docstring and node. No forbidden declaration or hollow definition is
   introduced. The locally chosen open right adjoint is determined up to natural
   isomorphism by its supplied adjunction, and is chosen only inside a theorem proof.
3. Split statements: PASS. Independently read Stacks Tags 0E4J, 0ATR and 0E9S
   (https://stacks.math.columbia.edu/tag/0E4J,
   https://stacks.math.columbia.edu/tag/0ATR,
   https://stacks.math.columbia.edu/tag/0E9S). The affine-open lemma is the invertibility
   ingredient without any further base T or Z. The factorization keeps the open mate
   as a factor, drops properness/flatness/finite-presentation assumptions, and has no
   final arbitrary pullback Z: it does not restate the original arrow isomorphism.
   Its ordinary base-change isomorphism hypotheses are the categorical ingredients
   used for inverse conjugates in Tag 0ATR; no geometric invertibility is smuggled in.
   Checked empty schemes/opens, zero complexes, total affine opens, arbitrary choices
   of adjunctions, and noninvertible local mates: the comparisons are adjunction-compatible
   and the equality does not cancel a noninvertible mate. Independent LeanFinder search
   for Beck-Chevalley/right-adjoint composition and open restriction, Loogle search for
   conjugateEquiv_comp, and rg searches of Sheaf, WeilConjectures and Mathlib found generic
   mate composition, underived restriction, and etale six-functor pasting only, with no
   exact derived scheme comparison. Neither remaining step closes in a short application
   of those declarations: the canonical derived/open comparisons still require proof.
4. Route and pruning: PASS. Read the assembly from its conclusion downward. Projection
   identities establish q composed with s = r by pullback.hom_ext; functorial transport
   then gives precisely the asserted Arrow isomorphism on Z. The source isomorphism
   in Arrow.isoMk uses only the independently isolated open invertibility, not either
   global or local mate's invertibility. Every added import is private when proof-only;
   the new public imports supply symbols in the new statements. The two removed imports
   and both removed old direct proof dependencies are listed in No longer needed; none
   is falsely claimed pruned from the transitive closure. Inspected the unit's realized
   record: no realization or unit step is bypassed or changed. Net holes remain -1
   (one original hole closed, two added), explicitly a decomposition, not a net proof.
5. DAG: PASS. The existing node differs only in proof, proof_deps and proof_origin.
   Each node's proof_deps equals the union of the steps' uses. Read all new node
   statements against their Lean signatures, proof plans and docstrings; checked source,
   search records, created/blueprint/chapter/unit fields and lean records. The parent
   records exactly the open-invertibility/factorization assembly and pullback transport.

Changes by the second reader: appended this independent review only; no Lean or node
changes were needed. Removed temporary axiom-probe copies after checking them. The two
split holes remain as reported; no additional holes were added by this reading.
