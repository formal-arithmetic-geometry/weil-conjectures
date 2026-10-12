## What changed

Reduced `AlgebraicGeometry.Scheme.GaloisCover.exists_module_descent_equivalence`
without changing its signature. Defined a concrete associated module functor in
`Sheaf.ConstructibleSheaf.TorsorAssociatedModule`: locally constant equivariant
sections on scheme fibre products, pointwise intertwiners, restriction of scalars,
and sheafification. Its definitions contain no holes. Restriction, naturality,
functor laws and additivity are proved. Left exact sheafification supplies additivity
by preservation of binary products.

The main theorem lifts this functor into the constant-pullback full subcategory.
The comparison gives membership; fullness passes to the lift; the essential-image
statement proves essential surjectivity. `Functor.asEquivalence` yields the
required equivalence with the same underlying functor. Faithfulness is proved,
not split off: evaluate the pullback comparison at an existing geometric point
of the nonempty total space, use the existing constant-sheaf fibre isomorphism,
and faithfulness of representation forgetting and restriction of scalars.
The unit `sk-thm-p1` and its realized steps are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.exists_module_descent_equivalence`.
This is a decomposition into three strictly smaller statements, not a complete
sorry-free descent proof. Added these three holes, each the entire proof of its
public theorem in a separate module:

- `AlgebraicGeometry.Scheme.GaloisCover.associatedModuleFunctor_comparisons`
  (`lem-weil-pbc-torsor-associated-module-comparisons`): diagonal evaluation and
  descent of invariant functions, with natural pullback and coefficient comparisons.
- `AlgebraicGeometry.Scheme.GaloisCover.associatedModuleFunctor_full`
  (`lem-weil-pbc-torsor-associated-module-full`): recovery of intertwiners from sheaf maps.
- `AlgebraicGeometry.Scheme.GaloisCover.associatedModuleFunctor_essentialImage`
  (`lem-weil-pbc-torsor-associated-module-essential-image`): recovery of a representation
  from a constant pullback trivialization.

No sorry remains in the item's module. Net holes: one closed, three added (minus two).
All five modules compile locally without warnings. No axiom or hollow definition is added.
The remaining statements include arbitrary modules; zero modules, the trivial group,
and the identity torsor satisfy the section formulas. ConnectedSpace excludes empty
bases and empty total spaces, exactly as in the original statement.

## No longer needed

Removed proof-only imports `Sheaf.AlgebraicGeometry.EtaleSheaves` and
`Sheaf.AlgebraicGeometry.NormalScheme`: their additional definitions are not used.
Removed the redundant proof-only import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; it remains available from
the public statement imports and is still needed for the pullback notation.
No public imports removed. The parent node no longer directly lists these old proof dependencies:
`def-sbc-normal-dominant-galois`, `def-weil-connected-scheme`,
`def-weil-pbc-constant-sheaf`, `def-weil-pbc-etale-sheaves`, and
`def-weil-pbc-inverse-image`. They remain needed as statement dependencies or
through the concrete construction and the split lemmas; their modules are not
claimed globally unnecessary.
No unit or unit step is pruned. The new route requires no separate faithful-functor
statement: faithfulness is proved from the existing fibre comparison.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies are definitions only: no stated theorem packages
the equivariant-section construction or the connectedness/descent arguments.
This delivery makes the construction real Lean and isolates the three remaining
geometric arguments rather than importing definitions as if they supplied those proofs.

Sources read: Stacks Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS on the official
Stacks pages. The first three discuss finite modules; the extension to arbitrary
modules for a fixed finite torsor uses the explicit equivariant-section and
connectedness argument in the parent node. The new docstrings spell this out.
The local literature body is absent on this machine; the named source pages were
read online. No source statement or target statement was changed.

LeanFinder and Loogle searches ran; LeanSearch returned Internal Server Error,
recorded as unavailable. Grep found no existing torsor associated module functor.
The nearby associatedModuleFunctor for modules over structure sheaves is a different
notion and is not duplicated. Existing constant-sheaf fibre isomorphisms were reused.

## New nodes

`def-weil-pbc-torsor-associated-module`, module `TorsorAssociatedModule`, gives
concrete equivariant-section data and its sheafification. All its definitions and
functor/additivity proofs compile without sorry.

`lem-weil-pbc-torsor-associated-module-comparisons`, module
`TorsorAssociatedModuleComparisons`, contains the diagonal and invariant-function
comparisons (original steps 1 and 2), with a complete natural-language proof.

`lem-weil-pbc-torsor-associated-module-full`, module `TorsorAssociatedModuleFull`,
contains the morphism descent part of original step 4. It does not assert an
equivalence, essential surjectivity, additivity or the comparisons.

`lem-weil-pbc-torsor-associated-module-essential-image`, module
`TorsorAssociatedModuleEssentialImage`, contains the object recovery part of
original step 3. It does not assert fullness, additivity or an equivalence.

The parent node's proof and dependencies now follow the compiled Lean reduction.
No change record is needed: existing statements and publicly visible imports are unchanged.

## Second reading by G1

1. PASS: compared every delivered module with the repository. Only the original
   module already exists; its theorem signature and docstring are byte-for-byte
   unchanged, and all its public imports are unchanged. Its differences are the
   proof and proof-only imports. The four other modules are new. No existing
   definition or statement changed, and no change record is required.
2. PASS: compiled all five modules locally in import order without errors or
   warnings. Read every construction and proof. The associated functor is
   explicitly constructed from equivariant locally constant sections, scalar
   restriction and sheafification, with no data chosen from an unproved existence
   theorem. The three named split theorems are the only sorries. Scratch copies
   with `#print axioms` verify the construction and additivity use only `propext`,
   `Classical.choice`, and `Quot.sound`; the split statements and the parent
   theorem additionally use `sorryAx`, as reported. No forbidden declaration or
   implementation mechanism occurs.
3. PASS: the comparison, fullness, and essential-image statements are separate,
   strictly smaller parts of the descent argument, each with its source,
   natural-language proof and node. Checked the left-action composition convention
   in `GaloisCover.mul_smul` against the section equation. For the identity torsor
   (trivial group), the equivariance condition disappears and the construction
   gives locally constant module sections; for the zero representation all section
   modules are zero. Empty schemes are excluded by `ConnectedSpace.toNonempty`.
   Arbitrary modules require no finite generation: connectedness applies separately
   to each constant vector, and finite torsor components give the action and
   cocycle. Independently reread Stacks Tags
   [0DV5](https://stacks.math.columbia.edu/tag/0DV5),
   [0DV6](https://stacks.math.columbia.edu/tag/0DV6),
   [0A3R](https://stacks.math.columbia.edu/tag/0A3R),
   [04TR](https://stacks.math.columbia.edu/tag/04TR), and
   [04TS](https://stacks.math.columbia.edu/tag/04TS).
   The arbitrary-module extension is the agent's explicit fixed-torsor argument,
   not a claim that the first three tags state it directly. Fresh LeanFinder,
   Loogle and grep searches used effective descent, module-valued sheaves and
   constant-functor fullness as alternate queries. The hits concern condensed
   spaces or local sites, not the connected small etale site or this associated
   torsor functor. Repository searches found the existing additive-group
   continuous-map model of constant etale sheaves and the already-reused fibre
   isomorphism, but no replacement theorem closing a split in a few minutes.
4. PASS: followed the proof from the original target hole through the concrete
   functor, membership, faithfulness, fullness, essential surjectivity and
   `asEquivalence`. The parent really performs this reduction; no split restates
   the equivalence. New public imports are required by their declarations'
   signatures; the parent adds only proof imports. Removed imports and all five
   removed direct DAG proof dependencies are now named under No longer needed.
   The unit `sk-thm-p1` statement, all four steps and its `realized` fields are
   preserved; this construction is below that route. No whole module is claimed
   pruned from the targets' closure.
5. PASS after metadata repair: the existing node changes only `proof`,
   `proof_deps`, and `proof_origin`, and these match the compiled reduction.
   Checked all new nodes' source, creation, blueprint ancestry, chapter, unit,
   dependency lists and Lean declarations. Replaced normalized `lean.statement`
   strings in the four new nodes with the exact multiline declaration signatures
   (starting at `def` for the construction, as the preflight signature parser
   requires). The first dry run rejected the `noncomputable` prefix in node
   metadata; removed that prefix from metadata only and reran the dry run.

Second reading changed only metadata and the report: exact new-node signatures,
the explicit list of removed direct proof dependencies, and this independent
review. No Lean proof, statement, definition or import needed repair. The delivery
closes one original hole and adds three: it is a decomposition with net minus two,
not a sorry-free proof or positive net progress.
