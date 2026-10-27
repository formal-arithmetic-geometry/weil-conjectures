## What changed

Replaced the sole proof hole in `Sheaf.Paper.LisseLatticeHeartLift` by a complete Lean
assembly of five strictly smaller, source-backed steps. The assembly proves the
rational standard-heart condition directly from the vanishing of the homology of a
single complex. On each quasi-compact etale chart it conjugates the specified sheaf
isomorphism by the actual single comparisons, lifts it with `Functor.preimageIso`,
proves both required equations, and proves uniqueness by cancellation and faithfulness.
These local isomorphisms are the inputs to completed-pullback lisse descent.

Moved the existing helper data to `Sheaf.Paper.LisseLatticeHeartLiftData` verbatim.
The item publicly reexports this module, including every original public import.
This permits each new proof-step module to import the definitions without a cycle.
The helper declarations, definitions, visibility, and theorem signature are unchanged;
no data are selected from an unproved existence theorem. The change record is
`coord/changes/U9-lisse-lattice-heart-lift-data.md`.

The original nine mathematical steps are retained: normalization, the two independent
lattice constructions and affine etale refinement, integral single-complex membership,
exact localization, normalized Hom comparison, unique specified lifting, and completed
pro-etale pullback. No unit or chapter route changes.

## Proved and sorry left

Original hole closed by decomposition:
`WeilConjectures.LisseLattice.lisse_lattice_heart_lift` (1 of 1 original holes).
The item and the data module now have zero direct `sorry` occurrences.

The new private theorems `unique_specified_lift` and `single_rational_heart` are proved.
The main proof uses them to prove the forward and inverse equations, uniqueness,
and rational standard-heart membership. Its proof has no remaining subgoals.

Five new holes, one public theorem and one new module each:

- `WeilConjectures.LisseLattice.normalized_realizations`:
  `lem-tw-lisse-lattice-normalized-realizations`.
- `WeilConjectures.LisseLattice.lattice_choice_exists`:
  `lem-tw-lisse-lattice-choice-existence`.
- `WeilConjectures.LisseLattice.lattice_single_comparisons`:
  `lem-tw-lisse-lattice-single-comparisons`.
- `WeilConjectures.LisseLattice.normalized_realization_fully_faithful`:
  `lem-tw-lisse-lattice-realization-faithful`.
- `WeilConjectures.LisseLattice.lattice_lisse_of_local_isomorphisms`:
  `lem-tw-lisse-lattice-lisse-descent`.

Each is exactly `:= by sorry` with its source, a full proof in words, and its node.
This is a decomposition, not a net hole reduction: 1 closed, 5 added, net -4.
The full theorem is not claimed to be axiom-free while these five steps remain open.

## No longer needed

No mathematical node or library module is withdrawn or pruned. Every original
nontrivial ingredient remains a stated proof dependency of the five proof-step nodes. In particular,
no upstream source declaration is changed, removed, or given a new hole.

The item itself no longer directly imports these original proof modules:
- `Sheaf.Paper.OrdinaryCompletedIntegralPullback`.
- `Sheaf.Paper.ConstructibleRationalHomComparison`.
- `Sheaf.Paper.ContinuousCoefficientSliceNormalization`.
- `Sheaf.Paper.RationalContinuousCoefficientDerivedLocalization`.
- `Sheaf.Paper.CompletedPerfectScalarPullback`.
- `Sheaf.Paper.IntegralPullbackComposition`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`.
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`.
- `Sheaf.Paper.LisseEConstructibleIntegralLattice`.
- `Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal`.
- `Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.Topology.NoetherianSpace`.

Their mathematical work now belongs to the corresponding smaller statements; this
is relocation, not mathematical pruning. Each split theorem module imports only the
data its statement needs; its future proof dependencies remain in its DAG node, rather
than adding unused imports to a proof that is still `sorry`. The data module retains every original public import.
The parent node no longer directly lists the former tool approvals, because it now
uses the new substeps; the former dependencies remain below those substeps. The
parent's categorical proof uses Mathlib's existing fully faithful preimage-isomorphism
construction rather than separately introducing two new morphism-existence holes.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. The declarations of the listed proof
dependencies use different coefficient presentations and different integral
constructible categories. In addition, `exists_lisse_lattice_etale_local` currently
fixes `E : Type`, whereas the item allows `E : Type u`; the lattice-choice substep
records coefficient transport through a small field model, available from finite
dimension over the small field Q_l, before applying that declaration. Applying them to the accepted `Realizations` and `Choice`
records requires normalization and transport arguments; the new modules state those
strict substeps rather than repeating the full target statement.

Read Bhatt--Scholze 6.8.2--6.8.15, especially pp. 59--62, and the current blueprint
unit `literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-r-real-linear/`.
The current unit and its record differ historically, but this proof-level split
changes neither; it retains the accepted lattice input to the unit's duality route.

Edge cases checked mathematically: empty schemes and empty covers; rank zero;
variable finite ranks; torsion local finitely presented models of N; arbitrary alpha
and beta; non-separated finite-type bases; and non-noetherian pro-etale trivializing
charts. The single-complex heart proof uses no local freeness, and the categorical
lift proof is valid for any full and faithful functor with the two comparison isos.
No new lemma asserts a globally free integral lattice.

## New nodes

`def-tw-lisse-lattice-heart-lift-data`: unchanged definitions formerly in the item,
relocated for acyclic proof imports, with no new existence-based data construction.

`lem-tw-lisse-lattice-normalized-realizations`: only the coefficient and balanced
restriction constructions of original step 2, for all schemes.

`lem-tw-lisse-lattice-choice-existence`: only existence of N, alpha and local lattice
choices on quasi-compact etale charts, original steps 1--4; no heart or local lift.

`lem-tw-lisse-lattice-single-comparisons`: integral membership and invertibility of
the actual single comparisons, original steps 5--6; no raw isomorphism lifting.

`lem-tw-lisse-lattice-realization-faithful`: transport of the existing normalized Hom
comparison to the accepted realization presentation, original step 7; no lattice data.

`lem-tw-lisse-lattice-lisse-descent`: the completed-pullback local triviality argument
of original step 9, assuming the already lifted raw local isomorphisms; it neither
constructs those lifts nor proves their uniqueness or specified image equations.

Every new statement has LeanSearch, LeanFinder, Loogle and source-grep search records.
The generic `Functor.preimageIso` match is used directly in the parent. None of the
search results supplies these normalized pro-etale transport statements.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
