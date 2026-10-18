## What changed

Replaced the one `sorry` of `AlgebraicGeometry.Scheme.galois_lisse_representations`
by a finite/adic assembly proof. The original theorem signature and all existing data and
clause definitions retain their meanings. Moved those definitions to
`Sheaf.Paper.GaloisLisseRepresentationData` and publicly re-exported them, avoiding cycles
between the four proof components and the final assembly. All original public imports stay.
See `coord/changes/galois-lisse-data-relocation.md` for the old/new code and 39 consumers.

The Lean glue proves the finite-etale evaluation comparison, identifies the two lissity
predicates over every finite ring (including noncommutative rings), proves closure under
kernels/cokernels and the full abelian-subcategory criterion, and obtains finite (co)limit
preservation from equivalences. On the adic side it constructs the profinite model explicitly using
`ProfiniteGrp.ofContinuousMulEquiv` and the finite-etale fundamental-group homeomorphism.
The identification on its unchanged carrier is `ContinuousMulEquiv.refl`. It transfers
abelian structures across
fully faithful equivalences and derives all three diagonal tensor and unit clauses from
the monoidal constraints. The tensor equation is `Rep.hom_comm_apply` applied to the
monoidal tensor isomorphism; no tensor-equivariance clause is assumed in its place.

The original data module was near the compile limit (the previous review records 58.66 s).
Profiling identified expensive reductions into p-adic Cauchy-sequence norms during failed
prime-parameter comparisons. Local transparency controls and direct instance caches,
plus disabling unused generated injectivity/sizeOf auxiliaries, bring serialized data
compilation to about 32 seconds without changing a mathematical definition.

Validation: all six delivery modules compile together without warnings; the final assembly
compiled in 20.3 seconds. The 46 relocated declarations have identical signatures and
bodies. Both unchanged direct consumers also compile against this delivery:
`Sheaf.AlgebraicGeometry.LisseFiniteEtaleFiltration` (5.1 s) and
`WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` (12.6 s). Their validation copies
are not delivered. No consumer needs adaptation. Searches found no consumer of the
disabled generated injectivity/sizeOf auxiliaries. The delivery dry run passed compilation,
axiom checks and preflight (review class CODEX, because of the new nodes and relocation).

## Proved and sorry left

Original holes: 1. Closed in the item module:
`AlgebraicGeometry.Scheme.galois_lisse_representations`
(node `cor-galois-lisse-representations`). This is a decomposition, not an axiom-free proof
of the entire correspondence: four strictly smaller parts remain, so the delivery adds
four holes and has net +3 holes. There is no `sorry` left in the item module or data module.

Every new hole is a public theorem whose entire proof is `:= by sorry`, in its own module,
with a source and full proof in words:

- `AlgebraicGeometry.Scheme.galois_lisse_finite_module_lift`
  (`lem-pod-galois-lisse-finite-module-lift`): transport the existing module-object
equivalences through the set correspondence, bridge the two internal-module encodings,
flatten finite/discrete-continuous subcategories, handle the universe lift, and identify
the linear stalk comparison and its evaluation formula.
- `AlgebraicGeometry.Scheme.galois_lisse_finite_compatibility`
  (`lem-pod-galois-lisse-finite-compatibility`): prove equivariance of the existing tensor
and scalar stalk comparisons by naturality of the evaluation automorphisms, and lift the
braided/coherent coefficient comparisons. The constant stalk gives the trivial unit.
- `AlgebraicGeometry.Scheme.galois_lisse_adic_equivalences`
  (`lem-pod-galois-lisse-adic-equivalences`): for the specified profinite model, construct integral limit actions and compare
Hom groups using the stated adic reconstruction theorems; rationalize using a stable
lattice; localize over finite coefficient fields and verify the three evaluation/model
formulas. This statement does not include abelianity, exactness, monoidal or tensor clauses.
- `AlgebraicGeometry.Scheme.galois_lisse_adic_compatibility`
  (`lem-pod-galois-lisse-adic-compatibility`): continuity for kernels/cokernels and descent
of morphisms give representation abelianity; finite-level tensor/scalar comparisons pass
through adic limits, rationalization and coefficient localization. It assumes the already
constructed equivalences with evaluation formulas and does not restate their existence.

No existing dependency theorem was duplicated. Existing `sorry` dependencies are inputs,
as intended by stage 3. No definition chooses data from an unproved mere existence statement; existential
witnesses are combined only inside the proof of the original existential theorem.

## No longer needed

Removed the following proof imports from the item module:

- `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`
- `Sheaf.CategoryTheory.EquivalenceInternalModule`
- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`
- `Sheaf.Paper.LisseAdicSheaves`
- `Sheaf.RepresentationTheory.ProfiniteStableLattice`
The module-object, adic and stable-lattice imports are needed by the component plans or are publicly available via the
unchanged data imports; they are not claimed as globally pruned modules. The source
lisse-module declarations are available through the unchanged public wrapper. The unused
private `galoisTensorAction_eq` was removed; tensor equivariance is checked directly.

The explicit exact-stalk dependency `prop-weil-pbc-geometric-stalks-exact` is unnecessary
for the assembly: an equivalence preserves finite limits and colimits. It is removed from
the corollary's proof dependencies and is not introduced by the four subproblems. All other
original declared dependencies remain relevant through the component proofs. There is no
claim that their modules disappear from the global target import closure; none is withdrawn.

The original `sk-lem-finite` unit route stays: the same finite and adic correspondence is
assembled, with the original finite-etale/FLC equivalence. Its realized-statement/step
records are empty; no required unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned declarations exist, as the brief says. Their interfaces do not directly compose:
`LambdaModuleObject` records diagrams in all set sheaves, whereas `InternalModule` records
generalized-element axioms in FLC; `FiniteContinuousModule` is a nested subcategory in a
smaller universe, whereas the correspondence uses one full subcategory of `Rep` in u+1.
The new finite-lift theorem isolates exactly that bridge, with the given evaluation formula.
The source library's proved finite correspondence in `RealSheaves.LocalSystems` covers
commutative rings; the current corollary also quantifies over noncommutative finite rings.
It therefore cannot replace that bridge unchanged.

The data declarations have no mathematical defect discovered in this session. Their
elaboration was expensive enough to prevent adding the proof without the local controls
explained above. This is an elaboration repair, not a compile-limit increase or a file split
to evade the limit: the data file contains all original data and both correspondence records.

## New nodes

`def-pod-galois-lisse-correspondence-data` owns the unchanged relocated data/clauses. It has
zero holes; `cor-galois-lisse-representations` now owns only the assembled theorem.

`lem-pod-galois-lisse-finite-module-lift` isolates the module lift of the given set equivalence
(original proof step 1). `lem-pod-galois-lisse-finite-compatibility` isolates its tensor, unit
and scalar compatibilities (steps 3-5).

`lem-pod-galois-lisse-adic-equivalences` isolates the integral/rational/algebraic evaluation
equivalences (steps 6-9). `lem-pod-galois-lisse-adic-compatibility` isolates the remaining
representation-abelian, monoidal and scalar comparisons (steps 9-10). Each has three kinds
of recorded search and the complete source proof in its docstring and node.

Change record: `coord/changes/galois-lisse-data-relocation.md`.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
