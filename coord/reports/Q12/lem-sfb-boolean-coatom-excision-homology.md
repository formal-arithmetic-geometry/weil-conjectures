## Worker report

The module `Sheaf.AlgebraicTopology.BooleanCoatomExcisionHomology` states
`AlgebraicTopology.AugmentedPosetChains.BooleanCoatom.excision_homology`, with
one postponed theorem and no new definitions. It is the per-degree consequence
of the already recorded derived theorem, rather than a second statement of that
derived theorem. The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- The finite set E is `{E : Type u} [Fintype E]`, in an arbitrary universe.
  `[DecidableEq E]` supplies the finite-subset implementation used by the recorded
  dependency; every finite set admits this structure, with no mathematical restriction.
- The bound |E| >= 2 is `(hcard : 2 ≤ Fintype.card E)`.
- The chosen element a in E is `(a : E)`; the underlying whole set is
  `(Finset.univ : Finset E)`.
- The smaller set v = E minus {a} is the dependency's `coatom a`, definitionally
  `Finset.univ.erase a`.
- P_F and its inclusion order are the dependency's `Proper F`, the subtype
  `{S : Finset E // S.Nonempty ∧ S ⊂ F}`. A subset of F is nonempty and unequal
  to F exactly when it is nonempty and a strict subset of F.
- B_F = C(P_F; Q) is exactly `booleanComplex F`, which unfolds to the recorded
  `AugmentedPosetChains.complex ℚ (Proper F)`.
- Every integer n is the explicit unrestricted binder `(n : ℤ)`.
- H_n(B_E) is `(booleanComplex (Finset.univ : Finset E)).homology n`.
  H_(n-1)(B_v) is `(booleanComplex (coatom a)).homology (n - 1)`.
- The isomorphism of rational vector spaces is `Nonempty (... ≅ ...)` in
  `ModuleCat.{u} ℚ`, so both directions are rational linear and inverse. This is
  an existence assertion about an isomorphism, as in the node; it does not claim
  a numerical dimension equality alone. The proof docstring specifies precisely
  the construction from H^(-n) of the existing `derivedComparison` and the
  identity-on-terms suspension identification, reproducing all three DAG steps.
  No derived-category size hypothesis is added to this homology assertion:
  stage 3 can choose `HasDerivedCategory.standard` when applying the dependency.

Recorded dependency declarations used:

- `Sheaf.AlgebraicTopology.AugmentedPosetChains`:
  `AlgebraicTopology.AugmentedPosetChains.complex`; read the full definition,
  strict-chain and augmentation definitions and docstrings.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology`; read its context `[K.HasHomology i]`, its
  signature and definition via `K.sc i`. Also read
  `ShortComplex.moduleCatLeftHomologyData` in Mathlib's ShortComplex/ModuleCat
  to check that this is kernel modulo image for modules.
- `Sheaf.AlgebraicTopology.BooleanCoatomExcisionDerived`:
  `AlgebraicTopology.AugmentedPosetChains.BooleanCoatom.Proper`,
  `booleanComplex`, `coatom`, `suspension`, `reversal`,
  `reversalSuspensionIso`, `derivedComparison`, and `excision`; the entire
  module was read, including the signed deletion representative and its proof.
  This is both a statement dependency (supplies the actual complexes) and the
  sole mathematical proof dependency, so its import is public.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory`, and `DerivedCategory.Q`.
  Their definitions and docstrings were read; the public derived-excision
  module supplies this statement dependency transitively.
- Proof import `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`, whose
  signatures and docstrings were read for the argument applying H^(-n).

Source checks: read the current `literature/blueprint/latest/blueprint/`
direct-images proof, paragraph (3). It contains no exact combinatorial theorem,
as the node already explicitly records. Read Stacks homology.tex at
`section-complexes`, `definition-shift-cochain`, and
`definition-cohomology-shift`, and derived.tex at `section-derived-categories`
and `definition-unbounded-derived-category`. These confirm reversal, the sign
of the shift, and cohomology factorization; they are not represented as a
literature proof of Boolean excision. The latter is the existing agent-written
DAG proof. No released repair note exists for this item.

Edge cases checked before writing:

- |E| = 2: P_E consists of two isolated vertices, with augmented H_0 = Q;
  v has one element, so P_v is empty and its augmented complex is Q in degree
  -1. The asserted n = 0 isomorphism has exactly the right shift.
- |E| = 3: the proper-subset order complex is a hexagon, giving H_1 = Q;
  the smaller interval has two vertices and H_0 = Q.
- n = -1: B_E has zero augmented H_(-1), since P_E has a vertex;
  the right side is H_(-2) = 0. Below -1 all terms vanish. Higher integer
  degrees are allowed and no artificial nonnegative-degree assumption is used.
- The empty/singleton cases of E are excluded exactly by the given bound;
  the necessary empty P_v at |E| = 2 remains included. No nonemptiness of
  P_v is assumed. E may live in any universe.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "The rational homology of the augmented strict-chain
  complex of proper nonempty subsets of a finite set is isomorphic to the homology
  for the set minus one element, shifted by one"`: eight hits, generic
  restriction homology isomorphisms, alternating constant homology, and group
  representation resolutions; no Boolean excision statement.
- `msearch.py ... loogle '"homology", "BooleanAlgebra"'`: zero hits.
- `msearch.py ... grep
  'Boolean.*homolog|coatom.*homolog|proper.subset.*homolog|poset.*homolog'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Reduced rational homology of proper nonempty subsets
  of a finite set satisfies a suspension recurrence after deleting one element"`:
  eight hits, including Finset erase/strict-subset facts and general homology-data
  recursors; none state the recurrence.
- `rg -n 'Boolean.*[Hh]omolog|coatom.*[Hh]omolog|booleanCoatom|excisionHomology'
  lean/WeilConjectures lean/Sheaf`: no matching existing declaration.
- `rg -n 'lem-sfb-boolean-coatom-excision-homology' lean/WeilConjectures`:
  no upstream attachment or declaration. Further inspection of homology modules
  under `lean/Sheaf/AlgebraicTopology` found unrelated free-homology comparisons.

No new nodes, dependency repairs, statement correction or disputed statement.

## Second reading by Q12

A separate second pass by the same worker, with the node, dependency module and
new file open (no other agents were started, as the dispatcher requires), checked
all binders and both homology objects. The full finite set is `Finset.univ`;
the smaller Boolean poset uses `coatom a`, not the deleted poset D and not a
non-augmented complex. `homology (n - 1)` agrees with reversal followed by
cochain shift [1], including the empty smaller poset and negative degrees.
The result is an isomorphism in rational modules, not an isomorphism of underlying
sets. The per-degree node builds on the existing derived statement without
redeclaring it. Both implicit-variable options are disabled, and all variables
and universes are explicit. No mismatch was found and no statement was changed.
The maintainer's independent delivery review remains independent of this pass.

Validation: `scompile.py Q12 lem-sfb-boolean-coatom-excision-homology` compiled
the delivered module successfully in both sandbox and library mode (1.7 s and
1.3 s respectively), with no compiler messages or unexpected warnings.
