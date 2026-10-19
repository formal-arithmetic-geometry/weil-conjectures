## Worker report

`Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement` states
`AlgebraicGeometry.Scheme.GaloisPartition.exact_refinement` with `sorry` and defines
only the two documented predicates `constructible` and `IsDirected`. It imports
Q59's landed `Sheaf.Paper.GaloisPartitionModules`, the canonical interface of
`def-per-galois-partition-modules`. No statement correction was necessary.

Hypothesis and clause audit against the current item node:

- Prime ell and its prime field: `(ℓ : ℕ) [Fact ℓ.Prime]` and `ZMod ℓ`.
- Noetherian scheme: `(X : Scheme.{u}) [IsNoetherian X]`.
- Commutative Noetherian algebra over that prime field:
  `(A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
  [Algebra (ZMod ℓ) A]`. The zero ring is included.
- The ambient category is the existing constant-coefficient convention
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`. The small etale site's
  different object and arrow universes are retained.
- `GaloisPartition X` is Q59's existing structure: its parent
  `FiniteLocallyClosedStratification X` gives finite, disjoint, locally closed
  strata covering X, realized by scheme immersions. Its fields `connected`,
  `reduced`, `cover`, and `galois` give nonempty connected reduced strata and
  actual connected finite etale Galois covers. The Galois predicate specializes
  `PreGaloisCategory.IsGalois` using `FiniteEtale.galoisCategory`; its geometric
  characterization is the simply transitive action on geometric fibres.
- W_P(A) is exactly the landed `P.modules A`. Its `FiniteExtensions` uses a
  finite filtration starting at zero, ending isomorphically at the given sheaf,
  and short exact sequences whose quotients are `IsLocallyConstantSheaf` and
  become `Sheaf.IsConstant` after `Etale.upperStar` along the cover. `modules`
  restricts along the stratum immersions and asks for an actual small filtered
  diagram, a colimit cocone, and an isomorphism to that restriction. It adds no
  finite-generation restriction.
- D^b_P(X,A), which the node introduces as notation, is already the landed
  `P.boundedDerived A`, using `Etale.DerivedCategoryModule` and
  `DerivedCategory.homologyFunctor`, with an integer vanishing interval and all
  cohomology in `P.modules A`. It is neither replaced nor redeclared.
- `P.constructible A F` is the real predicate
  `P.modules A F ∧ IsConstructibleSheaf F`. The existing latter predicate is a
  finite stratification with locally constant finitely generated geometric
  stalks. Over Noetherian X the constructibility of each locally closed stratum
  is automatic; no stronger finiteness condition on its underlying set is used.
- The first conjunct quantifies over every `P : GaloisPartition X`. Its eight
  categorical clauses are, in order:
  (1) `Nonempty (Abelian (P.modules A).FullSubcategory)`;
  (2) `PreservesFiniteLimits (P.modules A).ι`;
  (3) `PreservesFiniteColimits (P.modules A).ι`;
  (4) `(P.modules A).IsClosedUnderExtensions`;
  (5) for every `J : Type (u + 1)` with `[SmallCategory J] [IsFiltered J]`,
      `(P.modules A).IsClosedUnderColimitsOfShape J`;
  (6) `(P.constructible A).IsClosedUnderKernels`;
  (7) `(P.constructible A).IsClosedUnderCokernels`;
  (8) `(P.constructible A).IsClosedUnderExtensions`.
  The finite limit/colimit clauses encode exactness of the inclusion. The
  filtered-colimit assertion concerns ambient colimits; the last three clauses
  concern maps or short exact sequences with their endpoints in the stated
  constructible class.
- Every finite family is `(n : ℕ) (P : Fin n → GaloisPartition X)`, including
  `n = 0`. The conclusion supplies one `R : GaloisPartition X`, then
  `R.IsDirected`, then
  `∀ (i : Fin n) (B : Type (u + 1)) [CommRing B], R.Refines (P i) B`.
  Q59's `Refines` unfolds to `(P i).modules B ≤ R.modules B`. Thus one R works
  simultaneously for every B; B has no Noetherian or characteristic assumption.
- `IsDirected` uses a permutation of `Fin R.n` and says the complements of
  every initial union are closed. Because the strata are a partition, the next
  piece is open in the previous closed complement. The prescribed reduced
  scheme structures express the reduced-complement condition without extra
  scheme choices. The source calls existence of such an ordering dirigeable;
  this is exactly the item's 'can be ordered' formulation.

Dependency declarations used (read from their source, not inferred from names):

- `Sheaf.Paper.GaloisPartitionModules`: `Scheme.GaloisPartition` and its
  `.FiniteExtensions`, `.modules`, `.Refines`, `.boundedDerived`; the complete
  current source was also retrieved with `scompile.py --source`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` and its topological parent.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `WeilConjectures.ConstructibleSheaf.Defs`:
  `Scheme.IsLocallyConstantSheaf`, `Scheme.IsFiniteSheaf`,
  `Scheme.IsFiniteLocallyConstantSheaf`, `Scheme.IsConstructibleSheaf`.
  These supply the small-etale realization exposed by the dependency
  `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`; its generic
  `SheafOfModules.IsLocallyConstantFiniteTypeModules` was read, not copied.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`; `DerivedCategory.homologyFunctor` is Mathlib's.
  This is the recorded constant-module-valued realization of the derived category,
  rather than a second copy of `CategoryTheory.ringedSiteModules` (the generic
  `SheafOfModules` abbreviation in `Sheaf.CategoryTheory.RingedSiteModules`).
- `Mathlib.CategoryTheory.Galois.GaloisObjects`: `PreGaloisCategory.IsGalois`;
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`:
  `FiniteEtale.galoisCategory` and its geometric Galois characterization.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `colimit`;
  `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, used through
  `Sheaf.IsConstant` in the existing partition module.
- Ambient closure predicates are Mathlib's `ObjectProperty` predicates in
  `Extensions`, `Kernels`, and `ColimitsOfShape`; fullness and inclusion are the
  existing `.FullSubcategory` and `.ι`.

All currently recorded proof-dependency modules are imported privately, including
`Sheaf.RepresentationTheory.NormalSubgroupIndUnipotence`, which landed since the
old packet. The Mathlib proof leaf `Submodule.FG.of_le` is provided by the private
`Mathlib.RingTheory.Noetherian.Basic` import. The monodromy node currently has no
recorded module; no untracked theorem is substituted for it. The theorem docstring
retains the complete eight-step proof plan and its named dependencies.

Edge cases checked: empty scheme and empty partition; `n = 0` still requires a
partition and directedness even though all refinement obligations are vacuous;
`n = 1` includes refinement of a single partition. In `IsDirected`, the endpoints
of the initial-segment range give the whole space and empty closed complement;
for an empty partition they give the empty scheme. Connected strata exclude
empty pieces. The zero coefficient ring and infinite coefficient modules remain
allowed. `IsFiltered` includes nonemptiness. No independent universe is chosen
below the site or coefficient universe.

Searches retained from the saved investigation: `msearch.py` LeanFinder for
'Galois partitions weakly constructible sheaves exact abelian category common
directed refinements' returned eight unrelated condensed/topological results;
Loogle for 'CategoryTheory.ObjectProperty, CategoryTheory.IsFiltered' returned
generic ObjectProperty/filtered infrastructure, not this theorem; LeanSearch for
'Finite Galois partition of scheme weak constructible sheaves filtered colimits
extensions' returned generic infrastructure; Mathlib grep for
`GaloisPartition|weakly.constructible|FCons` found no matching definition.
Those searches do not establish current absence in the side library: the repair
repeated direct rg for `GaloisPartition|weakly.constructible|def IsDirected` in
`lean/Sheaf` and the upstream `WeilConjectures` tree and found Q59's landed
canonical module plus its consumer `CtfHomLocallyConstant`. There were no existing
`GaloisPartition.constructible` or `.IsDirected` helpers, nor another exact theorem.
The exact item id is absent upstream. Q59's module and its DAG node now supersede
the old packet's claim that the partition notion lacked a node.

Source checked again: local PDF pages 309--314, printed pp. 303--308, ILO XVII
7.3.1--7.3.8 and 7.4.5. In particular 7.3.5 gives the recursive open-first ordering,
7.3.8 gives common refinements, and 7.4.5 is the full constructible subcategory.
No statement dispute remains.

## Repair of return L (immutable head 465367b6f816)

Addressed H12/H4 and the H9 name clash by deleting the sandbox's new node
`def-per-galois-partition-weak-constructibility` and its entire module
`Sheaf.AlgebraicGeometry/GaloisPartition.lean`. The packet now contains one Lean
module and one node record. It adds the already landed
`def-per-galois-partition-modules` to the item's `stmt_deps`, uses `modules` for
W_P, and uses the existing ring-parameterized `Refines` for every B. Only the
nonduplicating `constructible` and `IsDirected` helpers remain, documented in the
item's module and listed in its `lean.declarations`. No GaloisPartition structure,
constructor, finite-extension, bounded-derived, or refinement name is redeclared.

The node was regenerated from the current read-only shared copy, retaining every
field except `lean` and the authorized added landed statement dependency. The
human-readable item statement and all proof fields are unchanged. This is a
substantive source repair, not an unchanged re-push of the returned packet.

## Second reading by Q91

Reopened the repaired module, current item node, and complete Q59 source after
the edits. Checked the prime-field, Noetherian scheme, Noetherian coefficient
algebra, and all eight closure clauses individually against the mapping above.
The same existing GaloisPartition type now occurs in this theorem and the landed
consumer; every W_P is Q59's `modules`. The refinement binder order chooses R
before all indices and rings, preserving coefficient independence, and includes
empty input families. The finite-extension and filtered-colimit data are Q59's
actual constructions, not the old inductive duplicate. The two remaining helper
predicates use that same type and contain no sorry. Compared their docstrings
and formulae to ILO 7.3.5 and 7.4.5; both express precisely the node's terminology.

Mismatch found and repaired: the old packet defined the partition vocabulary a
second time and buried coefficient quantification in its duplicate Refines. The
new packet uses the landed vocabulary with explicit coefficient quantification;
it also imports the proof dependency that has since acquired a Lean module.
The theorem remains the only postponed proof, with its named DAG node and full
proof docstring. `autoImplicit` and `relaxedAutoImplicit` are both false.

## Validation

The final module passed `scompile.py` in both sandbox and library placements
without errors or warnings. The repaired packet passed `deliver2.py --no-push`
(server preflight and per-file compilation). A local source-only self-check
confirmed the recorded signature verbatim, the authorized two-field node delta,
exactly one delivered node and module, one postponed theorem, no overlong Lean
lines, and complete removal of the old weaklyConstructible vocabulary. The old
missing-artifact history no longer applies. Delivery is through the prescribed
wrapper against current newtargets-dag.
