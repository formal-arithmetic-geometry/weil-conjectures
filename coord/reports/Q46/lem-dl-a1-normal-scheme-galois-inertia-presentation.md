## Worker report

The module `Sheaf.AlgebraicGeometry.FundamentalGroup.NormalSchemeGaloisInertiaPresentation`
states `AlgebraicGeometry.Scheme.FiniteEtale.normalScheme_galois_inertia_presentation`.
It has one theorem with proof `sorry`, no new definitions, no axioms, and no helper theorems.
The source is Stacks `pione.tex`, setup preceding lemma-normal-pione-quotient-inertia and
Tag 0BTD (1)=(3), with surjectivity from 0BQM. I read that setup and proof directly.
The node's mathematical statement, proof, and proof dependencies are unchanged.

Hypothesis and clause correspondence:

- Normal integral scheme: `[IsIntegral X]` and
  `hX : ∀ x, IsIntegrallyClosed (X.presheaf.stalk x)`. Integral-scheme stalks are already
  domains (`Scheme.isDomain_stalk`), so their domain property is not an extra assumption.
  There is no Noetherian, finiteness, affine, separatedness or characteristic hypothesis.
- The function field is exactly `X.functionField`, Mathlib's generic stalk; its point is
  `X.fromSpecStalk (genericPoint X)`, rather than an unspecified dominant field morphism.
- Separable closure: `[Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]`.
  `Gal(Ω / X.functionField)` uses Mathlib's existing Krull topology.
- Algebraic closure containing Ω: `[Algebra Ω Ωbar] [IsAlgClosure Ω Ωbar]`, with its
  algebraically closed structure, the induced K-algebra, and the commuting scalar tower.
  The geometric generic point is `pointOfAlgebra (K := X.functionField) Ωbar` applied
  to the canonical generic-point morphism. These are structural choices, not further
  restrictions on K or Ω. In particular Ω need not be algebraically closed.
- For each x, arbitrary geometric-point residue choices are `Ωx`, `sx`, and `hsx`;
  `hsx` says the underlying point is x via the recorded `SpecToEquivOfField` equivalence.
  The rings are precisely the dependency's `strictHenselizationRing (sx x)`.
- These rings are domains: the first conclusion `∀ x, IsDomain (...)`.
  This is a conclusion, not a hidden typeclass assumption.
- Their fraction fields embed compatibly into Ω: the second conclusion explicitly
  asserts `∀ x, ∃ j : FractionRing (...) →+* Ω, Function.Injective j ∧ ...`.
  Its scheme diagram says `Spec Ω → Spec A_x^sh → X` equals the canonical
  `Spec Ω → Spec K → X`. Since K is the fraction field of every stalk, this is
  equivalent to extension of the canonical stalk embedding and therefore to a
  compatible K-embedding of the strict-henselian fraction field. There is no arbitrary
  scalar action on that field. `FractionRing` exists as a ring before proving the first
  conclusion, so its use does not assume the requested domain assertion.
- Automorphisms extend uniquely: the third conclusion is
  `∀ σ, ∃! σbar, ∀ a, σbar (algebraMap Ω Ωbar a) = algebraMap Ω Ωbar (σ a)`.
  This retains the purely inseparable extension issue in positive characteristic.
- The fundamental group uses the standard project convention from `coord/STATE.md`:
  arbitrary `G : Type u` with its profinite topology, fibre actions and
  `[IsFundamentalGroup (fiber barη) G]`. The existing
  `exists_fiber_flc_equivalence` identifies this group, topology, and evaluation action
  with `Aut (flcFiber barη)` from the recorded `def-galois-fibre-functor` interface.
  Thus this is the fundamental group of that node in its finite-etale model, not a new
  definition of the group or a different sheaf category. Every such model is covered.
- The map q is asserted to exist as a monoid homomorphism. The first conjunct after q
  specifies its value on every σ to be the existing `galoisToFundamentalGroup` applied
  to its unique extension σbar, at the identity fibre path. That existing map acts by
  precomposition with `Spec σbar` on every finite-etale geometric fibre. Consequently
  this equation determines the canonical generic-point map, not an arbitrary surjection.
- Continuity and surjectivity are exactly `Continuous q ∧ Function.Surjective q`.
- For every family of compatible injective embeddings j, `fixingSubgroup` of
  `Set.range (j x)` is exactly `Aut_{K_x^sh}(Ω)` as a subgroup of `Gal(Ω/K)`.
  The last equality identifies `q.ker` with
  `(Subgroup.normalClosure (⋃ x, ...)).topologicalClosure`. In a topological group
  this is exactly the smallest closed normal subgroup containing every J_x.
  The embeddings are universally quantified after q, so the same canonical q works
  for every choice. Neither their existence nor their domain property is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`: nonempty
  scheme with domain sections on nonempty opens; stalk-domain instance is inherited.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`:
  integral closure in `FractionRing`; the domain condition comes from integrality.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`,
  `IsSepClosure.exists_intermediateField_mem`, on the existing `IsSepClosure` class.
  Read its full signature and its union-of-finite-separable-extensions docstring.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`,
  `Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme` and
  `Scheme.strictHenselization_properties`: the recorded small affine-neighbourhood
  coordinate-ring colimit; I read their definitions, types and docstrings.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`, `Scheme.flcFiber`: the actual
  geometric stalk on the existing FLC subcategory. The existing comparison theorem
  in `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence` is a proof import.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`, `IsAlgClosure`, and
  `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.SpecToEquivOfField`: exactly the
  recorded geometric-point and algebraic-closure notions; their full types were read.
- Added the already landed statement dependency
  `def-weil-pbc-strict-henselization-structural-map`, whose module is
  `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap` and declaration
  is `Scheme.strictHenselizationStructuralMap`. Read its node, canonical common-composite
  definition and existence theorem; its use makes the K-compatibility diagram explicit.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction`,
  `FiniteEtale.pointOfAlgebra`, `galoisToAut`, `galoisToFundamentalGroup`, and their
  fibre-action characterizations: existing canonical maps, not recreated helpers.

The already recorded proof modules are imported without `public`: the fibre equivalence,
field G-set equivalence, normal-integral generic full faithfulness, henselian finite-etale
comparison, open-subgroup fixed field theorem, field Galois classification, and strict
henselization local structure. Mathlib proof inputs for Krull limits, normalization,
integral-closure localization, etale field products and profinite separation are imported.
The three new stage-1 algebra inputs with no Lean declaration yet are not imported:
`lem-dl-a1-henselian-global-inertia-comparison`,
`lem-dl-a1-inertia-restriction-surjective`, and
`lem-dl-a1-finite-group-inertia-invariants-etale`. They are proof dependencies only;
none is needed to elaborate this statement. All ten proof steps are retained in the
Lean docstring for stage 3.

Edge cases checked: the empty scheme is excluded exactly by integrality; Spec of a
separably closed field gives a trivial Galois group and trivial kernel; Spec K gives
an isomorphism and trivial strict-henselian inertia; a strictly henselian local normal
domain gives the full Galois group as kernel at its closed point. Arbitrary dimension
and non-Noetherian schemes are retained. Imperfect fields are retained by using Ωbar
separately from Ω and asserting unique extension. Generic and nonclosed points occur
in the same unrestricted index X. Conjugating any chosen embedding does not change
its closed normal closure. All variables and the universe u are explicitly bound.

Searches actually run using `msearch.py Q46 <item>`:

- LeanFinder: “For a normal integral scheme the absolute Galois group of the function
  field surjects onto the etale fundamental group with kernel the closed normal subgroup
  generated by strict henselian inertia”. Eight hits on absolute Galois groups,
  IsGaloisGroup, and abstract Galois categories; none states the scheme comparison.
- Loogle: `Field.absoluteGaloisGroup, Subgroup.topologicalClosure,
  IntermediateField.fixingSubgroup`. Zero hits.
- Mathlib grep: `normal.*[Ii]nertia|[Ii]nertia.*normal|fundamentalGroupMap`.
  Two hits, both normality of ideal inertia inside stabilizers, not this statement.
- LeanSearch: “Etale fundamental group normal integral scheme absolute Galois group
  kernel strict henselian inertia”. Eight hits on absolute Galois groups, valuation
  inertia, and the small etale topology; none states the comparison.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for normal/inertia, fundamentalGroupMap,
  Galois actions, strict-henselization/stalk maps, and FLC fibre comparisons found the
  existing interfaces used above. Boundary-inertia theorems concern curves or open
  immersion kernels, not the absolute Galois presentation for arbitrary normal integral X.
- The prescribed node-id grep in `lean/WeilConjectures` found no declaration of this
  item. Its declaration name was also searched in both source trees with no match.
  No new notion or dependency replacement was needed.

Validation: the prescribed `scompile.py` compiled both the sandbox name and the actual
module name cleanly (6.8 s and 8.2 s). Initial elaboration failures were repaired by
using the actual Mathlib module for subgroup closure, the global `fixingSubgroup` name,
and explicit scalar-ring arguments instead of metavariables. No errors or warnings
remain. No statement dispute or correction is required.

## Second reading by Q46

Worker's separate second pass over the complete node and final Lean file; independent
review is the maintainer's delivery review, as specified in this dispatcher's brief.
I checked each binder and conclusion against the clause correspondence above, including
normality without Noetherianity, the actual generic stalk, arbitrary geometric points
above every x, domain and embedding existence as conclusions, all embeddings quantified
after the single canonical q, and the unique-extension formula in imperfect characteristic.
I also checked that the small fundamental-group model uses the existing finite-etale/FLC
comparison, rather than assuming an unrelated group or a kernel-generation property.
No mathematical mismatch was found. The elaboration repairs only made existing canonical
scalar structures explicit; no node statement or proof was changed.
