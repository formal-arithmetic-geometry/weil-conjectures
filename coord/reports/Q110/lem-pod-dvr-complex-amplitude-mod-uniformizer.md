## Worker report

The module `Sheaf.Algebra.Homology.DerivedCategory.DVRComplexAmplitude` states
`DerivedCategory.cohomology_amplitude_of_uniformizer_cone`, with `sorry` as its
entire proof. It adds no definitions. The node is unchanged except for `lean`.
There are no new nodes, dependency modules, statement corrections, or disputed
statements.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A discrete valuation ring is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`, using the recorded Mathlib class.
- Its uniformizer is `(ϖ : R)` with
  `hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}`. This is literally the
  generator-of-the-maximal-ideal definition in `def-sc-discrete-valuation-ring`;
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` confirms its equivalence
  with Mathlib's alternative `Irreducible ϖ` formulation.
- The category `D(R)` is `DerivedCategory (ModuleCat.{max u v} R)`, with
  `[HasDerivedCategory.{w} (ModuleCat.{max u v} R)]` selecting its morphism size
  as prescribed by `def-weil-abstract-derived-category`. Universes `u v w` are
  explicitly bound; the module-carrier universe is at least the ring universe.
  No equality of these universes is imposed.
- The arbitrary object is `M`; `H^i(M)` is
  `(DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj M`.
  These are the cohomology modules of a representing cochain complex, by
  `DerivedCategory.homologyFunctorFactors`.
- Vanishing in all but finitely many degrees is `hbounded : Set.Finite
  {i : ℤ | ¬ IsZero ((homologyFunctor (ModuleCat.{max u v} R) i).obj M)}`.
  This also covers the empty support of the zero object.
- Finite generation of every cohomology module is `hfinite : ∀ i : ℤ,
  Module.Finite R ((homologyFunctor (ModuleCat.{max u v} R) i).obj M)`.
  `Module.Finite` means finite generation, not finite underlying cardinality.
- The node explicitly stipulates a cone model for `M ⊗^L_R κ`, where
  `κ = R/ϖR`. Its model is the object `N` with arrows `ι : M ⟶ N` and
  `δ : N ⟶ M⟦(1 : ℤ)⟧` and
  `hcone : Triangle.mk (ϖ • 𝟙 M) ι δ ∈ distTriang _`.
  This is the ordinary distinguished-triangle specification of a cone of the
  *fixed* scalar-multiplication map. It introduces neither an arbitrary first
  map nor an extra mathematical condition on M: every such map has a cone,
  and any two cone triangles of the fixed map are isomorphic. In particular
  this quantifies over all models of the cone already stipulated in the node.
  By the two-term free resolution `R --ϖ--> R` of `κ`, this is precisely the
  derived residue reduction, viewed in D(R); forgetting the κ-module structure
  preserves and reflects the cohomology vanishing in question. No independent
  residue-field object or derived-tensor definition is needed for this cone
  formulation of the node. The triangle's shift is cohomological `[1]`.
- The integers and their order are `(a b : ℤ) (hab : a ≤ b)`.
- Vanishing of the reduction outside the *closed* interval is
  `hN : ∀ i : ℤ, i ∉ Set.Icc a b → IsZero (...obj N)`.
- The conclusion is the same predicate and the same interval for M:
  `∀ i : ℤ, i ∉ Set.Icc a b → IsZero (...obj M)`.

The source was read locally: Milne, Theorem 19.2 and its proof, printed p. 125
(PDF page 125), with the quotient/torsion short exact sequence and generators
modulo l; Stacks `algebra.tex`, `lemma-NAK`, part (2); and `derived.tex`,
`lemma-cohomology-homological` and the following long exact sequence. The current
blueprint `main-20261015`, `prop-cohomological-finiteness.proof.md`, Step 4,
and unit `sk-lem-finite/_section.md` were read. The declaration docstring carries
both proof steps of the node: obtain the quotient/torsion sequence from the cone
triangle, and apply degreewise Nakayama using finite generation and the maximal
ideal `(ϖ)`.

Dependency declarations used, with their signatures and docstrings inspected:

- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.mem_distTriang_iff`; imported through
  the homology-sequence and linearity modules. No private derived category.
- `def-sc-discrete-valuation-ring` (Mathlib leaf, no lean record required):
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`
  and `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `lem-sf-derived-homology-long-exact` (Mathlib leaf):
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.HomologySequence.δ`, `exact₁`, `exact₂`, `exact₃`.
  The same public module supplies the cohomology functor used in the statement.
- `lem-weil-pbc-nakayama-jacobson` (Mathlib leaf):
  `Mathlib.RingTheory.Nakayama`,
  `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`. This proof-only dependency
  has an ordinary, non-public import.
- Supporting standard notions: `ModuleCat` and its abelian structure from
  `Mathlib.Algebra.Category.ModuleCat.Abelian`; the canonical R-linear structure
  on the derived category from `Mathlib.Algebra.Homology.DerivedCategory.Linear`;
  `Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs`.

Edge cases checked mathematically before writing:

- M = 0, with its zero cone: finite support is empty and the conclusion holds
  for every allowed interval, including a=b. No nonzero-complex assumption.
- M = R[0]: the cone is κ[0]. An interval containing degree zero gives the
  claimed bound; an interval omitting it fails precisely the reduction premise.
- M = κ[0]: its reduction has cohomology in degrees -1 and 0 (multiplication
  by ϖ is zero), so the hypothesis does not incorrectly ignore Tor in degree -1.
- A shifted torsion module R/(ϖ²) concentrated in any integer degree gives the
  same two adjacent degrees in its reduction. Negative degrees and both interval
  endpoints are retained by the ℤ indexing and `Set.Icc`.
- The fraction field in degree zero has zero cone but nonzero cohomology. It is
  excluded by `hfinite`, confirming that finite generation was not discarded.
- ϖ=0 and a unit cannot generate the nonzero proper maximal ideal of a DVR.
  Neither a field nor the zero ring is silently included as a DVR. No separate
  completeness, characteristic, free-term, or torsion-free hypothesis was added.

Searches for an existing statement (2026-10-17):

- `msearch.py ... leanfinder` with query `vanishing range of a bounded complex
  with finitely generated cohomology over a DVR detected by the cone of
  multiplication by a uniformizer`: eight hits, on derived/projective/injective
  single-complex maps and cohomological bounds; no DVR detection theorem.
- `msearch.py ... loogle 'DerivedCategory, IsDiscreteValuationRing'`:
  successful query, zero hits.
- `msearch.py ... grep 'uniformizer|Nakayama|residueField|amplitude'
  Algebra/Homology`: successful search, zero hits.
- `msearch.py ... leansearch` with query `derived Nakayama cohomological
  vanishing detected by residue field reduction over a discrete valuation ring`:
  eight hits, including `IsLocalRing.span_eq_top_of_tmul_eq_basis`,
  `Submodule.le_of_le_smul_of_le_jacobson_bot`, module Nakayama, and DVR results;
  none states the complex-amplitude implication.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for DVR,
  uniformizer, amplitude, and Nakayama found ring-level Nakayama results and
  sheaf-level derived-completeness arguments, not this statement. The specific
  `derived Nakayama` candidate `Sheaf.Paper.ResidueLisseProjectiveModels` was
  opened: its theorem concerns partitions of affine weakly contractible schemes
  and projective models of derived-complete sheaves, a different assertion.
- `rg` for the exact node ID over upstream `WeilConjectures`: zero hits.
  Searches for the chosen declaration and module names over Mathlib, upstream,
  project Lean and `dag/lean_names_upstream.json` also gave zero hits.
- Read the Mathlib DVR, derived-category, linearity, cohomology-sequence,
  ModuleCat and finite-module interfaces directly to reuse their existing notions.

Validation: the prescribed `scompile.py Q110
lem-pod-dvr-complex-amplitude-mod-uniformizer <module>` compiled the file cleanly
both as a sandbox file and at its intended library module path, with no errors
or warnings. The delivery dry run is the final validation step; the independent
second reader will write the second-reading section and deliver.

## Second reading by Q110

I independently opened the DAG node, its sandbox copy, the complete Lean module,
both statement-dependency nodes and both additional proof-dependency nodes.
There is no repair note for this item, no statement_change, no new node, and no
dependency module in this delivery. The mathematical statement and Lean signature
need no change.

Object, hypothesis, and conclusion checklist, read against the node:

1. **R is a DVR.** `(R : Type u) [CommRing R] [IsDomain R]
   [IsDiscreteValuationRing R]` is exactly the recorded
   `def-sc-discrete-valuation-ring` notion. I read Basic.lean:55-100: the class
   extends local principal ideal rings and requires a nonzero maximal ideal.
   The domain instance is part of that notion, not an extra assumption. Pass.
2. **Uniformizer and residue field.** `(ϖ : R)` and
   `hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}` give precisely a generator
   of the maximal ideal. Basic.lean:93 explicitly equates this with irreducibility.
   The residue field is the quotient by this ideal; it need not be separately
   bound because the node itself specifies the cone as its derived-reduction
   model, and the conclusion asks only about cohomology vanishing. Pass.
3. **The category D(R) and arbitrary M.**
   `M : DerivedCategory (ModuleCat.{max u v} R)` uses the exact recorded
   `def-weil-abstract-derived-category` interface. I read Basic.lean:70-98 and
   :198-210: it localizes integer-indexed cochain complexes at quasi-isomorphisms,
   and its distinguished triangles are localized cone triangles.
   `[HasDerivedCategory.{w} ...]` chooses the morphism universe as the dependency
   prescribes; its standard construction exists. It is not a finiteness,
   completeness, or projectivity hypothesis. Pass.
4. **Cohomology modules.** Every occurrence of H^i is
   `(homologyFunctor (ModuleCat.{max u v} R) i).obj M` (or `.obj N`). I read
   HomologySequence.lean:34-41: `homologyFunctorFactors` identifies these with
   the cohomology of the representing cochain complex. ModuleCat has its ordinary
   module objects and abelian structure. Pass.
5. **Only finitely many nonzero cohomology modules.** `hbounded : Set.Finite
   {i : ℤ | ¬ IsZero (...obj M)}` expresses exactly finite cohomology support.
   This retains the node's boundedness hypothesis even though the degreewise
   Nakayama argument does not need it. Pass.
6. **Finite generation in every degree.** `hfinite : ∀ i : ℤ,
   Module.Finite R (...obj M)` is finite generation, not finite cardinality.
   I read Finiteness/Defs.lean:118-130, where it is finite generation of top.
   No finite-term model is assumed. Pass.
7. **Derived reduction, with the stipulated cone model.** The second object N,
   `ι : M ⟶ N`, `δ : N ⟶ M⟦(1 : ℤ)⟧`, and
   `hcone : Triangle.mk (ϖ • 𝟙 M) ι δ ∈ distTriang _` specify a cone of the
   actual scalar multiplication map on M. They do not substitute an arbitrary
   first arrow. I read DerivedCategory/Linear.lean:23-40: the scalar action is
   the canonical localized R-linear structure. A uniformizer is a nonzero divisor,
   so the two-term free resolution of R/(ϖ) gives precisely this cone model.
   Every such map has a cone, and its cone objects are isomorphic. Quantifying
   over cone triangles thus covers every representative of the node's reduction;
   forgetting the quotient-field action changes no cohomology-vanishing claim.
   The cohomological shift is +1, as required. Pass.
8. **Integer interval and its order.** `(a b : ℤ) (hab : a ≤ b)` retains both
   endpoints and the node's order assumption. Pass.
9. **Reduction vanishes outside that interval.** `hN : ∀ i : ℤ,
   i ∉ Set.Icc a b → IsZero (...obj N)` is exactly that premise for the closed
   interval, with no bound on the chosen representative's terms. Pass.
10. **Conclusion.** `∀ i : ℤ, i ∉ Set.Icc a b → IsZero (...obj M)` is exactly
    vanishing for M outside the same closed interval. The universal binders
    precede the reduction-vanishing hypothesis, and the conclusion applies to
    every degree outside that interval. No conclusion clause is missing. Pass.

Source and proof checks: I read Milne LEC PDF page 125, Theorem 19.2 and its
proof, including the quotient/torsion sequence and the final generator-modulo-l
argument. Milne's variety, separably closed field, flat adic sheaf, and
properness/characteristic alternatives concern his production of the exact
sequence and finite generation. This DAG node explicitly abstracts the subsequent
module argument and already assumes those algebraic inputs; they are not extra
hypotheses on the present DVR lemma. I also read Stacks algebra.tex:3605-3645,
lemma-NAK (2), and derived.tex:255-298 and :3595-3715. The latter assumes only
an abelian category for the cohomology functors and their long exact sequence.
The current blueprint prop-cohomological-finiteness proof, Step 4, and the
sk-lem-finite unit statement agree with this use of the bound.

The theorem docstring includes the source places, the exact blueprint id, and
both proof steps: the long exact sequence of the fixed scalar cone gives the
quotient/torsion short exact sequence; vanishing of its middle term kills
H^i(M)/ϖ H^i(M), and Nakayama kills the finite module H^i(M). I read the actual
signatures of `HomologySequence.δ`, `exact₁`, `exact₂`, `exact₃` at
HomologySequence.lean:152-184 and
`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` at Nakayama.lean:118-120.
They provide the node's proof dependencies without a private replacement.
All four dependency nodes are Mathlib leaves with usable interfaces.

Edge cases independently checked:

- The zero complex has empty cohomology support, and its cone is zero; the
  predicates allow it, including a=b=0. No nonempty support is required.
- R in degree zero reduces to κ in degree zero. An interval omitting zero
  violates precisely hN. A singleton interval containing zero is allowed.
- κ in degree zero, or R/(ϖ²) there, has reduction cohomology in degrees -1
  and 0. The +1 shift and arbitrary integer indexing retain this Tor term.
  Shifting gives the same check at arbitrary positive and negative endpoints.
- The fraction field in degree zero has zero reduction but nonzero cohomology;
  it is excluded exactly by hfinite. This tests the essential hypothesis.
- A zero ring, a field, a zero uniformizer and a unit uniformizer are excluded
  by the DVR/uniformizer notion itself, as the node requires. Equal and mixed
  characteristic DVRs are both covered; no characteristic or completeness
  condition occurs. Empty schemes/indexing families and a natural-number
  parameter n are not objects of this statement.
- Universes u, v, w are explicitly bound. Module carriers may be arbitrarily
  large via `max u v`; w is independent. This covers arbitrary ordinary
  R-modules (smaller carriers can be lifted), without an equality between
  ring, module, and localized-morphism universes. No variable is unbound.

Independent duplicate searches, with different phrasing from the worker:

- `msearch.py ... leanfinder` queried finite cohomology over a local principal
  ideal domain and detection by the scalar-multiplication cone. Eight hits
  were cochain/derived `isZero_of_isLE`, `isZero_of_isGE`, `isLE_iff`,
  `isGE_iff`, and single-complex morphism results. I opened TStructure.lean:
  these characterize existing bounds and do not detect them under reduction.
- `msearch.py ... loogle '"homology", "smul"'` succeeded with twelve hits:
  HomComplex cohomology scalar actions and ShortComplex homology-map linearity,
  not the present amplitude theorem.
- `msearch.py ... leansearch` queried zero cohomology of a maximal-ideal-generator
  cone and finite cohomology vanishing by Nakayama. Eight hits included module
  Nakayama, local-ring generator lifting, `exists_iso_single`, and
  `mappingCone.isZero_X_iff`. These are ingredients or termwise statements,
  not this statement.
- Independent `rg` searches over Mathlib/Algebra/Homology, upstream
  WeilConjectures, and project lean/Sheaf used `derived.?nakayama`,
  `uniformi[sz]er`, `Nakayama`, and residue/vanishing/amplitude combinations.
  I opened upstream Etale/Derived/ReductionConservative.lean: its two theorems
  concern invertibility and conservativity on derived-complete sheaves, not
  finite-cohomology DVR modules and degree bounds. Upstream IntegralCoefficient
  defines a complete integral coefficient category, and upstream Nakayama.lean
  supplies module and finite-ring-map lemmas. Project ResidueTorAmplitudeTest
  concerns sheaf Tor amplitude; ResidueLisseProjectiveModels concerns clopen
  models of complete sheaves. ResidueBottomDifferential and
  ResidueConnectiveProjectiveOpcycles assume finite projective complex terms
  and test residue fields at all primes; their conclusions differ. None is
  an exact existing declaration for this node.
- Exact searches for the node id and proposed declaration in upstream,
  project Lean and dag/lean_names_upstream.json had no hits. No new notion
  is needed: DVRs, modules, finite generation, derived categories, cohomology,
  scalar maps, and distinguished triangles all use existing Mathlib notions.

Mismatch and change record: no mathematical, dependency, universe, convention,
or statement-record mismatch was found. I preserved the module and node copy
verbatim, adding only this independent review to the report. The module has no
definitions, no hidden data, and one theorem with `sorry` as its whole proof.
All imports serve its statement or its recorded proof dependencies; every line
is within the 100-character limit and the signature contains no file-local
notation, instance, private declaration, or hidden `let`/`show` binder.

Second-reader validation: prescribed scompile.py passed at both the sandbox and
intended library paths (1.3 s and 1.4 s), with no error or warning. An independent
record check confirmed that only lean differs from the base node, lean.statement
equals the source signature verbatim, all Lean lines have at most 100 characters,
and the sole postponed theorem has exactly one sorry. The first wrapper invocation
used the repository cwd and could not find the sandbox-relative filename; rerunning
from the sandbox corrected that invocation without changing any source.
