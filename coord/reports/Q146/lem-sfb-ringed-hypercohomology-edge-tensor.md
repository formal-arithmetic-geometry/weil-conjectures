## Worker report

Delivered module: `Sheaf.CategoryTheory.RingedHypercohomologyEdgeTensor`.
Primary declaration: `SheafOfModules.RingedSiteCup.hypercohomologyEdge_tensor`.
The same node's introductory clauses are rendered by `HypercohomologyEdgeSpec`,
`hypercohomologyEdge_existsUnique`, and `hypercohomologyEdge`. Both theorems have
`sorry` proofs. The definitions contain real predicate/choice data: the chosen
natural transformation is uniquely determined by its cocycle normalization,
not selected from an uncharacterized existence assertion.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-sheafification-cohomology` (Tag 0BKV, lines 4349 onward) and
`lemma-cup-compatible-with-naive` (Tag 0FPK, lines 8244 onward), including their
proofs. The first identifies the cohomology sheaf by the cycles/boundaries
quotient on a K-injective model; the second identifies derived cup with the
signed total-complex tensor of sections. The module docstrings contain the
node's five-step proof, including the chosen-cocycle K-flat factorization and
the shifted-free-unit normalization needed when global sections are not K-flat.

Hypothesis and clause correspondence:

- A ringed site small in a common coefficient universe is the existing
  `X : RingedTensorCorner.{u,w}`: `X.site : Type u`, `Category.{u} X.site`,
  `X.topology`, `X.ring : Sheaf X.topology CommRingCat.{u}`, and its chosen
  `HasDerivedCategory.{w}`. This is the common small-site presentation used by
  the recorded cup-product dependency, rather than an extra restriction on K,L.
- The coefficient sheaf is commutative by `CommRingCat`. Its module sheaves
  are `X.mateModules`, transparently the recorded `ringedSiteModules` and hence
  Mathlib's `SheafOfModules`. No category or tensor has been copied.
- The unbounded derived category is `X.mateDerived`; its cohomology sheaves
  are `cohomology X n`, the recorded `DerivedCategory.homologyFunctor`.
- `A = Γ(C,O)` is the dependency's `scalars X`, the ring of compatible families
  `RingCat.sectionsSubring`, with its actual pointwise commutative ring structure.
- `derivedGlobalSections X` is the dependency's A-module-valued unbounded
  K-injective `rightDerivedFunctor` of `globalSections X = Hom_O(O,-)`.
  Forgetting A recovers the additive derived sections used by the recorded
  zeroth-hypercohomology definition. The dependency already supplies the
  canonical comparison (`globalUnderlyingSections`, `globalAbelianUnit`,
  `globalAbelianUnit_isRightDerived`); this delivery introduces no second RΓ.
- The edge for every K and integer n is `hypercohomologyEdge X n`, a natural
  transformation `RΓ ⋙ H^n ⟶ H^n ⋙ Γ`. Its natural-transformation type expresses
  naturality for every derived morphism, not just maps of complexes.
- Its exact normalization, and hence representative independence, are stated
  by `hypercohomologyEdge_existsUnique`. `HypercohomologyEdgeSpec` quantifies
  over every K-injective complex I. The element z is a cycle in ΓI and s is the
  corresponding global section of the cycle sheaf; their equality after the
  two cycle inclusions identifies the same compatible family. Global sections
  preserves kernels, so every z has exactly one such s. The left side transports
  its homology class through `homologyFunctorFactors.inv` and the canonical
  derived unit β_I. The right side sends s through `I.homologyπ n` and the
  canonical representative cohomology isomorphism. Thus the edge sends the
  original global cocycle to its sheaf class. The uniqueness clause precludes
  an arbitrary edge, and naturality transports this normalization to every
  isomorphic presentation of K.
- Derived tensor and its flat K-flat representative comparison are the
  recorded `X.tensor` and `b : RingedTensorModel X`; b specifies the chosen
  representative presentation, not flatness of K or L. Global cup is exactly
  `global X b K L`. The scalar κ is `scalarPairing`, and the sheaf κ is
  `cohomologyPairing`. These are the recorded dependency's constructions.
- The arbitrary objects are `K L : X.mateDerived`; the nonnegative integers
  a,b in the node are `a d : ℕ` (the letter b names the tensor model in Lean).
  Their casts to ℤ are explicit. The inputs x,y are elements of exactly
  `H^a(RΓK)` and `H^d(RΓL)`.
- On the left, `TensorProduct.tmul (scalars X) x y` is mapped by scalar κ,
  then by `(scalarCohomology X (a+d)).map (global X b K L)`, then by the
  edge component at `X.tensor.obj (K,L)`. This is the displayed left side.
- On the right, the two edge values are sections, encoded as O-linear maps
  O to the respective cohomology sheaves. Their tensor, preceded by
  `(λ_ O).inv : O ⟶ O ⊗ O`, is the canonical section of the sheaf tensor
  obtained from the tensor of global sections. Composing with
  `cohomologyPairing X b K L a d` is Γ(κ) applied to that section. Thus the
  displayed formula includes exactly the required global-to-sheaf tensor map.
- There is no terminal-object binder, boundedness predicate, flatness predicate
  on K or L, or quasi-coherence assumption. The edge exists in every integer
  degree even though the tensor equality is requested in nonnegative degrees.

Recorded dependencies read and used (some are public transitive imports of the
cup-product module):

- `def-weil-size-convention`: metatheoretic convention, implemented by explicit
  `universe u w` and the corner's small-site/module/localization universe data;
  there is intentionally no Lean object for this convention.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: site convention; the
  corner carries the associated Grothendieck topology used by all sheaves.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: exact Mathlib module-sheaf abbreviation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`: actual unbounded localization.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`: cohomology and
  its representative comparison, used in the edge normalization.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`,
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`: recorded additive
  H0 RΓ construction. The module-valued enhancement and the canonical
  forgetful comparison are already provided by the cup-product dependency.
- `Sheaf.CategoryTheory.RingedSiteModuleCupProduct`,
  `SheafOfModules.RingedSiteCup.global`, `scalarPairing`, `scalarCohomology`;
  its public imports expose `cohomologyPairing`, `representativeCohomology`,
  `derivedGlobalSections`, `globalSections`, `globalDerivedUnit`, `scalars`.

Already stated proof dependencies are imported: the recorded independent-size
K-injective resolution theorem, Mathlib's `Qh_map_bijective` and its bounded-below
variant, independent-coefficient K-flat/tensor/descent interfaces (through the
public cup imports), `CochainComplex.exists_kFlat_map_factorization`, and
`AlgebraicGeometry.Scheme.Modules.exists_cupShiftedUnitTensor`.
`lem-sfb-ringed-derived-naive-cup-comparison` currently has neither a Lean record
nor a Mathlib match, so there is no module to import for that proof dependency;
it is not needed to type this stage-2 statement and its use remains in the
proof docstring. No statement dependency is missing or repaired.

Edge cases checked before writing: the empty site (compatible families and
Hom(O,-) still make sense), the zero coefficient ring, zero derived objects and
zero inputs, a=d=0, and negative n for the edge. None requires a final object.
The proof only chooses flat K-flat representatives, not flat input objects;
ΓP need not be K-flat, hence the explicit shifted-unit argument in the docstring.
The general edge is not claimed to be an isomorphism. No added connectivity or
spectral-sequence convergence hypothesis is needed for this cycle-to-class map.

Searches executed:

- `msearch.py ... leanfinder "hypercohomology edge to sections of cohomology sheaves compatible with tensor cup product"`:
  8 results (Mayer-Vietoris short-complex maps, hypercover gluing, Hom-complex
  cohomology projection/data); none states this unbounded tensor compatibility.
- `msearch.py ... loogle "CategoryTheory.Sheaf, HomologicalComplex.homology"`:
  successful response, 0 hits.
- `msearch.py ... grep "edgeMap|edge_map|hypercohomology|cupProduct" CategoryTheory/Sites`:
  successful response, 0 hits. All three searches are logged in `searches.jsonl`.
- `rg` for `hypercohomology`, edge names, and homology-comparison names in
  `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib homology files: found the
  bounded-below `HypercohomologyLeftEdge` family and affine pushforward edges.
  Those do not give this map for arbitrary unbounded K and arbitrary small
  ringed sites, nor its tensor equality. `grep -rn` for this exact blueprint id
  in `lean/WeilConjectures` returned no match. The cup-product dependency was
  read in full and reused, including its sheaf and scalar normalizations.

Validation: `scompile.py Q146 lem-sfb-ringed-hypercohomology-edge-tensor` compiled
both the sandbox and library presentations cleanly (5.7 seconds each); no errors
or unexpected warnings. The node copy changes only `lean`. There are no new
nodes, no dependency repairs, and no statement correction or disputed statement.

## Second reading by Q146

Final worker rereading, with the node, source and delivered module open; the
independent maintainer review follows delivery as specified by the dispatch brief.
The normalization includes both canonical homology identifications and β_I,
so it does not silently identify H(ΓI) with H(RΓQI) by definitional equality.
The chosen edge is a natural transformation, not a family with an omitted
naturality clause. Its normalization ranges over all K-injective representatives,
not only the fixed resolution selected by a functor. The actual tensor equation
uses the dependency's global cup and both recorded κ maps; its right side uses
the tensor of unit-originating section maps, so it includes the map into global
sections of the sheaf tensor. Rechecked all degree casts and the section/module
categories against the compiled signature. No mismatch was found and no source
statement was changed. The two postponed theorems are precisely the node's
edge-existence/naturality clause and its tensor-equality clause, rather than
additional untracked lemmas.
