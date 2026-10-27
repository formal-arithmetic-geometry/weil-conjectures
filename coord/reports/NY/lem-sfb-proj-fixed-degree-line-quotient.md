## Worker report

Stage 2 statement of `lem-sfb-proj-fixed-degree-line-quotient` in
`Sheaf.AlgebraicGeometry.ProjFixedDegreeLineQuotient`, declaration
`AlgebraicGeometry.Proj.fixedDegreeLine_quotient_classification`.
One theorem, with proof `by sorry`; all helper definitions have real data.
The natural-language statement and accepted split are unchanged.
The only additional statement dependency is the already landed
`def-sfb-veronese-graded-ring`, whose actual ring and grading are reused.
There are no new nodes and no dependency repairs.

The inherited BLOCKED ending concerned a stage-1 unchanged-node refusal. The
current queue assigns stage 2 and the item had no Lean record. The maintenance
handoff in brief-stage2 §0 explicitly directs continuing stage 2 in this case.
There was no preserved Lean implementation in this item's sandbox.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Any nonnegatively graded commutative unital ring A | `{A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedRing 𝒜]` in the section. Every additive subgroup is canonically an integer submodule; no extra algebra hypothesis is imposed. |
| P = Proj(A) | Existing `AlgebraicGeometry.Proj 𝒜`. |
| d ≥ 1 | `d : ℕ+`; its coercion is the degree. |
| U_d is the union of D_+(a), a in A_d | `fixedDegreeOpen 𝒜 d := ⨆ a : 𝒜 (d : ℕ), basicOpen 𝒜 a.val`. |
| O_P(j) and the canonical homogeneous sections | Existing `Proj.twist` and `Proj.unitToTwist`; `fixedDegreeCanonicalSection` applies the latter to 1 on the image open and the inverse of `restrictAppIso`. This is literally the restricted section b/1. |
| M_d = O_P(d) restricted to U_d | `fixedDegreeLine`; it uses `Modules.restrict` of this exact twist along the open immersion. |
| M_d is invertible | First conjunct `(fixedDegreeLine 𝒜 d).IsInvertible`. The following `∀ hM` binds evidence of this proved conjunct for the section-ring instance; it adds no mathematical hypothesis. |
| M_d tensor k identifies with O_P(kd) restricted to U_d, k ≥ 0 | Existential `θ : ∀ k : ℕ, (fixedDegreeLine 𝒜 d).tensorPow k ≅ fixedDegreeTwist 𝒜 d k`. |
| These are multiplication identifications, not arbitrary isomorphisms | `HEq (θ 1).hom (ρ_ M_d).hom` fixes degree one. For every homogeneous b, `(θ k).hom.app ⊤ (η_k(b)) = fixedDegreeCanonicalSection ... k b`. Together with multiplicativity and unitality of η this pins θ to multiplication: on D_+(a), the section a freely generates M_d; θ sends its kth tensor power to a^k. These sections locally freely generate, determining the maps. At k=0, the graded unit pins θ to the canonical O → O(0) comparison. |
| A^(d)_k = A_(kd) | `GradedAlgebra.veroneseGrade 𝒜 d k`; its elements are elements of the actual `veroneseSubring` whose original degree is k*d. Its inclusion identifies this component with A_(kd), since every homogeneous element in that degree is one of the closure generators. |
| Canonical graded unital map η^d | `η : FixedDegreeMap 𝒜 d M_d hM`, an abbreviation of the existing `veroneseGrade 𝒜 d →+*ᵍ sectionRingGrade M_d`; the preceding normalization specifies all its homogeneous components. |
| T any scheme | `∀ T : Scheme.{u}` with arbitrary universe u; no compactness assumption. |
| L an invertible module | `L : T.Modules`, `hL : L.IsInvertible`. |
| φ a graded unital ring map to Γ_*(T,L) | `φ : FixedDegreeMap 𝒜 d L hL`; its underlying map is a genuine `GradedRingHom`, so additivity, multiplication, the unit and gradedness are included. |
| Images of A_d generate L as a sheaf | `FixedDegreeGenerates ... φ`: the supremum of `generatingLocus` for all `fixedDegreeLinearSection ... φ a` is top. For an invertible module this is equivalent to sheaf generation, by the local-ring unit criterion. Degree-one tensor powers are identified with L using the right unitor. |
| There is a unique pair (g,α) | `∃! q : Σ g : T ⟶ U_d.toScheme, (tensorPullback g).obj M_d ≅ L, FixedDegreeCompatible ... q.1 q.2`. The dependent pair retains α; uniqueness is not merely uniqueness of g. |
| Compatibility for every k ≥ 0 and b in A_(kd) | `FixedDegreeCompatible` quantifies `k : ℕ` and `b : veroneseGrade 𝒜 d k`. It applies `tensorPullbackSection` to η_k(b), then `boundaryPullbackPowIso` and `boundaryTensorPowIso α k`, and equates the result to φ_k(b). |
| Equality on global sections | The HEq in compatibility only transports `g ⁻¹ᵁ ⊤ = ⊤`; no section, coefficient, map or module has been replaced. |
| Conversely pullback along any g has these properties | Last conjunct: for every T and g, the actual module `(tensorPullback g).obj M_d` is invertible, and there exists its graded section map φ with generation and compatibility, using `Iso.refl _` as the line comparison. The all-degree equation uniquely specifies this map as pullback of η. |
| For a in A_d set s = φ_1(a) | `a : veroneseGrade 𝒜 d 1`; `fixedDegreeLinearSection ... φ a` is exactly this s in L. |
| g inverse image D_+(a) = T_s | First conjunct of `FixedDegreeCharts`, using the composite of g with the open immersion into P and the existing `generatingLocus s`. |
| The chart map sends b/a^k to φ_k(b)/s tensor k | Second conjunct of `FixedDegreeCharts`: the image of the actual `HomogeneousLocalization.Away.mk 𝒜 a.property k b.val.val ...` under `awayToSection` and the scheme's `app` map, multiplied by the restriction of `(φ a.val ^ k) k`, equals the restriction of φ_k(b). Ring multiplication in `InvertibleSectionRing` makes this denominator precisely s's kth tensor power. |
| Division uses a free generator, only on T_s | The chart preimage is T_s by the first conjunct. On this open s and its tensor powers are free generators by the meaning of generatingLocus, so the scalar equality uniquely expresses division. It does not cancel a section outside T_s. |
| The selected pair has the chart properties | The theorem asserts `∀ g α, FixedDegreeCompatible ... g α → FixedDegreeCharts ... φ g`. Thus charts hold for the unique compatible pair. Uniqueness is asserted among all compatible pairs, without adding chart conditions to its predicate. |
| No generation assumption on A; no quasi-compactness on T | Neither hypothesis occurs. Coverage uses the unrestricted supremum over the whole homogeneous component, never a finite subfamily. |

The additional helpers are restrictions, abbreviations of existing types, evaluations,
and predicates expressing the clauses of this one node. They introduce no independent
notion requiring a new definition node. `FixedDegreeMap`'s `letI` is inside a definition
and only installs its explicit invertibility proof; there are no lets in theorem
statements, local notation, local instances, private definitions or auto-implicit variables.

### Dependency declarations used

- `def-pc-proj`: Mathlib `AlgebraicGeometry.Proj`, `Proj.basicOpen`,
  `Proj.awayToSection`, `Proj.basicOpenIsoSpec`, in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`. These are the recorded
  mathematical constructions; the older name `projIsoSpec` is not needed.
- `def-weil-pbc-proj-twisting-sheaf`: `Proj.twist`, in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`, and
  `Proj.unitToTwist`, in the sibling `.UnitToTwist` module. Their full signatures
  and docstrings were read. The actual twists are used, not an abstract replacement.
- `def-sc-invertible-module`: `Scheme.Modules.IsInvertible`, in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`; also its actual recursive
  `tensorPow` and `tensorPowAddIso`. Degree zero is the monoidal unit; degree one
  is L tensor the unit, so the explicit right unitor is essential.
- `def-sc-invertible-section-ring`: `InvertibleSectionRing`,
  `SectionRingComponent`, `sectionRingGrade`, `sectionRingGCommRing`, in
  `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`. The graded map targets
  this exact ring. `fixedDegreeImage` is evaluation of its kth direct-sum component.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, Mathlib Scheme.
- `def-pc-module-pullback`: `tensorPullback` from the upstream TensorPullback
  module and `tensorPullbackSection`, `tensorPullbackSectionAdjunction`, from
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`. The actual section
  1 tensor m and the normalized adjunction are retained.
- `def-sc-section-generating-locus`: `Scheme.Modules.generatingLocus`, in
  `WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus`.
- `def-pur-sheaf-tensor-product`: the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is publicly
  imported. Scheme modules use the existing monoidal tensor and `tmulSection`
  through TensorSection and InvertibleSectionRing; no second tensor is constructed.
- `def-nagata-homogeneous-localization-degree-zero`:
  `HomogeneousLocalization.Away`, `.Away.mk`, `.Away.mk_surjective`, Mathlib
  HomogeneousLocalization. The fraction numerator membership is only an index
  transport from k*d to k • (1*d).
- Added landed node `def-sfb-veronese-graded-ring`:
  `GradedAlgebra.veroneseSubring`, `veroneseGrade`, `veroneseGradedRing`, in
  `Sheaf.RingTheory.VeroneseGradedRing`. Its full construction and signature were
  read. Using the canonical ℤ-algebra action makes it available for every A.
- Existing canonical comparison helpers `boundaryPullbackPowIso` and
  `boundaryTensorPowIso`, from
  `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`.
  Their recursive definitions, including the canonical unit at zero, were read.
  The underlying pullback adjunction is normalized on 1 tensor m by
  `exists_tensorPullbackAdjunction`; it is not a free choice of an isomorphism.

The stated proof dependencies with recorded modules are imported nonpublicly:
TensorBilinearUniversal, GlueSheavesOfModules, ModulePullbackTensor,
RestrictionTensorComparison and ProjGradedModuleSheafExists. Mathlib proof
dependencies are covered by ProjectiveSpectrum.Basic (standard-open intersections),
GammaSpecAdjunction (affine Hom), Gluing (scheme morphisms), and
Topology.Sheaves.SheafCondition.Sites (extension from a basis), with the latter
three explicitly imported nonpublicly. The two trf frame lemmas have no Lean
record, mathlib_match or upstream audit declaration, so there is no module
to import for them. No proof dependency is removed. The docstring carries all eight steps of the accepted proof.

### Edge cases and source check

Read constructions.tex: Tag 01MS in full; the discussion of U_d, psi-d and
psi-phi-d; Tag 01N8 with its complete proof; and Tag 01N9. The source explicitly
says neither Proj nor U_d need be quasi-compact.

- Empty T: coverage is top = bottom, all section equalities are valid, and the
  unique map/line comparison on the empty scheme is included.
- A_d = 0, or A has only a degree-zero part: U_d is empty. A generating map on
  nonempty T cannot satisfy the coverage hypothesis; empty T remains included.
- For a polynomial generator of degree e not dividing d, U_d can be empty even
  when Proj is nonempty. The target is U_d, never silently all of Proj.
- Zero ring, zero homogeneous a and nilpotent homogeneous a: their standard opens
  are empty. No assumption of regularity, nonzero numerator or cancellation appears.
- k = 0: tensorPow is the unit, η and φ preserve 1, pullback comparison uses its
  unit isomorphism, and the fraction denominator is φ(a)^0 = 1.
- k = 1: the right unitor identifies L tensor the unit with L. It is included
  explicitly both in canonical normalization and in the generating sections.
- Arbitrary infinite covers and non-quasi-compact T: all suprema and quantifiers
  are unrestricted; no finite-type, degree-one generation or compactness assumption.
- Nonreduced graded rings and arbitrary degree-zero rings remain included.
- The accepted split already repairs the source's incorrect assertion that
  fixed-degree basic opens form a basis. The module's proof plan uses affine Hom
  uniqueness on their overlaps and an open cover, never that basis assertion.
  No new statement dispute or correction was found.

### Searches and reuse

Run through msearch.py for this group and item:

- LeanFinder: `Morphisms from a scheme to Proj of an arbitrary graded ring classify
  invertible sheaves generated by fixed degree homogeneous sections`: eight hits,
  including Proj.fromOfGlobalSections, toBasicOpenOfGlobalSections, projIsoSpec and
  awayToSection; none states line-valued fixed-degree classification.
- Loogle: `AlgebraicGeometry.Proj, GradedRingHom, DirectSum`: zero hits.
- Mathlib grep: `veronese|Veronese|fromSection|toProj` in AlgebraicGeometry:
  five unrelated elliptic-curve projective-model hits.
- LeanSearch: `Morphisms to Proj correspond to invertible sheaves with a graded
  ring homomorphism and generating sections in a fixed positive degree`: eight
  hits on Proj.fromOfGlobalSections and chart morphisms into ordinary Proj.
  Those maps start from ring-valued functions, not arbitrary invertible lines.

Local rg over WeilConjectures and Sheaf for Veronese, graded maps, maps to Proj,
line quotients and fixed-degree names found the existing VeroneseGradedRing,
InvertibleSectionRing, ProjCanonicalMapTwistComparison and
SchemeVeroneseQuotientData. The latter treats relative graded algebra data on
affine-base tests, not this standalone classification for an arbitrary ring.
ProjCanonicalMapTwistComparison assumes a specified map to Proj and a
quasi-compact source and only compares sufficiently divisible positive twists;
it is not this theorem. None of the new full declaration names already exists.
Searching the item id in upstream WeilConjectures found no statement; the
Sheaf occurrence is its downstream SchemeProjVeroneseQuotientFunctor proof
plan. Mathlib's basic Proj source and all used dependency declarations were read.
`tools/blueprint_refs.py search 'Veronese'` found no blueprint node match; the DAG
search found the landed ring-definition node, which is reused.

### Validation

The module was compiled through the prescribed scompile.py against the live
published library, both sandbox and library views. The first diagnostic was a
homogeneous-component coercion in the fraction constructor; adding an explicit
typed membership before the index simplification repaired it. The subsequent
compile was clean (sandbox 8.4 s, library 4.2 s), with the permitted postponed
proof only. Final delivery-tool validation follows below.

The dry run passed compilation and server preflight at `baf9b47c35c`. The final
source additionally spells out the Mathlib proof-dependency imports; the
delivery tool recompiles and checks this final version before pushing. The
previous long-line warning in the proof docstring was repaired by wrapping it.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
