## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGradedProjMorphism` states
`AlgebraicGeometry.Proj.exists_isFinite_surjective_of_finite_graded` with a single
`sorry` proof. It introduces no new definitions. The node statement is unchanged.
The prior Q75 ledger entry is the stage-1 split, not a Lean statement: the current
node has no `lean` record, and there is no maintenance repair note for this item.
No prior delivery or substantive file was present in this sandbox at resumption.

Clause-by-clause correspondence:

- Commutative nonnegatively graded rings C and A: `{C A : Type u}`,
  `[CommRing C] [CommRing A]`, the families `𝒞 : ℕ → AddSubgroup C` and
  `𝒜 : ℕ → AddSubgroup A`, and their `[GradedRing]` instances. Every ordinary
  nonnegative grading is a family of additive subgroups with this structure.
- The injective graded ring homomorphism is `iota : 𝒞 →+*ᵍ 𝒜` and
  `_hinj : Function.Injective iota`. Its second field is the degree-preservation
  condition, so `iota.2 hf` gives `iota f ∈ 𝒜 d` whenever `hf : f ∈ 𝒞 d`.
- C is finite type over C₀: `_hft : (algebraMap (𝒞 0) C).FiniteType`. The
  algebra map is the canonical inclusion of the degree-zero subring provided by
  `GradedRing`, not a freely chosen scalar action.
- A is finitely generated as a C-module through iota:
  `_hfinite : iota.toRingHom.Finite`. Mathlib's definition equips A with
  `iota.toRingHom.toAlgebra` and asserts `Module.Finite C A`, exactly the node's action.
- Defined on all of Proj A: `∃ r : Proj 𝒜 ⟶ Proj 𝒞`. This is a morphism whose
  source is the entire scheme, not a restricted open or a rational map. The following
  chart condition pins it to the canonical morphism of Stacks 01MY. As the node's
  step 1 shows, the source charts indexed by positive-degree elements of C cover
  Proj A under the given module-finiteness hypothesis. Thus this existential does
  not replace the canonical map with an arbitrary map.
- Finite and surjective: `IsFinite r ∧ Surjective r`.
- Every positive-degree homogeneous element: `∀ (d : ℕ) (hd : 0 < d)
  (f : C) (hf : f ∈ 𝒞 d)`.
- The inverse-image formula is the equality of scheme opens
  `r ⁻¹ᵁ Proj.basicOpen 𝒞 f = Proj.basicOpen 𝒜 (iota f)`.
- The affine chart map is the commuting equation
  `Proj.awayι 𝒜 (iota f) (iota.2 hf) hd ≫ r =
  Spec.map (CommRingCat.ofHom (Away.map iota f)) ≫ Proj.awayι 𝒞 f hf hd`.
  Here `awayι` is the canonical affine chart inclusion defined using
  `basicOpenIsoSpec`. Together with the inverse-image formula, this says exactly
  that the restriction to the whole chart is induced by the displayed ring map.
- The fraction formula is part of the existing `HomogeneousLocalization.Away.map`,
  whose full implementation and `Away.map_mk` were read. The latter sends
  `Away.mk 𝒞 hf m c hc` to `Away.mk 𝒜 (iota.2 hf) m (iota c) (iota.2 hc)`.
  `Away.mk` represents c/f^m, so this is precisely the formula in the node, with
  numerator degree m*d. No duplicate localization or chart map is defined.
- No equality of C₀ and A₀ is imposed. There are no conditions on characteristic,
  reducedness, degree-one generation, or nonemptiness.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`, in
  `Mathlib.RingTheory.FiniteType`, with its underlying `Algebra.FiniteType` definition.
- `def-weil-finitely-generated-module`: `Module.Finite`, in
  `Mathlib.RingTheory.Finiteness.Defs`, used through the actual definition of
  `RingHom.Finite` in the same module. This selects the action induced by iota.
- `def-pc-proj`: Mathlib `AlgebraicGeometry.Proj`, `Proj.basicOpen`,
  `Proj.basicOpenIsoSpec`, `Proj.awayι`, in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme` and `.Basic`. The dependency
  is a Mathlib notion; its closed upstream audit theorem about affine basic opens
  was also inspected. The statement uses the canonical Mathlib constructions.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`, in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` (available through the finite
  morphism import).
- `def-nagata-homogeneous-localization-degree-zero`:
  `HomogeneousLocalization.Away`, `.Away.map`, `.Away.map_mk`, in
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`.

The proof docstring carries all seven steps of the DAG proof and names its inputs.
The available proof inputs are Mathlib: standard-open intersection and the affine
criterion are in the public Proj/finite imports; gluing, integrality of finite
algebras, and integral injective lying-over have explicit non-public imports
`Mathlib.AlgebraicGeometry.Gluing`,
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, and
`Mathlib.RingTheory.Spectrum.Prime.Topology`.
`lem-per-finite-graded-module-dehomogenization` has no recorded Lean module yet;
there is consequently no such module to import. It is needed for the future proof,
not for stating this theorem, and is neither restated nor added to this delivery.

Edge cases checked before writing: a zero ring; rings concentrated in degree zero;
empty Proj; f = 0 and nilpotent homogeneous f; gradings generated in degrees other
than one; and finite extensions of degree-zero rings. In the concentrated-degree-zero
case module finiteness forces positive-degree elements of A to be nilpotent, so both
Proj schemes are empty. Nilpotent f gives zero localized rings and empty standard
opens, with the same `Away.map` and chart inclusions. No `Nontrivial`, positivity
beyond d > 0 for a chart, or equality C₀ = A₀ excludes these cases.

Searches made (all on 2026-10-19):

- `msearch.py leanfinder`: “An injective module finite homomorphism of nonnegatively
  graded commutative rings induces a finite surjective map on Proj with homogeneous
  localization chart maps”. Eight hits: Proj construction, chart maps and properness
  of the structure map to Spec C₀; none states this result.
- `msearch.py loogle`: `"Proj", "IsFinite"`. One unrelated measure-theory result.
- `msearch.py grep`: `IsFinite|Module.Finite|Finite.*map`, restricted to
  `AlgebraicGeometry/ProjectiveSpectrum`. No hits.
- `msearch.py leansearch`: “An injective finite graded ring extension induces a finite
  surjective morphism on projective spectra with standard open localization formula”.
  Eight hits describing Proj charts and their localizations; no matching theorem.
- `rg` of the upstream `WeilConjectures` tree for the node ID and the proposed name
  found no existing declaration. `rg` of project `lean/Sheaf` found only uses in
  `ProjectiveFiniteGroupQuotient`, not a statement of this result. Searches of Mathlib,
  project Lean, and `dag/lean_names_upstream.json` for the proposed theorem name and
  module name found no collision.
- The exact APIs in Mathlib `ProjectiveSpectrum.Functor` and
  `GradedAlgebra.HomogeneousLocalization` were read. `Proj.map` requires the stronger
  ideal inclusion A₊ ≤ image(C₊). Module-finiteness only forces a radical inclusion
  (for example C = k[x²] inside A = k[x]), so imposing that API's hypothesis would
  exclude valid cases. Instead, this statement characterizes the canonical morphism
  directly by the source's actual chart equations on the entire scheme.

Sources read: Stacks `constructions.tex`, lemma-morphism-proj (01MY), including its
chart characterization and uniqueness argument; `algebra.tex`,
lemma-dehomogenize-finite-type (07Z2), including its finite graded module clause.
No statement fault or STATEMENT-DISPUTED flag was found. No new nodes, dependency
repairs, or statement correction were necessary.

Validation: the module is checked using the prescribed `scompile.py` wrapper. The
initial unknown unqualified `map_mem` was corrected to the graded homomorphism's
membership-preservation field. The final compilation and delivery preflight are
required to be clean before push.

## Second reading by Q155

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
