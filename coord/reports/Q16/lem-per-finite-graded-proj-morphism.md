## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGradedProjMorphism` states
`AlgebraicGeometry.Proj.exists_isFinite_surjective_of_finite_graded`, with one
`sorry` proof and no new definitions. Only the item's `lean` field changes.
The formerly recorded module was deleted as dead code; `lean_removed` records
this history, and the declaration is absent from both current source libraries.
There is no released repair note for this item.

Clause-by-clause correspondence:

- The commutative nonnegative graded rings are `C`, `A`, `[CommRing C]`,
  `[CommRing A]`, `𝒞 : ℕ → σ`, `𝒜 : ℕ → τ`, and their `GradedRing` instances.
  Set-like component types with `AddSubgroupClass` are Mathlib's general
  internal-grading interface, with no degree-one generation restriction.
- The injective degree-preserving ring map is `ι : 𝒞 →+*ᵍ 𝒜` and
  `hι : Function.Injective ι`. `GradedRingHom.map_mem` means exactly
  `ι(C_n) ⊆ A_n`.
- Finite type over the canonical degree-zero subring is
  `hC : (algebraMap (𝒞 0) C).FiniteType`. This uses the recorded
  `RingHom.FiniteType`, with Mathlib's canonical grade-zero algebra structure.
- Finitely generated as a C-module through ι is `hA : ι.toRingHom.Finite`.
  In `Mathlib.RingTheory.Finiteness.Defs:170` this is defined as `Module.Finite C A`
  for `ι.toRingHom.toAlgebra`. Thus it uses precisely the dependency's
  `Module.Finite`, with the action fixed to ι, and introduces no independent
  algebra structure or scalar-compatibility assumption.
- Defined on the whole source is `∃ r : Proj 𝒜 ⟶ Proj 𝒞`: the domain is the
  entire source scheme. This is the canonical map, specified by the chart
  equations below; Tag 01MY explains that these equations uniquely determine it.
  It is not an arbitrary unconstrained morphism.
- Finite and surjective are `IsFinite r ∧ Surjective r`.
- For every positive homogeneous f, binders `d`, `f`, `hf : f ∈ 𝒞 d`,
  `hd : 0 < d` precede
  `r ⁻¹ᵁ Proj.basicOpen 𝒞 f = Proj.basicOpen 𝒜 (ι f)`.
- The affine chart formula is the commuting square
  `Proj.awayι 𝒜 (ι f) (ι.map_mem hf) hd ≫ r =
  Spec.map (CommRingCat.ofHom (Away.map ι f)) ≫ Proj.awayι 𝒞 f hf hd`.
  `awayι` is the inverse of `basicOpenIsoSpec` followed by the open inclusion;
  thus this states exactly the restriction on the entire inverse image.
  `Away.map_mk` in HomogeneousLocalization.lean:730 sends
  `Away.mk 𝒞 hf m c hc` to `Away.mk 𝒜 (ι.map_mem hf) m (ι c) (ι.map_mem hc)`:
  exactly c/f^m ↦ ι(c)/ι(f)^m. `Away` is the recorded degree-zero homogeneous
  localization; no denominator regularity or nonzero condition is imposed.
- There is no equality or identification between `𝒞 0` and `𝒜 0`, no
  Noetherianity, field, nontriviality, standard grading or extra finiteness
  hypothesis. A common arbitrary universe `u` puts the two schemes in the same
  category; all component types and variables are explicitly bound.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (line 217), and the
  canonical inclusion algebra on `𝒞 0` from graded algebra basic definitions.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (117) and its ring-map
  formulation `RingHom.Finite` (170).
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`: `AlgebraicGeometry.Proj`,
  `AlgebraicGeometry.projIsoSpec`; `ProjectiveSpectrum.Topology`:
  `ProjectiveSpectrum.basicOpen`. Their scheme-facing interfaces
  `Proj.basicOpen`, `Proj.basicOpenIsoSpec`, `Proj.awayι` are imported from
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`.
- `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`:
  `HomogeneousLocalization.Away`, `Away.mk`, `Away.map`, `Away.map_mk`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.Surjective`.

The proof docstring follows all seven DAG steps, including the degree bound,
chart injectivity, overlap agreement, gluing, preimage calculation, finite module
dehomogenization, and integral lying-over. Proof-only Mathlib imports provide
`Scheme.Cover.glueMorphisms`, target locality of `IsFinite`,
`RingHom.Finite.to_isIntegral`, and `RingHom.IsIntegral.comap_surjective`.
The proof dependency `lem-per-finite-graded-module-dehomogenization` currently has
no Lean record or Mathlib match, so there is no module to import for it. It is
only a proof dependency: no missing notion is required to state this item.

Source checked: Stacks `constructions.tex`, lemma-morphism-proj (01MY),
lines 2053–2135, especially condition (2) and its uniqueness paragraph;
`algebra.tex`, lemma-dehomogenize-finite-type (07Z2), lines 13686–13727.
The statement is the agent formulation recorded in the node, combining 01MY
with the additional graded finite-extension argument; no correction is needed.

Edge cases checked mathematically against the signature:

- Zero rings and empty Proj are allowed: no `Nontrivial`, nonempty source or
  nonempty target assumption; the empty morphism is finite and surjective.
- Nilpotent f, including zero, gives empty standard opens and zero localization
  rings; all binders and the chart formula still apply.
- A grading concentrated in degree zero gives empty Proj. The finite graded
  extension has no surviving positive homogeneous element by the degree-bound
  argument, so surjectivity remains consistent.
- d=0 is excluded only from standard affine chart assertions, as in the node;
  m=0 fractions are included by `Away.map`.
- The example C=k[t] with t of degree two and A=k[x] with x of degree one,
  t↦x², satisfies the assumptions, but `(x)` is not contained in `(x²)`.
  Hence Mathlib's `Proj.map` hypothesis is too strong and is not added.
- Unequal degree-zero rings, e.g. a finite injective extension R⊂S and
  R[t]⊂S[t], are allowed; their Proj map reduces to Spec S→Spec R.

Searches actually run with `msearch.py Q16 lem-per-finite-graded-proj-morphism`:

- `leanfinder "finite graded ring Proj morphism"`: 8 hits, including Proj
  properness over the degree-zero ring and `Proj.fromOfGlobalSections`; none is
  the finite surjective extension theorem.
- `loogle "Projective Spectrum GradedRing"`: unavailable query identifiers
  (`Unknown identifier Projective`), not treated as a negative match.
- `grep "graded.*proj|Proj.*graded" Mathlib`: no hits.
- `leansearch "finite injective graded ring homomorphism induces finite
  surjective Proj morphism with standard affine localization maps"`: 8 hits,
  including `Proj.awayι_toSpecZero`, `projIsoSpec`, and chart maps, no exact match.
- `loogle '"Proj", "IsFinite"'`: only the unrelated finite-measure result.
- `grep 'IsFinite|Module.Finite|[Ss]urjective' AlgebraicGeometry/ProjectiveSpectrum`:
  15 hits, chart surjectivity and localization constructions, no exact theorem.
- Direct `rg` searches of `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for finite graded Proj and the proposed
  declaration name found projectivity and blowup functoriality, no matching
  statement. Searching the item id in `lean/WeilConjectures` found nothing.
- Read the full signature and implementation of `Proj.map` and `Away.map`:
  the former requires actual irrelevant-ideal inclusion, not just radical
  inclusion, so cannot represent the node with the stated hypotheses.

Validation: final module compiled by the prescribed `scompile.py` on the live
server, separately as sandbox and library module, with no errors or unexpected
warnings. No statement dispute, new definition node, or dependency repair.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
