## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralityPrimeNeighbourhood` states
`AlgebraicGeometry.exists_isIntegral_localizationAway_of_isIntegral_atPrime`.
Its only proof is `sorry`, as required for stage 2. It introduces no definitions.
The node is unchanged except for `lean`; no new nodes, dependency repairs, or
statement correction are needed. No statement is disputed.

Hypothesis and conclusion correspondence, reading the node and the module together:

- A commutative Noetherian ring is `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`. This uses the recorded Noetherian-ring definition,
  which says every ideal is finitely generated.
- The prime ideal is `(p : Ideal R) [p.IsPrime]`.
- The supplied scheme and its morphism to the affine spectrum are
  `(X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))`.
- Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the
  conjunction recorded in `def-weil-finite-type-morphism`. There is no
  separation hypothesis.
- The specified prime base change is literally `pullback f (Spec.map
  (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))))`.
  This uses localization at the complement of `p`, rather than the residue field.
  The two pullback arrows have the same target `Spec (CommRingCat.of R)`.
- Its integrality is the hypothesis `(h : IsIntegral (...))`. Mathlib's
  `IsIntegral` includes nonemptiness and agrees with the source's nonempty
  affine-domain definition, by reducedness and irreducibility.
- The conclusion `∃ a : R, a ∉ p ∧ ...` supplies exactly one ring element
  outside the given ideal.
- The remaining conjunct is `IsIntegral (pullback f (Spec.map
  (CommRingCat.ofHom (algebraMap R (Localization.Away a)))))`, exactly
  integrality of `X ×[Spec R] Spec R[1/a]` with its canonical structure map.
- No excellence, flatness, domain, or separatedness structure is assumed.
  The only universe is explicitly declared `u`; every object/variable is bound,
  and `set_option autoImplicit false` prevents implicit variable creation.
  The usual common-universe scheme category is used, as in the recorded
  affine-chart base-change interface. There is no restriction on test objects.

Dependency declarations, with full source signatures and available docstrings read:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme` (publicly available through the geometry imports).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; existence for
  schemes comes from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-ring-localization-away`: `Localization.Away`,
  `Mathlib.GroupTheory.MonoidLocalization.Away`; the public import
  `Mathlib.RingTheory.Localization.Away.Basic` supplies its ring/algebra instances.

Statement dependencies are public imports. Available proof dependencies are
plain imports: `Algebra.FiniteType.isNoetherianRing` from
`Mathlib.RingTheory.FiniteType`; `LocalizedModule` and its fraction relation from
`Mathlib.Algebra.Module.LocalizedModule.Basic`; `irreducibleComponents` and
`IsIrreducible` from `Mathlib.Topology.Irreducible`; and
`AlgebraicGeometry.exists_affineChart_baseChangeIso` from
`WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso`.
`AlgebraicGeometry.irreducibleSpace_of_isIntegral` is already publicly available
from `Mathlib.AlgebraicGeometry.Properties`. The remaining proof dependency
`lem-per-integral-affine-cover-criterion` has no Lean record or Mathlib match at
preparation time; its import cannot yet be added. It is named in the proof
docstring for the maintainer's later proof-import update. It supplies no notion
needed to state this item.

The module docstring identifies the source as an agent-formulated consequence,
not a quotation of Tag 01ON. The theorem docstring carries all six DAG proof
steps: finite affine charts and their base changes, explicit fraction/tensor
identifications, denominator annihilation of finitely generated kernels,
empty-chart removal and domain subrings, pairwise intersection witnesses, and
the integral affine-cover criterion. I read Stacks `properties.tex`, the
integral/reduced/irreducible affine-cover criteria (Tags 01OL, 01OM, 01ON), and
the current blueprint unit `sk-p-dl-a1-perverse` and its ancestor lemma. This
auxiliary statement is not the unit's own statement.

Edge cases checked mathematically before writing:

- If `X` is empty then its prime base change is empty, hence not integral;
  the theorem does not assert an integral empty scheme.
- The zero ring has no prime ideal, so `[p.IsPrime]` excludes that inconsistent
  input; no nonzero or domain hypothesis on a general `R` was added.
- Over a field, `p = 0` and `a = 1` works; prime and away localizations preserve
  the original model up to their canonical isomorphisms.
- For `R = ℤ`, `X = Spec (ℤ[x]/(2x))`, `p = 0`, the generic localization is
  integral while `X` is not; `a = 2` removes the torsion. Thus the statement
  genuinely needs a principal shrinking and does not assume `X` integral.
- For `X = Spec ℤ ⊔ Spec 𝔽₂` over `ℤ` at `p = 0`, `a = 2` discards the
  chart whose prime base change is empty, as required by proof step 4.
- A product base `R = k × k` has prime localizations which are fields; a
  suitable idempotent outside `p` isolates that component. The statement
  permits such a non-domain base.
- In the proof's finite annihilator product, no kernel generators means the
  product is `1`, which lies outside every prime. Nonempty charts need not
  have affine intersections, and no separatedness was used.

Searches for an existing exact statement (all run for Q127 and this item):

- `msearch.py ... leanfinder "A finite type scheme over a Noetherian ring
  integral after localization at a prime is integral on some principal open
  neighbourhood"`: OK, eight hits, including integral open subschemes,
  `affine_isIntegral_iff`, and `isIntegral_of_isAffine_of_isDomain`; none states
  spreading from prime localization to a principal localization.
- `msearch.py ... loogle "AlgebraicGeometry.IsIntegral, Localization.AtPrime"`:
  OK, zero hits.
- `msearch.py ... grep
  "IsIntegral.*[Ll]ocal|[Ll]ocal.*IsIntegral|integral.*neighb|integral.*spread"
  AlgebraicGeometry`: OK, 21 hits. Geometrically integral base changes and
  integral ring/scheme morphisms do not state the requested scheme-integrality
  spreading result.
- `msearch.py ... leansearch "A finite type scheme over a Noetherian ring
  integral after prime localization becomes integral after a principal
  localization"`: OK, eight hits, mostly integral morphisms/ring elements,
  localization finite type and structure-sheaf localizations; no exact match.
- `rg -n` over `lean/WeilConjectures` and `lean/Sheaf` with
  `integral.*[Nn]eighb|integral.*[Ss]pread|IsIntegral.*[Ll]ocal|
  lem-per-integrality-prime-neighbourhood`: related integral affine
  neighbourhoods, normal local rings and geometric fibres, no exact statement.
- `grep -rn "lem-per-integrality-prime-neighbourhood" lean/WeilConjectures`:
  no hits. A final exact-name/concept search for
  `integrality_prime_neighbourhood|isIntegral.*prime.*neigh|
  exists_isIntegral.*local` across Mathlib, upstream and Sheaf also found no hits.

Validation: the prescribed `scompile.py` checked the sandbox file and the
proper library module separately against the published server build; both
passed in 1.8 seconds, without errors or unexpected warnings. The delivery
preflight and compile are run by `deliver2.py` after this report is written.

## Second reading by Q127

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
