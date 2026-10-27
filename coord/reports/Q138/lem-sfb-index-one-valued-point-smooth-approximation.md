## Worker report

The module `Sheaf.AlgebraicGeometry.IndexOneValuedPointSmoothApproximation` states
`AlgebraicGeometry.exists_smooth_affine_factorization_of_index_one`, with its proof
entirely `sorry`. No definitions, extra nodes, dependency repairs, statement corrections,
or additional hypotheses are introduced. The item JSON changes only in `lean`.

Source checked: BLR, *Néron Models*, §3.6 Definition 1 and Proposition 4, printed
pp.78–79 (PDF pp.84–85), using the primary scan linked in the node:
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
Definition 1 includes both the common uniformizer and separable residue extension.
The text distinguishes residue separability from separability of the fraction fields;
Proposition 4 does not require excellence. The three-step proof recorded in the node
is carried into the theorem docstring: scaled generators, finite induction on the
strictly decreasing differential torsion defect, and final smooth principal localization.
The latest blueprint's direct-images proof was also read; this is an inherited
prerequisite rather than the unit's own statement.

Clause-by-clause translation:

- The rings `R A : Type u`, with `[CommRing]`, `[IsDomain]`, and
  `[IsDiscreteValuationRing]` for each, are exactly the two DVRs. In particular neither
  is a field. `[Algebra R A]` supplies the given homomorphism, `hRA` its injectivity,
  and `[IsLocalHom (algebraMap R A)]` its locality.
- `K` and `L` have `[Field]`, the respective ring algebras, and `[IsFractionRing]`.
  The canonical induced inclusion of fraction fields is the existing
  `IsFractionRing.map (K := K) (L := L) hRA`, not an arbitrary field map.
  This avoids requesting unrelated `R`- or `K`-algebra structures on `L`.
- `hindex` is the equality of the extended maximal ideal
  `(IsLocalRing.maximalIdeal R).map (algebraMap R A)` with
  `IsLocalRing.maximalIdeal A`.
- `hsep : Algebra.IsSeparableExtension (IsLocalRing.ResidueField R)
  (IsLocalRing.ResidueField A)` is exactly the recorded notion, including
  transcendental separability. Mathlib's canonical residue-field algebra is derived
  from the local algebra map, so no independently chosen residue embedding occurs.
- `W : Scheme.{u}` and its structure map `q : W ⟶ Spec (.of K)` give the `K`-scheme.
  `[Smooth q]` gives smoothness; `[LocallyOfFiniteType q] [QuasiCompact q]` give the
  node's finite type. No separatedness is required.
- `w : Spec (.of L) ⟶ W` together with `hw` says precisely that `w` is over `K` for
  the canonical inclusion `K → L`.
- The witnesses `U` and `f : U ⟶ Spec (.of R)` give the `R`-scheme.
  `IsAffine U ∧ Smooth f ∧ LocallyOfFiniteType f ∧ QuasiCompact f` is exactly
  affine, smooth and finite type.
- The witness `a : Spec (.of A) ⟶ U`, with
  `a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A))`, is the required
  `R`-morphism.
- `pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))` is exactly `U_K`.
  The witness `h` has that domain and codomain `W`; its equation
  `h ≫ q = pullback.snd ...` is exactly that it is a `K`-morphism.
- `aK` has domain `Spec L` and codomain `U_K`. Its first projection is
  `Spec (A → L) ≫ a` and its second projection is the canonical `Spec L → Spec K`.
  These are the universal-property characterization of the generic restriction of
  `a`, and uniquely determine `aK` by pullback hom-extensionality. Thus existential
  quantification of `aK` introduces no arbitrary map or stronger assumption. Under
  the index-one hypothesis `A ⊗[R] K = A[1/π] ≅ L`, so this is the usual base-changed
  point with its domain canonically identified as `Spec L`.
- The final equation `aK ≫ h = w` is the requested `h ∘ a_K = w`.
- There are no completeness, excellence, or `L/K` separability assumptions. All
  variables and the universe `u` are explicitly bound, with no auto-bound implicits.
  The common ambient universe is Mathlib's scheme-category convention; taking a
  universe containing the given rings, fraction fields, and scheme allows arbitrary
  input sizes and does not restrict a quantifier over test objects.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`;
  its domain/local PID/nonfield definition was read, including the uniformizer lemma.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its documented reuse of
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd` for scheme base
  change. The node's primary `moduleBaseChange` declaration concerns modules and is
  not misused for scheme base change. The recorded module and full docstring were read.
- `WeilConjectures.FieldTheory.SeparableExtension`: `Algebra.IsSeparableExtension`,
  and its constituent `Algebra.IsSeparablyGenerated`, with their full definitions.
- Mathlib's existing `IsFractionRing.map` and the canonical local residue-field
  algebra from `Mathlib.RingTheory.LocalRing.ResidueField.Basic` supply canonical maps.
- Proof-only imports cover `Localization.Away` and `RingHom.FiniteType`, with
  `AlgebraicGeometry.pullbackSpecIso` available from Mathlib's pullbacks module.
  The two differential-defect proof dependencies currently have no Lean attachment
  or Mathlib match, so they have no module to import; they are named in the proof
  docstring. They are proof prerequisites, not missing statement notions.

Edge cases checked mathematically before writing:

- For `A = R`, `L = K`, `W = Spec K`, and `w` the identity, use `U = Spec R` and
  the identity integral point. Both projection equations and the factorization agree.
- For empty `W` there is no `Spec L`-point because `L` is a field; the statement
  quantifies an actual point `w` and therefore has no spurious empty-target obligation.
- The zero ring is excluded exactly by the DVR/domain assumptions; dimension zero
  generic schemes and defect zero are allowed. No relative-dimension bound is imposed.
- A transcendental separable residue extension is allowed by `IsSeparableExtension`;
  the stronger algebraic-only `Algebra.IsSeparable` was deliberately not substituted.
- A nonexcellent DVR and a completion with inseparable fraction-field extension
  remain permitted, as in the BLR discussion. No henselian assumption is imposed.
- A nonseparated smooth finite-type `W` is allowed; the construction only needs one
  affine neighbourhood of the point. No conclusion forces a generic isomorphism onto W.

Searches (all on 2026-10-24):

- `msearch.py ... leanfinder`: “A valued point of a smooth finite type scheme over a
  DVR fraction field extends through a smooth affine model for a ramification index
  one extension with separable residue fields”. Eight hits, including
  `ValuativeCommSq.i₁`, `WeierstrassCurve.IsGoodReduction`, and residue-unramified
  results. None asserts this smooth-model factorization.
- `msearch.py ... loogle`: `"IsDiscreteValuationRing", "Smooth"`. Zero hits.
- `msearch.py ... grep`: `smooth.*approximation|dilatation|smoothening|Neron`.
  Zero Mathlib hits.
- `msearch.py ... leansearch`: “For an index one local injective map of discrete
  valuation rings with separable residue extension any valued point on a smooth
  generic fibre factors through a smooth affine model”. Eight hits about valuation
  rings, smooth morphisms and separable algebraic residue extensions; no match.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `smooth.*approximation|dilatation|smoothening|Neron` and for the intended declaration
  found only unrelated noetherian/Artin/smooth approximation statements and no name
  conflict. `grep -rn` for the item id in `lean/WeilConjectures` found no declaration;
  the upstream-name index has no occurrence of the intended name.

No statement fault or dispute was found. The only postponed declaration is the
item's own theorem. `scompile.py` checked the actual module against the live published
library, with no errors or warnings. All delivery compilation uses that wrapper.

## Second reading by Q138

A separate sequential rereading compared the complete node with the final theorem,
its source interfaces, and its proof docstring. No second agent was started, as the
worker's explicit brief prohibits that; the maintainer supplies the independent review.

The rereading checked both DVR instances, injectivity and locality, both fraction-ring
structures, the extended ideal equality, and separability through the canonical residue
map. It checked smoothness and BOTH finite-type conditions on `q` and `f`; affineness is
required only of the output. It checked `hw`, the equation making `a` an `R`-map,
the equation making `h` a `K`-map, both projections uniquely fixing `aK`, and the final
factorization in categorical composition order. It verified that no assumption on the
fraction-field extension was added. The final source-based check of the pullback
projection equations found no mismatch and required no mathematical change. The first
compiler pass required fully qualifying `CommRingCat.ofHom`; the corrected file then
compiled cleanly. No new nodes or dependency modules need review.
