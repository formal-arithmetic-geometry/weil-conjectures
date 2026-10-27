## Worker report

The delivery states `Algebra.smooth_chart_generic_residue_transcendence` in
`lean/Sheaf/RingTheory/SmoothChartGenericResidueTranscendence.lean`, with `sorry`.
There are no new definitions, additional nodes, dependency repairs, or statement
corrections. The copied node changes only `lean`.

Sources read: Stacks `morphisms.tex`, Tag 02G1,
`lemma-smooth-omega-finite-locally-free` (lines 7213–7234), and `algebra.tex`, Tag
00P1, `lemma-dimension-at-a-point-finite-type-field` (lines 28221–28275).
The former identifies smooth fibre point dimension with differential rank; the
latter gives point dimension = local-ring dimension + residue transcendence
degree. The module docstring reproduces the node's seven-step assembly, including
minimality, specialization, and the compatible fraction maps.

Hypotheses and objects, clause by clause:

- A nonzero commutative Noetherian local ring is `{A : Type u} [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`. Mathlib's `IsLocalRing A` implies
  `Nontrivial A`; an initially explicit duplicate instance was removed following
  the compiler's overlapping-instance warning. No nonzero case is lost.
- The smooth A-algebra is `{P : Type v} [CommRing P] [Algebra A P] [Smooth A P]`.
  The universes `u` and `v` are independent and explicitly declared.
- `(m : Ideal A) [m.IsMaximal] (hm : m = IsLocalRing.maximalIdeal A)` names
  exactly the distinguished maximal ideal. `(N : Ideal P) [N.IsPrime]` is the
  chosen prime; `hN : m = N.comap (algebraMap A P)` is precisely its contraction
  condition. `m` and `hm` merely name the given local ring's maximal ideal.
- B is written explicitly as `Localization.AtPrime N`. F is its quotient by
  `m.map (algebraMap A (Localization.AtPrime N))`.
- K is modeled by `m.ResidueField`, and L by `N.ResidueField`. For a maximal
  ideal, `m.ResidueField` is canonically the field A/m; in general Mathlib
  provides `IsFractionRing (A ⧸ m) m.ResidueField`. This is a concrete model of
  the specified residue field, not a new field or an extra algebra structure.
  The K-algebra structure on L is explicitly the `.toAlgebra` of
  `Ideal.ResidueField.map m N (algebraMap A P) hN`.

Conclusions, clause by clause:

- `∃ (n : PrimeSpectrum (m.Fiber P)) (r s t : ℕ)` supplies the indicated
  closed-fibre point and all three finite nonnegative integer witnesses.
  The contraction of `n` along `includeRight` equals N, selecting precisely
  the point of the fibre, not an arbitrary point. The fibre prime
  correspondence makes this point unique.
- `topologicalKrullDimAt (n : Spec (CommRingCat.of (m.Fiber P))) = r` states
  the definition of r. `Ideal.Fiber` is Mathlib's canonical tensor order
  K ⊗_A P; tensor symmetry identifies this with the source's P ⊗_A K.
- `ringKrullDim (B ⧸ m.map (algebraMap A B)) = s` is s = dim F.
  The explicit `@Algebra.trdeg ... map.toAlgebra = (t : Cardinal.{v})`
  is t = trdeg_K L with the actual induced field embedding. Neither dimension
  nor cardinal is truncated with `toNat`.
- `r = s + t` is the closed-fibre dimension formula. The `WithBot ℕ∞`
  equalities assert genuine finite dimension, excluding both infinities.
- `∀ Q : PrimeSpectrum P, Q.asIdeal ∈ minimalPrimes P → Q.asIdeal ≤ N →
  Q.asIdeal.comap (algebraMap A P) ∈ minimalPrimes A → ...` quantifies over
  exactly the specified minimal components. Mathlib's `minimalPrimes` is
  minimal among prime ideals; it does not require reducedness or uniqueness.
- p is written as `Q.asIdeal.comap (algebraMap A P)`, E as `p.ResidueField`,
  and H as `Q.asIdeal.ResidueField`. The `IsFractionRing` instances in
  `ResidueField/Ideal.lean` identify these with Frac(A/p) and Frac(P/Q).
  The E-algebra on H is explicitly the canonical residue map along A → P,
  with contraction equality `rfl`; it is not an arbitrary inclusion.
- `∃ q : PrimeSpectrum (p.Fiber P)` with contraction Q names Q-bar.
  Membership in `minimalPrimes (p.Fiber P)` asserts minimality, and
  `ringKrullDim (Localization.AtPrime q.asIdeal) = 0` asserts the
  zero-dimensional localization.
- The `∃ θ : q.asIdeal.ResidueField ≃+* Q.asIdeal.ResidueField` clause
  identifies its residue field with H, requiring equality on every element
  of P under the canonical maps through the tensor fibre. This is the
  canonical identification and forces agreement on E: the maps agree on
  A/p, and all elements of E are fractions of A/p. Tensor balancing gives
  the same action from the left tensor factor.
- `@Algebra.trdeg E H ... canonicalMap.toAlgebra = (r : Cardinal.{v})`
  and `topologicalKrullDimAt (q : Spec ...) = (r : WithBot ℕ∞)` give
  precisely trdeg_E H = dim_Qbar Spec(P ⊗_A E) = r.
- The final `∃ e : H ≃+* FractionRing (B ⧸ Q.map (algebraMap P B))`
  is H ≃ Frac(B/QB). Its displayed equation fixes the image of every x in P
  in the two fields, as in the source's fraction-map proof. Therefore it
  fixes A/p and all of its fractions, proving exactly the requested
  compatibility with E. FractionRing can be formed before Lean has a
  domain instance for B/QB; the asserted equivalence to the field H entails
  that this total fraction ring really is a field. Mathematically QB is
  prime since Q ≤ N; no additional hypothesis is introduced.
- The last sentence distinguishing point dimension r from local-ring
  dimension s is respected by using `topologicalKrullDimAt` for r and
  `ringKrullDim` of the quotient local ring for s throughout.

Dependency declarations used (signatures and docstrings read):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Smooth.Basic`: `Algebra.Smooth` (formal smoothness and
  finite presentation, the recorded interface).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`,
  its `IsFractionRing` instance, and `Ideal.ResidueField.map`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct` and its canonical
  bilinear map; fibre rings use this existing tensor product.

The module also imports the recorded proof interfaces:
`HasRingHomProperty.Spec_iff` from `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`,
`pullbackSpecIso` from `Mathlib.AlgebraicGeometry.Pullbacks`,
`PrimeSpectrum.fibre_primes_residue_fields` from
`WeilConjectures.RingTheory.FibrePrimesResidueFields`,
`Ideal.Fiber.algEquivAux₂` from the fibre module,
`AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg` from
`WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg`,
the localization quotient and prime correspondences from
`Mathlib.RingTheory.Localization.Ideal`, `Mathlib.RingTheory.Localization.Basic`,
and `Mathlib.RingTheory.Localization.AtPrime.Basic`, and
`AlgebraicGeometry.Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
The upstream twins of the two recorded residue/dimension modules are used directly.

Edge cases checked before writing:

- A field A and P=A: all three dimensions are zero; the generic component and
  fraction identifications reduce to the original field.
- A field k, P=k[X], N=(0): r=1, s=0, t=1. At N=(X), r=1, s=1, t=0.
  These distinguish point dimension from local-ring dimension and show why a
  generic point must not be silently replaced by a closed point.
- An étale chart has r=0, so s=t=0; no assumption r>0 is used.
- A nonreduced Noetherian local base, for example k[ε]/(ε²), is allowed.
  Minimal-prime localizations need not be fields; only their dimension is
  zero. Only the residue field is identified with H.
- Multiple minimal components and disconnected smooth algebras are allowed:
  the generic clause is universal only for Q below the fixed N, with no
  global equidimensionality assumption.
- P=0 has no N, and A=0 is excluded by `IsLocalRing`; both match the node.
  No characteristic restriction or algebraic-closedness assumption occurs.

Searches actually run:

- `msearch.py ... leanfinder "smooth algebra over local ring generic component
  fraction field transcendence degree equals closed fibre point dimension"`:
  eight candidates, including `Algebra.IsStandardSmooth.relativeDimension`,
  `Algebra.IsStandardSmoothOfRelativeDimension`, and `Algebra.IsSmoothAt`.
  None states this three-part comparison; the latter notion is not used.
- `msearch.py ... loogle "Algebra.Smooth, Algebra.trdeg"`: zero hits.
- `msearch.py ... grep "trdeg|topologicalKrullDimAt" RingTheory/Smooth`:
  zero hits.
- `msearch.py ... leansearch "smooth local algebra relative dimension generic
  component transcendence degree"`: eight hits, including relative smooth
  dimension, `Algebra.trdeg`, and `trdeg_lt_aleph0`; no exact match.
- `rg` in `lean/WeilConjectures` by the node id: no match. `rg` in
  `lean/Sheaf/RingTheory` and `lean/Sheaf/AlgebraicGeometry` by trdeg and generic
  residue terms found the general dimension formula and the already stated
  downstream tangent-cone extension. Neither states this node. Searches for
  `SmoothChartGenericResidue|smooth_chart_generic_residue` in both project
  namespaces and `dag/lean_names_upstream.json` found no declaration clash.
- A broader `rg` for smooth/trdeg and generic/residue/transcendence found
  `SmoothStrictLocalFieldModelCoeffFractionTrdeg` and unrelated scheme bounds;
  these concern different objects and hypotheses.

Validation: every compile uses the prescribed `scompile.py` wrapper. The initial
elaboration failures were unresolved implicit tensor base and quotient ideal;
both now have explicit arguments. The duplicate `Nontrivial A` instance was
removed. No statement is disputed and no source error was found.

## Second reading by Q28

This is the author's consistency check; the maintainer supplies the independent
review under the direct-delivery brief. Re-read the node and the final Lean
signature together: all hypotheses and clauses are matched above. In particular,
r is a fibre point dimension, t retains the canonical field embedding, every
minimal component under N is included, and the final isomorphism fixes P and
hence E. The two tensor-factor conventions differ only by the existing canonical
tensor symmetry. No notion is redefined, no theorem is proved, and the node's
statement, statement dependencies, and proof remain unchanged.
