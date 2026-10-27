## Worker report

The module `Sheaf.AlgebraicGeometry.RegularSeparableAffineSmoothNeighbourhood` states
`AlgebraicGeometry.exists_smooth_principal_neighbourhood_of_regular_separable_residue`.
Its only theorem proof is `sorry`. It introduces no definitions, dependency modules, or nodes.
The existing node changes only in `lean`; no statement correction or dispute is needed.

Sources read: Stacks `algebra.tex`, definition-smooth-at-prime (00TB), lines 37510ff,
and lemma-separable-smooth (00TV), lines 38740ff; `schemes.tex`,
lemma-standard-open-affine (01I3), lines 966ff; `morphisms.tex`,
lemma-smooth-characterize (01V6), lines 7048ff. 00TV gives regularity implies smoothness
at the prime with separable residue; 00TB spells this out as a smooth principal
localization. 01I3 identifies its spectrum and 01V6 supplies scheme smoothness.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`. The scheme and the named structure morphism are
  `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`.
- The affine open is `(U : X.Opens) (hU : IsAffineOpen U)`; its section ring is literally
  `Γ(X, U)`, not a separately supplied ring or a mere abstract affine chart.
- The canonical immersion `ι_U` is the existing `hU.fromSpec`. Its definition is
  `hU.isoSpec.inv ≫ U.ι`.
- `[Algebra k Γ(X, U)]` together with
  `hbase : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))`
  presents precisely the induced algebra structure. This equality is the compatibility
  specifying that structure, not an extra geometric hypothesis: full faithfulness of Spec
  uniquely determines the ring map by the given composite `hU.fromSpec ≫ f`.
  Every morphism to Spec k provides this compatible structure on sections. In particular
  no global finite-type, affineness, separation, or smoothness condition on X or f is assumed.
- Finite type of this section algebra is `[Algebra.FiniteType k Γ(X, U)]`. The dependency's
  recorded `RingHom.FiniteType (algebraMap k Γ(X,U))` is this same predicate, as witnessed
  by `RingHom.finiteType_algebraMap`; no replacement finite-type definition is made.
- The prime is `(q : PrimeSpectrum Γ(X, U))`; the point x is `hU.fromSpec q`.
- Regularity is `[IsRegularLocalRing (Localization.AtPrime q.asIdeal)]`, including
  Noetherianity and locality by the existing regular-local class.
- The residue field is `q.asIdeal.ResidueField`, the existing abbreviation for
  `IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)`. Its k-algebra structure
  is the canonical tower from the section ring and localization.
- The finite separable extension is exactly `[Module.Finite k q.asIdeal.ResidueField]`
  and `[Algebra.IsSeparable k q.asIdeal.ResidueField]`. Finiteness here is finite
  dimension as a vector space; separability includes algebraicity.
- Existence of g is the first conjunction:
  `∃ g : Γ(X, U), g ∉ q.asIdeal ∧ Algebra.Smooth k (Localization.Away g)`.
  `Localization.Away g` is localization at `Submonoid.powers g` with its canonical
  section-ring algebra and induced k-algebra.
- The phrase "For such a g" is a separate universal clause, not just properties of a
  specially chosen witness: `∀ g, g ∉ q.asIdeal → Algebra.Smooth k (Localization.Away g) → …`.
- D(g) is `PrimeSpectrum.basicOpen g`. V with its open subscheme structure is literally
  `hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g`, using the open-image operation for the
  canonical open immersion. This avoids introducing V as an unconstrained open.
- The x-in-V assertion is `hU.fromSpec q ∈ hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g`.
- Smoothness of f restricted to V is `Smooth ((hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g).ι ≫ f)`.
- The identification of Spec S_g with V is an isomorphism
  `e : Spec (.of (Localization.Away g)) ≅ (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g).toScheme`.
  Its first compatibility clause says that `e.hom` followed by V's inclusion equals
  `Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away g))) ≫ hU.fromSpec`.
  This fixes the claimed identification by the canonical map, rather than an arbitrary
  scheme isomorphism.
- The second compatibility says `e.hom ≫ V.ι ≫ f` equals the spectrum map of
  `algebraMap k (Localization.Away g)`. By the canonical algebra tower this is precisely
  k → S → S_g. Together the two equalities state that the canonical map into X
  is over Spec k with exactly the specified source structure map.
- No dimension, integrality, normality, perfection, characteristic, or nonemptiness
  hypothesis appears. There is no bound on the scheme's dimension or on the field.

Dependency declarations used and read:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180), including its docstring.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`; `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen.fromSpec`, `isoSpec`,
  `fromSpec_image_basicOpen` (lines 388, 427, 592), with their full signatures.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and the existing instance
  `IsAffineOpen.isOpenImmersion_fromSpec`, needed for the image-open construction.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, `Algebra.FiniteType`,
  `RingHom.finiteType_algebraMap` (lines 217, 220 for the ring-map interface).
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing` (line 51), from the
  unchanged ring part of `def-weil-regular-scheme.mathlib_match`. This item uses only
  the regular-local clause, not the scheme predicate. The recorded scheme interface
  `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`, was
  also read; its scheme clause is unnecessary for this statement.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField` (line 33).
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable` (line 549).
- `Mathlib.RingTheory.Smooth.Basic`: `Algebra.Smooth` (line 540).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` (line 62),
  also providing the ring/scheme comparison and restriction interfaces of the Mathlib
  proof-dependency matches. Public imports expose the statement notions.
- Proof-only imports are `WeilConjectures.FieldTheory.SeparableExtension`
  (`Algebra.IsSeparablyGenerated`, `Algebra.IsSeparableExtension`),
  `WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth`
  (`Algebra.regularLocal_iff_smoothAtPrime`), and
  `WeilConjectures.RingTheory.SingularIdeal` (`Algebra.IsSmoothAtPrime`).
  The module docstring lists all four DAG proof steps and their dependencies.

Searches actually run (2026-10-24):

- `msearch.py … leanfinder "regular local prime finite separable residue finite type algebra
  field smooth principal open neighbourhood"`: 8 hits, including
  `Algebra.IsSmoothAt.exists_notMem_smooth`, `exists_notMem_isStandardSmooth`, and
  `AlgebraicGeometry.IsSmooth.exists_isStandardSmooth`. They assume smoothness at
  the prime or of the ambient morphism and omit the present regularity/residue input
  and the full ambient canonical comparison, so none states this node.
- `msearch.py … loogle "Algebra.Smooth, Localization.Away"`: 3 hits,
  `Algebra.basicOpen_subset_smoothLocus_iff_smooth`,
  `Algebra.IsSmoothAt.exists_notMem_smooth`, and
  `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`; none is an exact match.
- `msearch.py … grep "regular.*[Ss]mooth|[Ss]mooth.*regular|exists_notMem_smooth" RingTheory`:
  2 hits in Smooth/StandardSmoothOfFree and Smooth/Locus, only the already-smooth input.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for regular/smooth and separable
  neighbourhood patterns, and for the exact node id: found the algebraic 00TV interface,
  the upstream formally-smooth-localization theorem, perfect/algebraically closed-field
  variants, and downstream proof citations, but no statement of this whole node.
  Read `WeilConjectures.Mathlib.RingTheory.Smooth.Local` in full through its relevant
  regularity criteria: those give formal smoothness of a local ring rather than the
  present geometric conclusion. The affine-neighbourhood node cited in
  `FlatSmoothPointBaseChange` assumes smoothness at the prime, rather than regularity.
- A focused `rg` over both source roots and `dag/lean_names_upstream.json` for the proposed
  declaration name, regular-separable-neighbourhood variants, and this node id returned
  only downstream proof mentions; the new declaration name does not already exist.

Edge cases checked before writing: U empty (its section ring has no prime, so no q);
S = k and q = 0 (g = 1 and V = U work); a unit g (V = U); g = 0 (excluded by g ∉ q);
a nilpotent g (also excluded). A singular cusp fails the regular-local hypothesis;
a purely inseparable closed point over an imperfect field fails the residue-separability
hypothesis. Separable extensions of positive degree, positive characteristic, reducible
ambient schemes, non-affine X, non-separated X and unbounded dimension are retained.
There is no perfection assumption. All objects lie in a common arbitrary universe u,
as required for morphisms in Mathlib's category of schemes.

Validation: the prescribed `scompile.py Q16 … RegularSeparableAffineSmoothNeighbourhood.lean`
compiled both the sandbox module and the actual library module cleanly on the server
(2.2 s and 2.1 s). No diagnostic commands or auxiliary proof declarations remain.

## Second reading by Q16

This is a separate self-reading pass by the assigned worker; the dispatcher explicitly
forbids starting other agents. The maintainer supplies the independent delivery review.
I reread the node and the full theorem signature clause by clause: the section ring,
canonical chart map, induced base algebra, finite type, regular prime localization,
finite separable residue, existence of a smooth localization, and the universal-for-g
geometric conclusions all have the counterparts listed above. In particular the two
isomorphism compatibility equations fix both the map to X and the map to Spec k.
The universal clause is separate from the existential one, so it retains the source's
"For such a g" assertion for every suitable g. The hbase binder only specifies the
already stipulated induced algebra structure; it is not a smoothness or finiteness
assumption on f. No mismatch was found on this pass, and no node correction is needed.
