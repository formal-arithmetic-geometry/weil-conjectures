## Worker report

Stated `AlgebraicGeometry.exists_normalIntegralFiniteSheafNorm` in
`Sheaf.AlgebraicGeometry.NormalIntegralFiniteSheafNorm`. The sole theorem has proof
`sorry`, as required for stage 2. No definitions, auxiliary theorems, dependency
repairs, new nodes, or statement changes are needed. Only the item's `lean` record
changes. All binders are explicit, with `set_option autoImplicit false`.

Source read: `literature/stacks-project/divisors.tex`, Section `section-norms`
(Tag 0BCX), conditions (1) and (2), and `lemma-norm-in-normal-case` (Tag 0BD3).
The latter constructs the field norm on affine opens and glues it. The node already
correctly spells out the signed constant coefficient and its positive power; the
source's concluding paragraph confusingly calls the constant coefficient `b_0`
after writing it as `b_m` and suppresses the sign. This does not affect either the
node's statement or its proof, and no node correction is made. The theorem asserts
existence of a positive degree, exactly as the node does, without adding an equality
identifying that degree with the function-field degree.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes `Y`, `Z` and a morphism `p : Y → Z` | `{Y Z : Scheme.{u}} (p : Y ⟶ Z)` |
| Finite and surjective | `[IsFinite p] [Surjective p]` |
| Both schemes integral | `[IsIntegral Y] [IsIntegral Z]` |
| Every local ring of `Z` is an integrally closed domain | `hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z)` |
| An integer `d ≥ 1` | `∃ d : ℕ, 1 ≤ d ∧ ...`; nonnegative integers at least one are exactly positive integers |
| Maps on sections for all opens | `∃ ν : ∀ V : Z.Opens, Γ(Y, p ⁻¹ᵁ V) →* Γ(Z, V), ...` |
| Multiplication and one preserved | The `MonoidHom` type `→*` supplies precisely these two laws |
| Compatibility with every restriction `W ⊆ V` | First conjunct, quantifying `V W`, `h : W ≤ V`, and all sections `b`; restrictions are the structure presheaf maps on `(homOfLE h).op` and `(homOfLE (p.preimage_mono h)).op` |
| `ν_V(p♯a) = a^d` for every section | Second conjunct: `∀ V a, ν V (p.app V a) = a ^ d` |
| Vanishing at any point over `V` implies vanishing at its image | Third conjunct: for every `V b y hy`, `Y.evaluation (p ⁻¹ᵁ V) y hy b = 0 → Z.evaluation V (p y) hy (ν V b) = 0` |
| Values in residue fields | `Scheme.evaluation` is the germ followed by `Scheme.residue`, with codomain `Scheme.residueField`; `hy` also witnesses `p y ∈ V` by definition of preimage |

There is no additivity requirement on `ν`. Its maps are neither ring
homomorphisms nor the determinant norm on arbitrary section modules. The two
existentials give one global degree and one simultaneous family of maps.

Statement dependencies used, with their recorded modules and declarations:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom` (also `Hom.app` and
  inverse images of opens).
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`. The statement needs its finite clause.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, with `Scheme.evaluation` for the specified
  residue-field values (evaluation's definition and docstring read at lines 90–101).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral` (nonempty and domain sections on nonempty opens).
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, with the recorded inline `IsDomain` conjunction on stalks.

Plain proof imports preserve the node's stage-3 plan:

- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`:
  `AlgebraicGeometry.Spec.residueFieldMap_residueFieldIso_hom` for
  `lem-weil-pbc-spec-map-residue-field-naturality` (full signature and docstring read).
- `Mathlib.AlgebraicGeometry.FunctionField`:
  `functionField_isFractionRing_of_isAffineOpen`, `germ_injective_of_isIntegral`,
  `Scheme.germToFunctionField_injective`, and the stalk fraction-field/domain instances
  for the two integral-function-field nodes.
- `Mathlib.RingTheory.Algebraic.Integral`: the fraction-ring finite-dimensional instance
  for `lem-trf-finite-domain-fraction-degree`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`:
  `Scheme.exists_germToFunctionField_eq` for `lem-sc-function-field-sections-glue`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`:
  `Algebra.IsIntegral.of_finite` for `lem-weil-pbc-finite-algebra-is-integral`.
- `Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed`:
  `minpoly.isIntegrallyClosed_eq_field_fractions`, with `minpoly.monic` and
  `minpoly.aeval` available through imports, for integral minimal-polynomial descent.
- `Mathlib.RingTheory.Norm.Transitivity`: `Algebra.norm_eq_norm_adjoin` and the
  imported `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly` for the finite-field
  norm formula, including inseparable extensions.
- The public residue-field import and its affine-scheme imports provide
  `Scheme.evaluation_eq_zero_iff_notMem_basicOpen`,
  `IsAffineOpen.fromSpec_preimage_basicOpen`, `IsAffineOpen.fromSpec_primeIdealOf`,
  `IsAffineOpen.basicOpen`, `IsAffineOpen.isLocalization_basicOpen`, and
  `PrimeSpectrum.mem_basicOpen` for affine section vanishing.

Edge cases checked before writing: the empty scheme is excluded by the node's
integrality hypotheses, whereas the empty open is included in every quantifier.
Its section rings are one-element rings and the map and scalar law make sense.
The vanishing clause there has no points to test. Identity maps admit degree one.
Zero sections cause no conflict with the scalar law or vanishing condition.
Purely inseparable finite covers in positive characteristic remain included;
there is no separability, Noetherian, locally free, affine-target, quasi-compact,
or characteristic hypothesis. A general universe `u` is retained. Restriction
ranges over arbitrary opens, including non-affine overlaps.

Searches actually run through `msearch.py NS lem-sfb-normal-integral-finite-sheaf-norm`:

- LeanFinder: “A finite surjective morphism of integral schemes onto a normal
  scheme has a multiplicative norm on structure sheaf sections compatible with
  restriction and vanishing at image points”. Eight hits: normalization interfaces
  and `Algebra.intNorm`. No sheaf-norm existence statement. `Algebra.intNorm` has
  additional integrally-closed-source assumptions and is a ring construction.
- Loogle: `AlgebraicGeometry.IsFinite, "norm"`. Zero hits.
- Mathlib grep: `norm.*[Ss]heaf|[Ss]heaf.*[Nn]orm`, subdirectory
  `AlgebraicGeometry`. Five normalization hits; no matching theorem.
- LeanSearch: “A finite surjective morphism of integral schemes onto a normal
  integral scheme admits a norm on the structure sheaf”. Eight hits on finite
  morphisms, surjectivity and normalization; no matching norm theorem.
- Direct `rg` searches in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for sheaf norms, norm existence, and normal
  integral norm phrases found no exact declaration. The item-id search in
  `lean/WeilConjectures` found none. The citing module
  `Sheaf.AlgebraicGeometry.FiniteNormalAmpleDescent` mentions this node only in its
  proof plan; it does not state it.
- Read the candidate `WeilConjectures.AlgebraicGeometry.BaseChangeNorm` in full.
  `Scheme.Hom.normAt` is `Algebra.norm` of the sections algebra, meaningful under
  finite freeness. Its compatibility and vanishing lemmas require a pullback
  along a finite field extension and affine opens. It does not assert the norm
  here for arbitrary finite integral covers and arbitrary opens, so it cannot
  serve as an existing statement or as this theorem's norm family.

No statement disputes or unusable dependency interfaces were found.

Validation: `scompile.py` compiled the file both as a sandbox module and under its
final library module name, with no errors or unexpected warnings (4.7 s and 3.5 s).

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
