/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Reduction steps for the eight curve-cohomology assertions

This file collects the reduction steps through which the eight curve-cohomology assertions
`AlgebraicGeometry.IsCurve.Assertions` (and in particular the invariance `C₇` of the cohomology
of a proper curve under extension of algebraically closed fields) are reduced to the
calculations on smooth curves with constant coefficients.

Throughout, `k` is an algebraically closed field, a curve over `k` is a morphism
`f : X ⟶ Spec k` with `AlgebraicGeometry.IsCurve f`, coefficient sheaves are étale sheaves of
`Λ`-modules and `Hᵠ(X, F)` is the cohomology of the underlying abelian sheaf. A sheaf of
`𝐅_r`-modules is a sheaf `F` of `Λ`-modules killed by the prime `r`, i.e. `r • 𝟙 F = 0`, or (in
the hypotheses of the reduction statements) a sheaf of modules over `ULift (ZMod r)`.

## Main statements

- `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`: étale cohomology of a
  quasi-compact quasi-separated scheme commutes with filtered colimits.
- `AlgebraicGeometry.IsCurve.Assertions.of_shortExact`: dévissage, the assertions for the outer
  terms of a short exact sequence imply those for the middle term.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero`: field
  extension invariance in dimension zero.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_forall_isReduced`: `C₇` reduces to
  reduced curves and constructible `𝐅_r`-coefficients.
- `AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced`: all eight assertions reduce to
  reduced curves and constructible `𝐅_ℓ`-coefficients.
- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_lowerShriek`: localisation to a dense
  open on which the coefficients are finite locally constant.
- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_forall_lowerShriek`: the same, split
  along the irreducible components of the dense open.
- `AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar`: the normalisation
  exact sequence `0 → j_! 𝐅_ℓ → ν_* j'_! 𝐅_ℓ → Q → 0`.
- `AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`: the
  assertions for `j_! 𝐅_ℓ` on a reduced curve follow from those on its normalisation.

## References

- Stacks Project, Section 59.83, <https://stacks.math.columbia.edu/tag/03SB>
- Stacks Project, Lemma 59.51.7 (cohomology and filtered colimits),
  <https://stacks.math.columbia.edu/tag/03Q6>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Filtered colimits -/

/-- **Étale cohomology commutes with filtered colimits on a qcqs scheme.** Let `X` be
quasi-compact and quasi-separated and let `c` be a colimit cocone of a filtered diagram `D` of
abelian étale sheaves on `X`. Then for every `q` the canonical map
`colim_λ Hᵠ(X, D_λ) ⟶ Hᵠ(X, colim_λ D_λ)` is bijective; this is spelled out elementwise:
every class on the colimit comes from some `D_λ`, and a class on `D_λ` which dies on the colimit
already dies on some `D_μ`, `λ ⟶ μ`. The compatibility with the pullback along a field
extension is the naturality `AlgebraicGeometry.Etale.cohomologyMap_map` of the pullback maps.
The statement holds for arbitrary (not only torsion) abelian sheaves, and for filtered diagrams
indexed by a category in the universe `u + 1` of the coefficients, such as the diagram of
finitely generated subgroups of an abelian group of that universe; the case of a diagram
indexed in the universe `u` is `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`.
(blueprint: `lemma-weil-pbc-curve-filtered-cohomology`) -/
@[stacks 03Q6]
theorem Scheme.H_map_isColimit_of_isFiltered_of_large (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (j : J) (y : Sheaf.H (D.obj j) q),
      Sheaf.H.map (c.ι.app j) q y = x) ∧
    ∀ (j : J) (y : Sheaf.H (D.obj j) q), Sheaf.H.map (c.ι.app j) q y = 0 →
      ∃ (j' : J) (φ : j ⟶ j'), Sheaf.H.map (D.map φ) q y = 0 :=
  sorry

/-- **Étale cohomology commutes with filtered colimits on a qcqs scheme.** Let `X` be
quasi-compact and quasi-separated and let `c` be a colimit cocone of a filtered diagram `D` of
abelian étale sheaves on `X`. Then for every `q` the canonical map
`colim_λ Hᵠ(X, D_λ) ⟶ Hᵠ(X, colim_λ D_λ)` is bijective; this is spelled out elementwise:
every class on the colimit comes from some `D_λ`, and a class on `D_λ` which dies on the colimit
already dies on some `D_μ`, `λ ⟶ μ`. The compatibility with the pullback along a field
extension is the naturality `AlgebraicGeometry.Etale.cohomologyMap_map` of the pullback maps.
The statement holds for arbitrary (not only torsion) abelian sheaves. This is the case of a
diagram indexed in the universe `u` of
`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered_of_large`.
(blueprint: `lemma-weil-pbc-curve-filtered-cohomology`) -/
@[stacks 03Q6]
theorem Scheme.H_map_isColimit_of_isFiltered (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {J : Type u} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (j : J) (y : Sheaf.H (D.obj j) q),
      Sheaf.H.map (c.ι.app j) q y = x) ∧
    ∀ (j : J) (y : Sheaf.H (D.obj j) q), Sheaf.H.map (c.ι.app j) q y = 0 →
      ∃ (j' : J) (φ : j ⟶ j'), Sheaf.H.map (D.map φ) q y = 0 := by
  have : IsFiltered (AsSmall.{u + 1} J) := IsFiltered.of_equivalence AsSmall.equiv
  obtain ⟨h₁, h₂⟩ := X.H_map_isColimit_of_isFiltered_of_large
    (IsColimit.whiskerEquivalence hc AsSmall.equiv.symm) q
  refine ⟨fun x ↦ ?_, fun j y hy ↦ ?_⟩
  · obtain ⟨j, y, hy⟩ := h₁ x
    exact ⟨AsSmall.down.obj j, y, hy⟩
  · obtain ⟨j', φ, hφ⟩ := h₂ (AsSmall.up.obj j) y hy
    exact ⟨AsSmall.down.obj j', AsSmall.down.map φ, hφ⟩

/-! ### Dévissage -/

/-- **Short exact dévissage for the eight curve assertions.** Let `X` be a curve over `k` and
`0 ⟶ F₁ ⟶ F ⟶ F₂ ⟶ 0` a short exact sequence of étale sheaves of `Λ`-modules on `X`. If the
eight assertions `C(X, F₁)` and `C(X, F₂)` hold, then so does `C(X, F)`: the long exact
cohomology sequences (and their pullbacks along a field extension) pass vanishing, finiteness
and bijectivity to the middle term, the hypotheses of the assertions being inherited by
subsheaves and quotients, constructibility for subsheaves since `Λ` is noetherian; for `C₈` one uses
`H³(X, F₁) = 0`, i.e. `C₁(X, F₁)`.
(blueprint: `lemma-weil-pbc-eight-curve-devissage`) -/
theorem IsCurve.Assertions.of_shortExact [IsNoetherianRing Λ] {k : Type u} [Field k]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (h₁ : IsCurve.Assertions Λ f S.X₁) (h₃ : IsCurve.Assertions Λ f S.X₃) :
    IsCurve.Assertions Λ f S.X₂ :=
  sorry

/-! ### Dimension zero -/

/-- **Field extension in dimension zero.** Let `k ⊆ k'` be algebraically closed fields, `C` a
separated `k`-scheme of finite type of dimension at most zero, and `F` a torsion étale sheaf of
`Λ`-modules on `C`. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` is bijective for every `q`: both sides vanish for
`q > 0`, and in degree zero both are the finite product of the stalks of `F` at the points of
`C`. (blueprint: `lem-weil-pbc-zero-dimensional-field-extension`) -/
theorem IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] (hC : topologicalKrullDim C ≤ 0)
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

/-! ### Reduction to constructible prime torsion -/

/-- **Reduction of `C₇` to constructible prime torsion on reduced curves.** Let `k` be
algebraically closed. Suppose that `C₇` holds for every reduced proper curve `X` over `k`,
every prime `r` and every constructible sheaf `G` of `𝐅_r`-modules on `X` (modules over
`ULift (ZMod r)`), i.e. that the pullback `Hᵠ(X, G) ⟶ Hᵠ(X', ι'^* G)` is bijective for every
base change `X'` of `X` to an algebraically closed extension `k'` of `k`. Then `C₇(C, F)`
holds for every proper curve `C` over `k` and every torsion sheaf `F` of `Λ`-modules.

The proof replaces `C` by `C_red` (a universal homeomorphism), writes the underlying abelian
sheaf of `F` as the filtered colimit of its constructible subsheaves
(`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`), splits a constructible sheaf into
its primary parts and dévisses an `r`-primary one along `0 → F[r] → F → F/F[r] → 0`
(`AlgebraicGeometry.IsCurve.Assertions.of_shortExact`).
(blueprint: `lem-weil-pbc-curve-constructible-reduction`) -/
theorem IsCurve.bijective_cohomologyMap_of_forall_isReduced {k : Type u} [Field k]
    [IsAlgClosed k]
    (H : ∀ {X X' : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve g] [IsProper g] [IsReduced X]
      (k' : Type u) [Field k'] [IsAlgClosed k'] {ι : Spec (.of k') ⟶ Spec (.of k)}
      {g' : X' ⟶ Spec (.of k')} {ι' : X' ⟶ X} (_ : IsPullback ι' g' g ι) (r : ℕ) [Fact r.Prime]
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
      [Scheme.IsConstructibleSheaf G] (q : ℕ),
      Function.Bijective (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj G) q))
    {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] (k' : Type u)
    [Field k'] [IsAlgClosed k'] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')}
    {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

/-- **Constructible and primary reduction of the eight assertions.** Let `k` be algebraically
closed. Suppose that the eight assertions `C(X, G)` hold for every reduced curve `X` over `k`,
every prime `ℓ` and every constructible sheaf `G` of `𝐅_ℓ`-modules on `X` (modules over
`ULift (ZMod ℓ)`). Then `C(C, F)` holds for every curve `C` over `k` and every torsion sheaf
`F` of `Λ`-modules, for a finite ring `Λ` (over an infinite ring such as `𝐅_ℓ[t]` the constant
sheaf is constructible and its `H⁰` on a proper curve is infinite); in particular so does the field
extension invariance `C₇`.

The proof is that of `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_forall_isReduced`,
run for all eight assertions simultaneously: reduction to `C_red`, constructible approximation
and continuity of cohomology, primary decomposition, and induction on the exponent along
`0 → F[ℓ] → F → F/F[ℓ] → 0` using `AlgebraicGeometry.IsCurve.Assertions.of_shortExact`.
(blueprint: `lemma-weil-pbc-curve-constructible-primary-reduction`) -/
theorem IsCurve.Assertions.of_forall_isReduced [Finite Λ] {k : Type u} [Field k]
    [IsAlgClosed k]
    (H : ∀ {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve g] [IsReduced X] (ℓ : ℕ)
      [Fact ℓ.Prime]
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
      [Scheme.IsConstructibleSheaf G], IsCurve.Assertions (ULift.{u + 1} (ZMod ℓ)) g G)
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionSheaf F] :
    IsCurve.Assertions Λ f F :=
  sorry

/-! ### Localisation to a dense open -/

/-- **Dense-open localisation reduction.** Let `X` be a reduced curve over an algebraically
closed field `k` and `F` a constructible sheaf of `Λ`-modules killed by a prime `r`, over a
finite ring `Λ`. There is a dense open `j : U ⟶ X` whose connected components are irreducible
and on which `F` is finite locally constant, and for it the eight assertions for `F` are
equivalent to those for `j_! j^* F`: the open–closed sequence `0 → j_! j^* F → F → i_* i^* F → 0`
has third term
supported on the zero-dimensional complement `Z` of `U`, whose cohomology is concentrated in
degree zero and invariant under field extension.
(blueprint: `lemma-weil-pbc-curve-dense-open-reduction`) -/
theorem IsCurve.exists_dense_assertions_iff_lowerShriek [Finite Λ] {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      (∀ x ∈ (U : Set X), IsIrreducible (connectedComponentIn (U : Set X) x)) ∧
      Scheme.IsFiniteLocallyConstantSheaf ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F) ∧
      (IsCurve.Assertions Λ f F ↔ IsCurve.Assertions Λ f
        ((U.ι)_!open[ModuleCat.{u + 1} Λ].obj ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  sorry

/-- **Dense-open localisation, componentwise.** Let `C` be a reduced curve over an
algebraically closed field `k` and `F` a constructible sheaf of `Λ`-modules killed by a prime
`r`, over a finite ring `Λ`. There are finitely many pairwise disjoint irreducible opens
`U_a ⊆ C`, with dense union `U` and zero-dimensional complement `Z = C ∖ U`, on each of which
`F` is finite locally constant, such that, writing `j_a : U_a ⟶ C` for the inclusions,
`C(C, F) ↔ ∀ a, C(C, j_{a,!}(F|_{U_a}))`. This combines the open–closed sequence
`0 → j_! j^* F → F → i_* i^* F → 0`, the assertions on the zero-dimensional `Z`, the
decomposition `j_! j^* F = ⨁_a j_{a,!}(F|_{U_a})` and dévissage.
(blueprint: `lem-weil-pbc-curve-dense-open-localization`) -/
theorem IsCurve.exists_dense_assertions_iff_forall_lowerShriek [Finite Λ] {k : Type u}
    [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsReduced C]
    (r : ℕ) [Fact r.Prime] (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0) :
    ∃ (n : ℕ) (U : Fin n → C.Opens), Dense (⋃ a, (U a : Set C)) ∧
      Pairwise (fun a b ↦ Disjoint (U a : Set C) (U b)) ∧ (∀ a, IsIrreducible (U a : Set C)) ∧
      topologicalKrullDim ↥(⋃ a, (U a : Set C))ᶜ ≤ 0 ∧
      (∀ a, Scheme.IsFiniteLocallyConstantSheaf (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) ∧
      (IsCurve.Assertions Λ f F ↔ ∀ a, IsCurve.Assertions Λ f
        (((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  sorry

/-! ### Normalisation -/

/-- **The normalisation exact sequence.** Let `X` be a reduced curve over an algebraically
closed field `k`, `ν : X' ⟶ X` a finite surjective morphism which is an isomorphism over a
dense open `V ⊆ X` (e.g. the normalisation of `X`), `j : U ⟶ X` an open immersion and
`j' : U' ⟶ X'` its pullback along `ν`. For a prime `ℓ` with `Λ/ℓΛ` finite there is a
monomorphism

`α : j_! (Λ/ℓ)_U ⟶ ν_* j'_! (Λ/ℓ)_{U'}`

(the extension by zero of the unit of `ν|_{U'}^* ⊣ ν|_{U'*}`, stalkwise the diagonal into the
fibre) whose cokernel `Q` is constructible and supported on the finite set `X ∖ V`, giving the
short exact sequence `0 → j_! 𝐅_ℓ → ν_* j'_! 𝐅_ℓ → Q → 0`.

Mathlib's `Scheme.Hom.normalization` is the relative normalisation of a morphism, and does not
directly provide the normalisation of a reduced curve together with its finiteness; we therefore
state the lemma for an arbitrary finite surjective `ν` which is an isomorphism over a dense open,
the properties of the normalisation that are used. The compatibility of the sequence with field
extension and restriction to opens, also part of the blueprint statement, is not recorded in
this existential form. (blueprint: `lemma-weil-pbc-normalization-exact-sequence`) -/
theorem exists_mono_lowerShriek_constantModSheaf_lowerStar {k : Type u} [Field k]
    [IsAlgClosed k] {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] (V : X.Opens) (hV : Dense (V : Set X))
    [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j] {j' : U' ⟶ X'} [IsOpenImmersion j']
    {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ) [Fact ℓ.Prime]
    [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})] :
    ∃ α : (j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ) ⟶
        (ν)_*[ModuleCat.{u + 1} Λ].obj
          ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ)),
      Mono α ∧ Scheme.IsConstructibleSheaf (cokernel α) ∧
        IsZero ((V.ι)^*[ModuleCat.{u + 1} Λ].obj (cokernel α)) :=
  sorry

/-- **Normalisation and the smooth constant case.** Let `X` be a reduced curve over an
algebraically closed field `k`, `ν : X' ⟶ X` a finite surjective morphism from a smooth
`k`-scheme which is an isomorphism over a dense open (e.g. the normalisation of `X`),
`j : U ⟶ X` an open immersion and `j' : U' ⟶ X'` its pullback along `ν`. Then the eight
assertions for `j_! 𝐅_ℓ` on `X` follow from those for `j'_! 𝐅_ℓ` on the smooth curve `X'`
(which are the Kummer and Artin–Schreier calculations): finite direct image is exact and
preserves cohomology, and the normalisation exact sequence
`AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar` has a third term whose
cohomology is concentrated in degree zero and invariant under field extension.
(blueprint: `lemma-weil-pbc-curve-normalization-constant`) -/
theorem IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite {k : Type u} [Field k]
    [IsAlgClosed k] {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] [Smooth (ν ≫ f)] (V : X.Opens)
    (hV : Dense (V : Set X)) [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j]
    {j' : U' ⟶ X'} [IsOpenImmersion j'] {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ)
    [Fact ℓ.Prime]
    (H : IsCurve.Assertions Λ (ν ≫ f)
      ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ))) :
    IsCurve.Assertions Λ f ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ)) :=
  sorry

end AlgebraicGeometry
