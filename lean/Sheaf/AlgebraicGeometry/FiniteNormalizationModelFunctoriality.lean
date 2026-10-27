module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! # Finite normalization models and semilinear functoriality

Source: Stacks Project, Algebra, Tags 034L, 00GY, 0307, 00GQ and 00GK;
Morphisms, Tags 0AVK and 01WI. The semilinear and group-action assertions are the
monic-equation and gluing argument of the DAG node, motivated by de Jong §§3.2, 3.5.
(blueprint: lem-sfb-finite-normalization-model-functoriality)

All normalizations and generic maps below are the existing constructions
`Scheme.normalizationIn`, `Scheme.fromNormalizationIn`, and
`Scheme.Hom.toNormalization`. Compatibility on function fields is expressed by
commutativity after applying `Spec` and the canonical generic morphisms. This avoids
choosing identifications of the function fields of open subschemes. Field isomorphisms
in the semilinear clauses are written in pullback direction. For a left group action
on fields, the pullback of a geometric action map is the inverse field automorphism.
-/

@[expose] public section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The geometry of a finite normalization model.

Source: Stacks Tags 034L, 00GY, 00GQ and 0AVK; finite-type and Noetherian composition
criteria, Tags 01T6, 01S7 and 01T3.
(blueprint: lem-sfb-finite-normalization-model-functoriality)

Proof: On a nonempty affine `Spec A` of `V`, take the integral closure `C` of `A` in
`M`. The affine fraction-field lemma identifies `Frac A` with `k(V)`. Integral closure
in a finite field extension is a normal domain with fraction field `M`. Its localizations
are normal domains (034L, 00GY). These affine charts share the same generic point, so
normalization is integral and has function field `M`; the displayed generic triangle
fixes the identification. The finite-normalization theorem gives finiteness, with no
separability hypothesis. The inclusions `A ⊆ C` are integral and injective, so lying over
(00GQ) gives surjectivity. A finite module over a finite-type `k`-algebra is a finite-type
`k`-algebra. Hence both models are finite type over the Noetherian field spectrum and
are Noetherian. A finite morphism is separated; composition gives the final clause. -/
theorem finite_normalization_model {k : Type u} [Field k]
    (V : Scheme.{u}) [IsIntegral V] (q : V ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (M : Type u) [Field M] [Algebra V.functionField M]
    [FiniteDimensional V.functionField M] :
    IsIntegral (V.normalizationIn M) ∧
    (∀ x : V.normalizationIn M,
      IsDomain ((V.normalizationIn M).presheaf.stalk x) ∧
      IsIntegrallyClosed ((V.normalizationIn M).presheaf.stalk x)) ∧
    LocallyOfFiniteType (V.fromNormalizationIn M ≫ q) ∧
    QuasiCompact (V.fromNormalizationIn M ≫ q) ∧
    IsFinite (V.fromNormalizationIn M) ∧ Surjective (V.fromNormalizationIn M) ∧
    IsNoetherian V ∧ IsNoetherian (V.normalizationIn M) ∧
    (∃! e : Spec (.of M) ≅ Spec (V.normalizationIn M).functionField,
      e.hom ≫ (V.normalizationIn M).fromSpecFunctionField =
        (V.fromSpecOfAlgebraFunctionField M).toNormalization) ∧
    (IsSeparated q → IsSeparated (V.fromNormalizationIn M ≫ q)) := by
  sorry

/-- Restricting a finite normalization model to a nonempty open.

Source: Stacks Tag 0307; the affine normalization construction.
(blueprint: lem-sfb-finite-normalization-model-functoriality)

Proof: A nonempty open contains the generic point and has the same generic stalk.
Transport `k(V) → M` along this canonical stalk isomorphism to obtain `a`. On each
nonempty affine `Spec A` in `U`, both normalizations have coordinate ring the integral
closure of `A` in `M`. Under localization, the identifications are `x/s ↦ x/s` (0307).
They agree on affine refinements of overlaps, so glue to the displayed isomorphism.
Its generic and base triangles characterize it uniquely by injectivity into `M` on
affine coordinate rings. No affine-intersection assumption is used. -/
theorem finite_normalization_model_restrict {k : Type u} [Field k]
    (V : Scheme.{u}) [IsIntegral V] (q : V ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (M : Type u) [Field M] [Algebra V.functionField M]
    [FiniteDimensional V.functionField M] (U : V.Opens) [Nonempty U] :
    ∃ a : Algebra U.toScheme.functionField M,
      @fromSpecOfAlgebraFunctionField U.toScheme inferInstance M inferInstance a ≫ U.ι =
        V.fromSpecOfAlgebraFunctionField M ∧
      ∃! e : @normalizationIn U.toScheme inferInstance M inferInstance a ≅
          pullback (V.fromNormalizationIn M) U.ι,
        e.hom ≫ pullback.snd (V.fromNormalizationIn M) U.ι =
          @fromNormalizationIn U.toScheme inferInstance M inferInstance a ∧
        (@fromSpecOfAlgebraFunctionField U.toScheme inferInstance M inferInstance a).toNormalization
          ≫ e.hom ≫ pullback.fst (V.fromNormalizationIn M) U.ι =
          (V.fromSpecOfAlgebraFunctionField M).toNormalization := by
  sorry

/-- The unique finite map from the normalization to an intermediate finite normal model.

Source: Stacks Tags 00GK and 01WI, and the affine normalization and gluing constructions.
(blueprint: lem-sfb-finite-normalization-model-functoriality)

Proof: On a nonempty affine `Spec A ⊆ U`, write its finite inverse image in `Z` as
`Spec B`. Dominance makes it nonempty, and integrality embeds `B` in `k(Z)`. Each
`b : B` is integral over `A` (00GK), so its prescribed image under `j` lies in the
integral closure `C` of `A` in `M`. These maps `B → C` agree on affine refinements of
overlaps, since they agree in `M` and the germ maps are injective. Glue their spectra.
The same affine test gives uniqueness among all compatible `U`-morphisms. Generators
of `C` as an `A`-module also generate it as a `B`-module. Thus the resulting morphism is
finite on this target affine cover, hence finite by 01WI. The normality assumption
on `Z` is retained, although the construction does not need it. The restriction theorem
identifies this source with `N_U`. -/
theorem finite_normalization_model_intermediate {k : Type u} [Field k]
    (V : Scheme.{u}) [IsIntegral V] (q : V ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (M : Type u) [Field M] [Algebra V.functionField M]
    [FiniteDimensional V.functionField M] (U : V.Opens) [Nonempty U]
    [Algebra U.toScheme.functionField M]
    (hU : U.toScheme.fromSpecOfAlgebraFunctionField M ≫ U.ι =
      V.fromSpecOfAlgebraFunctionField M)
    (Z : Scheme.{u}) [IsIntegral Z]
    (hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z))
    (p : Z ⟶ U.toScheme) [IsFinite p] [IsDominant p]
    (j : Z.functionField →+* M)
    (hj : Spec.map (CommRingCat.ofHom j) ≫ Z.fromSpecFunctionField ≫ p ≫ U.ι =
      V.fromSpecOfAlgebraFunctionField M) :
    ∃ f : U.toScheme.normalizationIn M ⟶ Z,
      f ≫ p = U.toScheme.fromNormalizationIn M ∧
      (U.toScheme.fromSpecOfAlgebraFunctionField M).toNormalization ≫ f =
        Spec.map (CommRingCat.ofHom j) ≫ Z.fromSpecFunctionField ∧
      IsFinite f ∧
      ∀ f' : U.toScheme.normalizationIn M ⟶ Z,
        f' ≫ p = U.toScheme.fromNormalizationIn M →
        (U.toScheme.fromSpecOfAlgebraFunctionField M).toNormalization ≫ f' =
          Spec.map (CommRingCat.ofHom j) ≫ Z.fromSpecFunctionField → f' = f := by
  sorry

/-- A compatible semilinear isomorphism of model and field data lifts uniquely.

Source: the monic-equation transport argument in this node, using Stacks Tag 0307
and scheme-morphism gluing (01JA).
(blueprint: lem-sfb-finite-normalization-model-functoriality)

Proof: For an affine `Spec A'` of `V'`, its inverse image is `Spec A`. If `x'` in `M'`
satisfies a monic equation over `A'`, apply `φ` to the equation. Compatibility changes
its coefficients by the pullback along `f`, so `φ(x')` is integral over `A`. Apply
`φ⁻¹` for the converse. This identifies the two integral closures as rings, with the
specified semilinear action on constants. On localizations the formula is
`x'/s' ↦ φ(x')/f*(s')`; hence the local spectra glue. Gluing the inverse constructions
gives an inverse. Any compatible lift has these same affine ring maps, because the
coordinate rings embed in `M`, which proves uniqueness. -/
theorem finite_normalization_model_semilinear {k k' : Type u} [Field k] [Field k']
    (V V' : Scheme.{u}) [IsIntegral V] [IsIntegral V']
    (q : V ⟶ Spec (.of k)) (q' : V' ⟶ Spec (.of k'))
    [LocallyOfFiniteType q] [QuasiCompact q] [LocallyOfFiniteType q'] [QuasiCompact q']
    (M M' : Type u) [Field M] [Field M']
    [Algebra V.functionField M] [Algebra V'.functionField M']
    [FiniteDimensional V.functionField M] [FiniteDimensional V'.functionField M']
    (κ : k' ≃+* k) (f : V ≅ V') (φ : M' ≃+* M)
    (hk : f.hom ≫ q' = q ≫ Spec.map (CommRingCat.ofHom κ.toRingHom))
    (hM : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      V'.fromSpecOfAlgebraFunctionField M' = V.fromSpecOfAlgebraFunctionField M ≫ f.hom) :
    ∃! F : V.normalizationIn M ≅ V'.normalizationIn M',
      F.hom ≫ V'.fromNormalizationIn M' = V.fromNormalizationIn M ≫ f.hom ∧
      (V.fromSpecOfAlgebraFunctionField M).toNormalization ≫ F.hom =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          (V'.fromSpecOfAlgebraFunctionField M').toNormalization := by
  sorry

/-- Lifting identity data gives the identity of the normalization.

Source: uniqueness in the semilinear affine construction of this node.
(blueprint: lem-sfb-finite-normalization-model-functoriality)

Proof: The identity of the normalization commutes with its base and generic maps.
Any lift of identity data has the same two maps, so the affine uniqueness test in the
semilinear argument identifies it with the identity. -/
theorem finite_normalization_model_identity {k : Type u} [Field k]
    (V : Scheme.{u}) [IsIntegral V] (q : V ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (M : Type u) [Field M] [Algebra V.functionField M]
    [FiniteDimensional V.functionField M] (F : V.normalizationIn M ≅ V.normalizationIn M)
    (hV : F.hom ≫ V.fromNormalizationIn M = V.fromNormalizationIn M)
    (hM : (V.fromSpecOfAlgebraFunctionField M).toNormalization ≫ F.hom =
      (V.fromSpecOfAlgebraFunctionField M).toNormalization) :
    F = Iso.refl (V.normalizationIn M) := by
  sorry

/-- Compatible lifts preserve composition of semilinear data.

Source: uniqueness in the semilinear affine construction of this node.
(blueprint: lem-sfb-finite-normalization-model-functoriality)

Proof: Compose the two base triangles and the two generic triangles. Functoriality of
`Spec` identifies the latter with pullback by `φ.comp ψ`. Thus the composite lift has
the composite base and field data. The same affine uniqueness test identifies it with
any lift `H` of that composite. This argument allows different coefficient fields. -/
theorem finite_normalization_model_composition {k₁ k₂ k₃ : Type u}
    [Field k₁] [Field k₂] [Field k₃]
    (V₁ V₂ V₃ : Scheme.{u}) [IsIntegral V₁] [IsIntegral V₂] [IsIntegral V₃]
    (q₁ : V₁ ⟶ Spec (.of k₁)) (q₂ : V₂ ⟶ Spec (.of k₂))
    (q₃ : V₃ ⟶ Spec (.of k₃))
    [LocallyOfFiniteType q₁] [QuasiCompact q₁]
    [LocallyOfFiniteType q₂] [QuasiCompact q₂]
    [LocallyOfFiniteType q₃] [QuasiCompact q₃]
    (M₁ M₂ M₃ : Type u) [Field M₁] [Field M₂] [Field M₃]
    [Algebra V₁.functionField M₁] [Algebra V₂.functionField M₂]
    [Algebra V₃.functionField M₃]
    [FiniteDimensional V₁.functionField M₁] [FiniteDimensional V₂.functionField M₂]
    [FiniteDimensional V₃.functionField M₃]
    (κ : k₂ ≃+* k₁) (κ₂ : k₃ ≃+* k₂) (f : V₁ ≅ V₂) (g : V₂ ≅ V₃)
    (φ : M₂ ≃+* M₁) (ψ : M₃ ≃+* M₂)
    (hk₁ : f.hom ≫ q₂ = q₁ ≫ Spec.map (CommRingCat.ofHom κ.toRingHom))
    (hk₂ : g.hom ≫ q₃ = q₂ ≫ Spec.map (CommRingCat.ofHom κ₂.toRingHom))
    (hm₁ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      V₂.fromSpecOfAlgebraFunctionField M₂ = V₁.fromSpecOfAlgebraFunctionField M₁ ≫ f.hom)
    (hm₂ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      V₃.fromSpecOfAlgebraFunctionField M₃ = V₂.fromSpecOfAlgebraFunctionField M₂ ≫ g.hom)
    (F : V₁.normalizationIn M₁ ≅ V₂.normalizationIn M₂)
    (G : V₂.normalizationIn M₂ ≅ V₃.normalizationIn M₃)
    (H : V₁.normalizationIn M₁ ≅ V₃.normalizationIn M₃)
    (hF : F.hom ≫ V₂.fromNormalizationIn M₂ = V₁.fromNormalizationIn M₁ ≫ f.hom)
    (hG : G.hom ≫ V₃.fromNormalizationIn M₃ = V₂.fromNormalizationIn M₂ ≫ g.hom)
    (hH : H.hom ≫ V₃.fromNormalizationIn M₃ =
      V₁.fromNormalizationIn M₁ ≫ (f ≪≫ g).hom)
    (hFM : (V₁.fromSpecOfAlgebraFunctionField M₁).toNormalization ≫ F.hom =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (V₂.fromSpecOfAlgebraFunctionField M₂).toNormalization)
    (hGM : (V₂.fromSpecOfAlgebraFunctionField M₂).toNormalization ≫ G.hom =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        (V₃.fromSpecOfAlgebraFunctionField M₃).toNormalization)
    (hHM : (V₁.fromSpecOfAlgebraFunctionField M₁).toNormalization ≫ H.hom =
      Spec.map (CommRingCat.ofHom (φ.toRingHom.comp ψ.toRingHom)) ≫
        (V₃.fromSpecOfAlgebraFunctionField M₃).toNormalization) :
    F ≪≫ G = H := by
  sorry

/-- Every compatible group action extends uniquely to a finite normalization model.

Source: the identity/composition argument following the affine semilinear construction
in this node, motivated by de Jong §§3.2, 3.5.
(blueprint: lem-sfb-finite-normalization-model-functoriality)

Proof: For each `g`, lift its scheme isomorphism using the inverse of its left field
automorphism as pullback. The identity lift is the identity. For `g,h`, the composite
lifts have the composite scheme map and pullback by the inverse of `σ(g*h)`;
uniqueness therefore gives the group law. These lifts form a homomorphism to scheme
automorphisms. Any other compatible action has the same individual lifts and hence
is equal. Neither faithfulness, finiteness of the group, nor triviality on `k` is used. -/
theorem finite_normalization_model_action {k : Type u} [Field k]
    (V : Scheme.{u}) [IsIntegral V] (q : V ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (M : Type u) [Field M] [Algebra V.functionField M]
    [FiniteDimensional V.functionField M] (G : Type v) [Group G]
    (κ : G →* (k ≃+* k)) (ρ : G →* Aut V) (σ : G →* (M ≃+* M))
    (hk : ∀ g : G, (ρ g).hom ≫ q =
      q ≫ Spec.map (CommRingCat.ofHom (κ g).symm.toRingHom))
    (hM : ∀ g : G, Spec.map (CommRingCat.ofHom (σ g).symm.toRingHom) ≫
      V.fromSpecOfAlgebraFunctionField M = V.fromSpecOfAlgebraFunctionField M ≫ (ρ g).hom) :
    ∃! τ : G →* Aut (V.normalizationIn M), ∀ g : G,
      (τ g).hom ≫ V.fromNormalizationIn M = V.fromNormalizationIn M ≫ (ρ g).hom ∧
      (V.fromSpecOfAlgebraFunctionField M).toNormalization ≫ (τ g).hom =
        Spec.map (CommRingCat.ofHom (σ g).symm.toRingHom) ≫
          (V.fromSpecOfAlgebraFunctionField M).toNormalization := by
  sorry

end AlgebraicGeometry.Scheme
