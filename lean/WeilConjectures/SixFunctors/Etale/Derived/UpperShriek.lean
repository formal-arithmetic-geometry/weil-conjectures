/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek

public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound

/-!

# Derived Upper Shriek

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *defined* here as a chosen right adjoint of the derived lower shriek `Rf_!` on the
unbounded derived categories of étale sheaves. It is defined whenever `Rf_!` is a left adjoint,
which is taken as an instance argument.

# Main Results

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : for torsion coefficients,
  `A = ModuleCat Λ` with `Λ` finite, `Rf_!` is a left adjoint on `D(X_ét)`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét) ⥤ D(X_ét)`, with scoped
  notation `R(f)^![A]`, for `Rf_!` a left adjoint.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

- `AlgebraicGeometry.Etale.HasBoundedBelowUpperShriek` : `Rf^!` exists and preserves bounded
  below objects, an instance for torsion coefficients over a quasi-compact base; and
  `AlgebraicGeometry.Etale.HasBoundedBelowUpperShrieks`, the same for every `f` with
  quasi-compact target.

## Implementation notes

* That `Rf_!` is a left adjoint is *not* true for an arbitrary coefficient category: it rests
  on `Rg_*` preserving coproducts for the proper part `g` of the compactification, which needs
  `Rg_*` to have finite cohomological dimension, i.e. torsion coefficients. For general `A` the
  existence of the right adjoint is therefore an instance argument
  `[(R(f)_![A]).IsLeftAdjoint]` of `rightDerivedUpperShriek`, and it is supplied as an instance
  only at the torsion coefficients `ModuleCat Λ`, `[Finite Λ]`
  (`isLeftAdjoint_rightDerivedLowerShriek`). That instance is the blueprint theorem
  `thm-amb-etale-exceptional-adjoint` of the smooth-purity chapter (Brown representability,
  Stacks `0F5Y`, applied to the coproduct-preserving `Rf_!`), proved in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.
* `Rf^!` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint extracted from
  the instance, not a construction. Only the adjunction `rightDerivedUpperShriekAdjunction`
  should be used about it; it has no definitional content.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.
* No bounded below variant of `Rf^!` is defined here. The ambient `Rf^!` preserves `D⁺` only
  through the finite cohomological amplitude of `Rf_!`, and the bounded below exceptional
  functor of the blueprint is the constructible one of `sk-prop-sf-existence` (c). That `Rf^!`
  preserves `D⁺` is recorded, together with the existence of `Rf^!`, by the hypothesis class
  `AlgebraicGeometry.Etale.HasBoundedBelowUpperShriek`, which the pro-étale adjunction for
  `Rf^!` assumes; it is an instance for torsion coefficients when `Y` is quasi-compact
  (`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`). Quasi-compactness is needed: for
  `Y = ⊔ₙ Spec k` and `X = ⊔ₙ ℙⁿ_k`, `f` proper, `Rf^! Λ` is `Λ(n)[2n]` on `ℙⁿ_k`, which is not
  bounded below.

## TODO

* The composition `R(f ≫ g)^! ≅ R(g)^! ⋙ R(f)^!`, from the corresponding compatibility
  of `Rf_!`.
* For `f` étale, `Rf^! = f^*`; for `f` proper, `Rf^!` is right adjoint to `Rf_*`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section TorsionCoefficients

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `thm-amb-etale-exceptional-adjoint`: The ordinary ambient exceptional adjoint.

For torsion coefficients `Λ`, the derived lower shriek `Rf_! : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` is a
left adjoint; its right adjoint is the exceptional inverse image `Rf^!`.

`Rf_! = D(i_!) ⋙ Rg_*` for the chosen compactification `(i, g)` of `f`. The extension by zero
is exact and commutes with coproducts. For torsion coefficients the proper `Rg_*` has finite
cohomological dimension, locally on `Y` bounded by twice the fibre dimension of `g`, and its
cohomology sheaves commute with filtered colimits, so `Rg_*` preserves coproducts on the
unbounded derived category. Brown representability for the derived category of the
Grothendieck abelian category of étale sheaves of `Λ`-modules (Stacks `0F5Y`) then gives the
right adjoint [SGA 4, Exp. XVIII, Thm 3.1.4]. -/
instance isLeftAdjoint_rightDerivedLowerShriek [Finite Λ] :
    (R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint :=
  isLeftAdjoint_rightDerivedLowerShriekOfCompactification Λ _

end TorsionCoefficients

section Unbounded

variable [(R(f)_![A]).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : D(Y_ét) ⥤ D(X_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: *by
definition* a chosen right adjoint of the derived lower shriek `R(f)_![A]`, which is assumed
to be a left adjoint (this holds for torsion coefficients,
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`). -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (R(f)_![A]).rightAdjoint

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" A "]" =>
  rightDerivedUpperShriek A f

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of étale sheaves. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_![A] ⊣ R(f)^![A] :=
  Adjunction.ofIsLeftAdjoint _

instance : (R(f)^![A]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isRightAdjoint

variable (Λ : Type*) [Ring Λ] [Linear Λ A] in
/-- If `A` is `Λ`-linear, the exceptional inverse image `Rf^!` is `Λ`-linear, being right
adjoint to the `Λ`-linear functor `Rf_!`. -/
instance linear_rightDerivedUpperShriek : (R(f)^![A]).Linear Λ :=
  (rightDerivedUpperShriekAdjunction A f).right_adjoint_linear

end Unbounded

section BoundedBelow

/-- `Rf_!` is a left adjoint whose right adjoint `Rf^!` preserves bounded below objects: if
`K ∈ D(Y_ét)` is bounded below, then so is `Rf^! K ∈ D(X_ét)`.

This is what the constructible pro-étale `Rf^!`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`) needs of the étale one. Neither half
holds for an arbitrary coefficient category: both rest on the finite cohomological amplitude of
the proper direct image, that is, on torsion coefficients, where the class is the instance
`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`. Note that `Rf^!` is not left t-exact:
the bound it produces is shifted by the cohomological amplitude of `Rf_!`, which is why the
condition is about `t.plus` rather than about `IsGE n` for a fixed `n`. -/
class HasBoundedBelowUpperShriek : Prop extends (R(f)_![A]).IsLeftAdjoint where
  plus_rightDerivedUpperShriek_obj (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    DerivedCategory.TStructure.t.plus K →
      DerivedCategory.TStructure.t.plus
        ((@Functor.rightAdjoint _ _ _ _ (R(f)_![A]) ⟨exists_rightAdjoint⟩).obj K)

/-- The exceptional inverse image `Rf^!` preserves bounded below objects. -/
lemma plus_rightDerivedUpperShriek_obj [HasBoundedBelowUpperShriek A f]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((R(f)^![A]).obj K) :=
  HasBoundedBelowUpperShriek.plus_rightDerivedUpperShriek_obj K hK

/-- For finite coefficients and a uniform global upper-amplitude bound `N` for `Rf_!`,
the exceptional inverse image preserves bounded below objects.

Source: SGA 4, Exp. XVIII, 3.1.7; the adjunction and t-structure orthogonality argument.
(blueprint: lem-etale-upper-shriek-bounded-below-from-amplitude)

Proof: if `K` is bounded below by `n` and `L` is bounded above by `n - N - 1`, the
amplitude hypothesis bounds `Rf_! L` above by `n - 1`. Every morphism from `Rf_! L`
to `K` is zero by t-structure orthogonality. The adjunction identifies these morphisms
with those from `L` to `Rf^! K`, so orthogonality bounds `Rf^! K` below by `n - N`.
The bound must be global: finite coefficients alone do not supply a uniform `N`
when the fibre dimensions of the compactification are unbounded. -/
theorem hasBoundedBelowUpperShriek_of_amplitude (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : ℤ)
    (hN : ∀ (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (n : ℤ), DerivedCategory.TStructure.t.IsLE L n →
        DerivedCategory.TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) (n + N)) :
    HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f := by
  refine { plus_rightDerivedUpperShriek_obj := ?_ }
  intro K hK
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - N, ?_⟩
  change DerivedCategory.TStructure.t.IsGE ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) (n - N)
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - N - 1) (n - N) (by omega)]
  intro L φ hL
  have := hn
  have : DerivedCategory.TStructure.t.IsLE
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) (n - 1) := by
    convert hN L (n - N - 1) hL using 1
    omega
  let adj := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f
  apply (adj.homEquiv L K).symm.injective
  rw [adj.homAddEquiv_symm_zero]
  exact DerivedCategory.TStructure.t.zero _ (n - 1) n (by omega)


private theorem exists_uniform_proper_dimension_bound
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] [CompactSpace T]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ d : ℕ, ∀ (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj G) := by
  obtain ⟨d, hd⟩ := exists_fibre_dimension_bound p
  refine ⟨2 * d, fun G q hq ↦ ?_⟩
  apply Etale.isZero_of_forall_isZero_upperStar_algClosurePoint Λ
  intro t
  let x := T.algClosurePoint t
  let sq := IsPullback.of_hasPullback p x
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  have hdim : topologicalKrullDim (pullback p x : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
    let a : Spec (.of (AlgebraicClosure (T.residueField t))) ⟶ Spec (T.residueField t) :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) _))
    have hx : x = a ≫ T.fromSpecResidueField t := rfl
    have : LocallyOfFiniteType (p.fiberToSpecResidueField t) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    rw [hx]
    calc
      _ = topologicalKrullDim
          (pullback (p.fiberToSpecResidueField t) a : Scheme.{u}) := by
        let e := pullbackLeftPullbackSndIso p (T.fromSpecResidueField t) a
        exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm
      _ ≤ topologicalKrullDim (p.fiber t) :=
        topologicalKrullDim_pullback_le_of_field (p.fiberToSpecResidueField t) a
      _ ≤ (d : WithBot ℕ∞) := hd t
  have hvan := Etale.isZero_higherDirectImage_of_two_mul_lt isAddTorsion_of_finite
    (pullback.snd p x) (pullback.snd p x) (𝟙 _) (Category.comp_id _) d hdim
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst p x)).obj G) q (by omega)
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  refine IsZero.of_iso hvan
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapIso
        ((p)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso G q).symm ≪≫
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapDerivedCategoryPlusHomologyFunctorIso q).app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.obj K) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd p x)).rightDerivedFunctorPlus.mapIso
          (((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.fst p x)).mapDerivedCategoryPlusSingleFunctor 0).app G)))

/-- For torsion coefficients and a quasi-compact target `Y`, `Rf_!` is a left adjoint
(`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`) and `Rf^!` preserves bounded
below objects. The second half holds because `Rf_!` has finite cohomological amplitude, bounded
by twice the fibre dimension of the compactification, which is bounded as `Y` is
quasi-compact: if `Rf_!` sends `D^{≤ 0}` into `D^{≤ N}` then `Rf^!` sends `D^{≥ 0}` into
`D^{≥ -N}`, by adjunction [SGA 4, Exp. XVIII, 3.1.7]. Without quasi-compactness of `Y` this
fails: for `Y = ⊔ₙ Spec k` and `X = ⊔ₙ ℙⁿ_k`, `Rf^! Λ` restricts to `Λ(n)[2n]` on `ℙⁿ_k`.

Source: Stacks Project, Tags 0A3V, 095U, and 07K7 (4)(c); SGA 4, Exp. XVIII, 3.1.7.
(blueprint: lem-etale-upper-shriek-quasicompact-bounded-below)

Proof: the proper part of the chosen compactification has uniformly bounded fibre dimension
because its target is quasi-compact. Proper base change and the torsion vanishing bound on
geometric fibres give a uniform classical cohomological-dimension bound. Dimension shifting
on a K-injective complex with injective components gives the same upper amplitude on the
unbounded derived category. Extension by zero is exact, hence preserves the input upper
bound. Apply `hasBoundedBelowUpperShriek_of_amplitude` to the composite. -/
instance hasBoundedBelowUpperShriek [CompactSpace Y] (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] : HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f where
  plus_rightDerivedUpperShriek_obj :=
    plus_obj_of_rightDerivedLowerShriek_adjunction Λ f (Adjunction.ofIsLeftAdjoint _)

/-- The coefficients have exceptional inverse images along every morphism admitting a
compactification, preserving bounded below objects when the target is quasi-compact:
`Rf_!` is a left adjoint for every such `f`, and
`AlgebraicGeometry.Etale.HasBoundedBelowUpperShriek` holds when moreover the target is
quasi-compact. This holds for torsion coefficients
(`AlgebraicGeometry.Etale.hasBoundedBelowUpperShrieks`). -/
class HasBoundedBelowUpperShrieks : Prop where
  isLeftAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (R(f)_![A]).IsLeftAdjoint
  hasBoundedBelowUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [CompactSpace Y] : HasBoundedBelowUpperShriek A f

attribute [instance] HasBoundedBelowUpperShrieks.isLeftAdjoint
  HasBoundedBelowUpperShrieks.hasBoundedBelowUpperShriek

/-- Torsion coefficients have exceptional inverse images, preserving bounded below objects over
a quasi-compact target. -/
instance hasBoundedBelowUpperShrieks (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    HasBoundedBelowUpperShrieks (ModuleCat.{u + 1} Λ) where
  isLeftAdjoint _ _ := inferInstance
  hasBoundedBelowUpperShriek _ _ _ := inferInstance

/-- If every compactifiable morphism has a uniform upper-amplitude bound for `Rf_!`,
finite coefficients have exceptional inverse images preserving bounded below objects.
The amplitude bound is an explicit hypothesis, rather than a consequence of finiteness.

Source: `hasBoundedBelowUpperShriek_of_amplitude` and `HasBoundedBelowUpperShrieks`.
(blueprint: lem-etale-upper-shrieks-bounded-below-from-amplitude)

Proof: for each compactifiable morphism f, take its amplitude bound N and apply
`hasBoundedBelowUpperShriek_of_amplitude f Λ N` to the given bound. Return the resulting
bound for all morphisms, including non-quasi-compact targets, and build the upstream global
class from it. Only proofs of propositions are constructed. -/
theorem hasBoundedBelowUpperShrieks_of_amplitude (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (h : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f],
      ∃ N : ℤ, ∀ (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (n : ℤ), DerivedCategory.TStructure.t.IsLE L n →
          DerivedCategory.TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) (n + N)) :
    HasBoundedBelowUpperShrieks (ModuleCat.{u + 1} Λ) ∧
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f],
        HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f := by
  have hall : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f],
      HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f := by
    intro X Y f hf
    obtain ⟨N, hN⟩ := h f
    simpa only using hasBoundedBelowUpperShriek_of_amplitude f Λ N hN
  refine ⟨?_, hall⟩
  constructor
  · intro X Y f hf
    infer_instance
  · intro X Y f hf hcompact
    exact hall f

end BoundedBelow

end Etale

end AlgebraicGeometry
