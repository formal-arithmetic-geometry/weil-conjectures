/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFreeSheafDerivedSections
public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve.GenericReduction
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Stalks of proper direct images and the cohomology of geometric fibres

Let `f : X ⟶ S` be proper, `Λ` a finite ring and `s : Spec Ω ⟶ S` a geometric point, `Ω`
separably closed. By proper base change, the stalk at `s` of `Rᵠf_* M`, for the constant sheaf on
a `Λ`-module `M`, has the cardinality of the étale cohomology `Hᵠ(X_s, M)` of the geometric fibre
`X_s = X ×_S Spec Ω` (`AlgebraicGeometry.Etale.natCard_sheafFiber_homology_rightDerivedLowerStar`).
For the coefficients `𝔽_ℓ` this is the cardinality of the cohomology `Hᵠ(X_s, ℤ/ℓ)` of the
abelian sheaf `ℤ/ℓ`
(`AlgebraicGeometry.Etale.natCard_sheafFiber_homology_rightDerivedLowerStar_zmod`). Only
cardinalities are compared, so no compatibility of the identifications is needed.

Moreover the stalk at every geometric point has the cardinality of the stalk at the geometric
point given by an algebraic closure of the residue field of some point
(`AlgebraicGeometry.Etale.exists_natCard_sheafFiber_eq_natCard_sheafFiber_algClosurePoint`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Cohomology of sheaves of modules and of abelian sheaves.** On a quasi-compact
quasi-separated scheme `Z`, the étale cohomology `Hᵠ(Z, N)` of a sheaf of `Λ`-modules has the
cardinality of the cohomology of its underlying abelian sheaf. -/
lemma natCard_cohomology_singleFunctor_eq_natCard_sheafH (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z] (N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Nat.card ((Etale.cohomology (ModuleCat.{u + 1} Λ) Z (q : ℤ)).obj ((singleFunctor _ 0).obj N))
      = Nat.card (Sheaf.H ((Etale.forget₂Sheaf Λ Z).obj N) q) := by
  obtain ⟨e⟩ := Scheme.nonempty_freeSheafDerivedSectionsIso Z Λ q
  exact Nat.card_congr ((e.symm ≪≫ Etale.shiftedHomFunctorFreeSheafIso Λ Z q).app
    N).addCommGroupIsoToAddEquiv.toEquiv

variable [Finite Λ]

/-- **Stalks of proper direct images.** For `f : X ⟶ S` proper, a geometric point
`s : Spec Ω ⟶ S` (`Ω` separably closed) with geometric fibre `X_s`, and a `Λ`-module `M`, the stalk
at `s` of `Rᵠf_* M` has the cardinality of `Hᵠ(X_s, M)`: by proper base change it is the stalk at
the closed point of `Spec Ω` of `Rᵠ(X_s ⟶ Spec Ω)_* M`, which is its module of global sections,
`Ω` being separably closed, and the Leray isomorphism computes these as `Hᵠ(X_s, M)`. -/
lemma natCard_sheafFiber_homology_rightDerivedLowerStar {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (M : ModuleCat.{u + 1} Λ) (q : ℤ) :
    Nat.card (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))) =
    Nat.card ((Etale.cohomology (ModuleCat.{u + 1} Λ) (pullback f s) q).obj
      ((singleFunctor _ 0).obj
        ((constantSheaf (pullback f s).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  let E := (homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))
  let L := (singleFunctor _ 0).obj
    ((constantSheaf (pullback f s).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  have e₁ : (pointSmallEtale (𝟙 (Spec (.of Ω)) ≫ s)).sheafFiber.obj E ≅
      (pointSmallEtale s).sheafFiber.obj E := by
    rw [Category.id_comp]
  let e : (pointSmallEtale s).sheafFiber.obj E ≅
      (Etale.cohomology (ModuleCat.{u + 1} Λ) (pullback f s) q).obj L :=
    e₁.symm ≪≫ ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s (𝟙 _)).app E).symm ≪≫
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.mapIso
        (upperStarHomologyRightDerivedLowerStarConstantIsoOfIsProper
          (IsPullback.of_hasPullback f s) M q) ≪≫
      (ΓIsoSheafFiberOfIsSepClosed _).symm ≪≫
      ((homologyRightDerivedGlobalSectionsIsoOfIsSepClosed q).app _).symm ≪≫
      (homologyFunctor _ q).mapIso
        ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ (pullback.snd f s)).app L)
  exact Nat.card_congr e.toLinearEquiv.toEquiv

/-- The abelian sheaf underlying the constant sheaf `𝔽_ℓ` is the constant sheaf `ℤ/ℓ`. -/
noncomputable def forget₂SheafConstantZModIso (Z : Scheme.{u}) (ℓ : ℕ) :
    (Etale.forget₂Sheaf (ULift.{u + 1} (ZMod ℓ)) Z).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) ≅ Z.constantZMod ℓ :=
  haveI : Z.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction _ (ModuleCat.forget₂CoinduceAdj _)
  (constantCommuteCompose Z.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) AddCommGrpCat.{u + 1})).app _

/-- **Stalks of proper direct images of `𝔽_ℓ`.** For `f : X ⟶ S` proper and a geometric point
`s : Spec Ω ⟶ S`, the stalk at `s` of `Rᵠf_* 𝔽_ℓ` has the cardinality of the cohomology
`Hᵠ(X_s, ℤ/ℓ)` of the geometric fibre. -/
theorem natCard_sheafFiber_homology_rightDerivedLowerStar_zmod {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) (ℓ : ℕ)
    [NeZero ℓ] (q : ℕ) :
    Nat.card (((pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj ((homologyFunctor _ (q : ℤ)).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))))) =
    Nat.card (Sheaf.H ((Limits.pullback f s : Scheme.{u}).constantZMod ℓ) q) := by
  have : IsProper (pullback.snd f s) := MorphismProperty.pullback_snd _ _ inferInstance
  have : CompactSpace (Limits.pullback f s : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f s)
  have : QuasiSeparatedSpace (Limits.pullback f s : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f s)
  rw [natCard_sheafFiber_homology_rightDerivedLowerStar,
    natCard_cohomology_singleFunctor_eq_natCard_sheafH]
  exact Nat.card_congr ((Sheaf.functorH _ q).mapIso
    (forget₂SheafConstantZModIso (Limits.pullback f s) ℓ)).addCommGroupIsoToAddEquiv.toEquiv

omit [Finite Λ] in
/-- The stalk of a sheaf of `Λ`-modules has the cardinality of the stalk of its underlying
abelian sheaf. -/
lemma natCard_sheafFiber_forget₂Sheaf {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nat.card (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((Etale.forget₂Sheaf Λ S).obj F)) =
      Nat.card (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact Nat.card_congr (((pointSmallEtale s).sheafFiberCompIso
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F).addCommGroupIsoToAddEquiv.toEquiv

omit [Finite Λ] in
/-- **Stalks do not change under extension of the separably closed field of a geometric
point** (`AlgebraicGeometry.Scheme.isIso_pointSmallEtalePrecomp_sheafFiber`), as far as their
cardinalities are concerned. -/
lemma natCard_sheafFiber_comp {S : Scheme.{u}} {k l : Type u} [Field k] [IsSepClosed k]
    [Field l] [IsSepClosed l] (s : Spec (.of k) ⟶ S) (a : Spec (.of l) ⟶ Spec (.of k))
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nat.card (((pointSmallEtale (a ≫ s)).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) =
      Nat.card (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) := by
  rw [← natCard_sheafFiber_forget₂Sheaf, ← natCard_sheafFiber_forget₂Sheaf]
  have := isIso_pointSmallEtalePrecomp_sheafFiber s a ((Etale.forget₂Sheaf Λ S).obj F)
  exact Nat.card_congr (asIso ((pointSmallEtalePrecomp s a).sheafFiber.app
    ((Etale.forget₂Sheaf Λ S).obj F))).addCommGroupIsoToAddEquiv.toEquiv.symm

omit [Finite Λ] in
/-- **Stalks at geometric points over the same point.** The stalk of a sheaf of `Λ`-modules at a
geometric point `s : Spec Ω ⟶ S` (`Ω` separably closed) has the cardinality of its stalk at the
geometric point `S.algClosurePoint x` given by an algebraic closure of the residue field of some
point `x`: both agree with the stalk at a common algebraically closed extension. -/
lemma exists_natCard_sheafFiber_eq_natCard_sheafFiber_algClosurePoint {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ x : S, Nat.card (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) =
      Nat.card (((pointSmallEtale (S.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F) := by
  let a : Spec (.of (AlgebraicClosure Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
  obtain ⟨⟨x, φ⟩, hφ⟩ : ∃ p, (SpecToEquivOfField (AlgebraicClosure Ω) S).symm p = a ≫ s :=
    ⟨_, Equiv.symm_apply_apply _ _⟩
  let : Algebra (S.residueField x) (AlgebraicClosure Ω) := φ.hom.toAlgebra
  let ψ : AlgebraicClosure (S.residueField x) →ₐ[S.residueField x] AlgebraicClosure Ω :=
    IsAlgClosed.lift
  let b : Spec (.of (AlgebraicClosure Ω)) ⟶ Spec (.of (AlgebraicClosure (S.residueField x))) :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hb : b ≫ S.algClosurePoint x = a ≫ s := by
    rw [← hφ]
    change b ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x)
      (AlgebraicClosure (S.residueField x)))) ≫ S.fromSpecResidueField x =
      Spec.map φ ≫ S.fromSpecResidueField x
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext y
    exact ψ.commutes y
  refine ⟨x, ?_⟩
  rw [← natCard_sheafFiber_comp s a, ← hb, natCard_sheafFiber_comp]

end Etale

end AlgebraicGeometry
