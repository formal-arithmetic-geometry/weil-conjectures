/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.AdmissibleScalarHomologyData
import WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel

/-! # Constructible homology of locally perfect scalar models

Source: blueprint latest, scalar-six-ctf proof (2), local models.
(blueprint: lem-sfb-perfect-local-model-bounded-constructible).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar Functor.mapDerivedCategory
  Functor.mapDerivedCategoryHomologyFunctorIso

-- Check the comparison with abstract functors before substituting the coefficient
-- functors, whose concrete definitions contain large localization constructions.
private theorem homology_model_nonempty
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : B ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (Q : DerivedCategory A) (C : CochainComplex B ℤ)
    (e : F.mapDerivedCategory.obj Q ≅
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj C)) (n : ℤ) :
    Nonempty (F.obj ((DerivedCategory.homologyFunctor A n).obj Q) ≅
      E.obj (C.homology n)) := by
  exact ⟨(F.mapDerivedCategoryHomologyFunctorIso n).app Q ≪≫
    (DerivedCategory.homologyFunctor D n).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors D n).app _ ≪≫
    (E.mapHomologicalComplexHomologyIso (.up ℤ) n).app C⟩

private theorem finiteLocalModel_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    (e : M ≅ N) (hN : HasFiniteConstantLocalModel Λ S N) :
    HasFiniteConstantLocalModel Λ S M := by
  obtain ⟨V, hV⟩ := hN
  refine ⟨V, fun j ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hV j
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (V.f j)).mapIso e ≪≫ eP⟩⟩

private theorem constructible_of_local_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S]
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hlocal : HasFiniteConstantLocalModel Λ S M) : IsConstantModelConstructible Λ S M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  refine ⟨Scheme.Stratification.trivial S, fun _ ↦ ?_⟩
  exact finiteLocalModel_of_iso Λ S ((CondensedRing.upperStarId Λ S).app M) hlocal

/-- Every homology sheaf of a locally perfect scalar model has finite constant
models on a finite constructible stratification.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md (2), local models.
(blueprint: lem-sfb-perfect-local-model-bounded-constructible).

Proof in words:
1. Choose the cover and scalar complexes from the locally perfect hypothesis.
   The proved admissibleScalarHomologyData theorem gives finite presentation of
   their scalar homology and exactness of scalar realization on every cover member.
   Its proof includes the finite-subextension algebraic closure, identified with
   its scalar field at the point, and transport along admissibility isomorphisms.
2. Exact pullback commutes with derived homology. Compose that comparison with
   homology of the given local model isomorphism, the representative comparison,
   and exact scalar realization's homology comparison. Each restricted homology
   sheaf is therefore the realization of a finitely presented scalar module.
   The finiteConstantLocalModel_iff_exists_cover theorem converts these witnesses
   to condensed-point finite presentations, chosen before scheme restriction.
3. A locally Noetherian scheme is quasi-separated. Compactness therefore selects
   the qcqs branch of constructibility. Use the single identity stratum and
   transport the same cover and models through the identity pullback isomorphism.
   The proof needs no cohomological bound or Tor calculation and includes empty
   schemes, zero rings, rank zero, and finite-ring torsion homology. -/
theorem constructibleHomology_of_isLocallyPerfectScalarModel
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (Q : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)))
    (hQ : IsLocallyPerfectScalarModel Λ S Q) :
    ∀ n : ℤ, IsConstantModelConstructible Λ S
      ((DerivedCategory.homologyFunctor _ n).obj Q) := by
  classical
  obtain ⟨U, hU⟩ := hQ
  obtain ⟨hfp, hex⟩ := admissibleScalarHomologyData ell Λ hΛ
  intro n
  have hlocal : HasFiniteConstantLocalModel Λ S
      ((DerivedCategory.homologyFunctor _ n).obj Q) := by
    apply (finiteConstantLocalModel_iff_exists_cover Λ _).mpr
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨C, l, h, _, _, hp, ⟨e⟩⟩ := hU i
    let E := finiteConstantScalarExtension Λ (U.X i)
    have : PreservesFiniteLimits E := hex (U.X i)
    have : PreservesFiniteColimits E := scalarExtension_preservesFiniteColimits Λ (U.X i)
    have : E.Additive := scalarExtension_additive Λ (U.X i)
    refine ⟨C.homology n, hfp C hp n, ?_⟩
    exact homology_model_nonempty (CondensedRing.upperStar Λ (U.f i)) E Q C e n
  exact constructible_of_local_model Λ S _ hlocal

end AlgebraicGeometry.ProEtale
