/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.SixFunctors.IntegralBrownAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.SixFunctors.IntegralExceptionalAffineFactorization
import Sheaf.SixFunctors.IntegralRestrictionLine
import Sheaf.SixFunctors.IntegralRestrictionClosed

/-!
# Constructibility on one affine chart of the integral Brown adjoint

Source: blueprint main-20261015, sk-thm-int-restriction, General f paragraph,
and sk-thm-int-restriction-glue.proof.md, paragraph (2).
(blueprint: lem-sfb-integral-exceptional-affine-chart).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable {X Y : Scheme.{u}}

private theorem finiteConstantLocalModel_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ T M) :
    HasFiniteConstantLocalModel Λ T N := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC a
  exact ⟨P, hP, ⟨((upperStar Λ (C.f a)).mapIso e).symm ≪≫ eP⟩⟩

private theorem finiteConstantStratified_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ T M) :
    IsFiniteConstantStratified Λ T N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_iso Λ (S.domain a)
    ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

private theorem constantModelConstructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ T M) :
    IsConstantModelConstructible Λ T N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hT
  · exact finiteConstantStratified_of_iso Λ T e hM
  · intro U hU
    exact finiteConstantStratified_of_iso Λ U.toScheme
      ((upperStar Λ U.ι).mapIso e) (hM U hU)

private theorem generators_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    {M N : Ambient Λ T} (e : M ≅ N) (hM : generators Λ T M) : generators Λ T N := by
  refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hM.1, fun n ↦ ?_⟩
  exact constantModelConstructible_of_iso Λ T
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (hM.2 n)

private theorem closedBrown_preserves (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {T Z : Scheme.{u}} [T.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ T) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification i)
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) Z K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) T
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) T).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) Z).FullSubcategory)
    (adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) T).FullSubcategory)
    (hK : generators (Profinite.padicIntegersRingObj ℓ E.val) T K.obj) :
    generators (Profinite.padicIntegersRingObj ℓ E.val) Z (G.obj K).obj := by
  obtain ⟨hAdd, hgen, hpres, hcomp⟩ := integralRestrictionClosed ℓ E k i
  let := hAdd
  obtain ⟨e⟩ := hcomp c h G adj
  exact generators_of_iso _ Z (e.app ⟨K.obj, hK⟩).symm (hpres K.obj hK)

private theorem affineBrown_preserves (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] (d : ℕ)
    (c : Compactification.BoundaryCompactification
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T))
    (h : ∀ K,
      localizing (Profinite.padicIntegersRingObj ℓ E.val) (AffineSpace (ULift.{u} (Fin d)) T) K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) T
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) T).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (AffineSpace (ULift.{u} (Fin d)) T)).FullSubcategory)
    (adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) T).FullSubcategory)
    (hK : generators (Profinite.padicIntegersRingObj ℓ E.val) T K.obj) :
    generators (Profinite.padicIntegersRingObj ℓ E.val)
      (AffineSpace (ULift.{u} (Fin d)) T) (G.obj K).obj := by
  obtain ⟨hq, hp, hr, _, _, hcomp, _, hpres⟩ :=
    IntegralRestriction.integralRestrictionLine ℓ E k T d
  obtain ⟨e⟩ := hcomp c h G ⟨adj⟩
  exact generators_of_iso _ _
    (((localizing _ _).ι).mapIso (e.app K)).symm (hpres K.obj hK)

/-- On one affine chart lying over an affine target chart, restriction of the integral
Brown adjoint of a bounded constructible object is bounded constructible.

Source: blueprint main-20261015, sk-thm-int-restriction.proof.md, General f;
sk-thm-int-restriction-glue.proof.md, paragraph (2).
(blueprint: lem-sfb-integral-exceptional-affine-chart).

Proof: The map q = f.resLE V U hUV is locally of finite type between affine schemes.
Choose finitely many generators of its map of coordinate rings. They give a surjection
from a polynomial ring and hence a closed immersion i : U -> A^d_V over V.
The schemes U, V and A^d_V are separated and of finite type over k. Their open
inclusions into X and Y are quasi-compact since X and Y are quasi-separated.
On the ordinary localizing categories, open extension by zero is left adjoint to
restriction. Composition for compact support identifies Rf_! u_! with v_! Rp_! Ri_!.
Apply the given Brown adjunction and the adjunctions for u, v, p and i to obtain,
naturally in A, Hom(A,u^* G K) = Hom(A,i^! p^! v^* K).
Yoneda gives an isomorphism between the two representing objects: the two maps
are the images of their identity maps, and naturality proves both inverse equations.
Integral inverse image preserves constructibility of v^* K. The integral affine-space
comparison identifies p^! with p^*(d)[2d] and proves constructibility of its value.
The integral closed-immersion theorem gives constructibility after i^!. Transfer
this membership across the Yoneda isomorphism. This argument is local on the one
specified chart and uses neither finite-cover gluing nor global preservation by G.
For empty U the same calculation applies; d=0 allows polynomial presentations with
no generators, and the zero complex is included throughout.
-/
theorem integralExceptionalAffineChart (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory)
    (_adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (U : X.Opens) (V : Y.Opens) (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (_hUV : U ≤ f ⁻¹ᵁ V)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory)
    (_hK : generators (Profinite.padicIntegersRingObj ℓ E.val) Y K.obj) :
    generators (Profinite.padicIntegersRingObj ℓ E.val) U.toScheme
      ((pull (Profinite.padicIntegersRingObj ℓ E.val) U.ι).obj (G.obj K).obj) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let : IsAffine U.toScheme := _hU
  let : IsAffine V.toScheme := _hV
  let : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  let : QuasiCompact U.ι := inferInstance
  let : QuasiCompact V.ι := inferInstance
  let : LocallyOfFiniteType (U.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of k)))
  let : QuasiCompact (U.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (U.ι ≫ X ↘ Spec (.of k)))
  let : IsSeparated (U.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (U.ι ≫ X ↘ Spec (.of k)))
  let : LocallyOfFiniteType (V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ Y ↘ Spec (.of k)))
  let : QuasiCompact (V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (V.ι ≫ Y ↘ Spec (.of k)))
  let : IsSeparated (V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (V.ι ≫ Y ↘ Spec (.of k)))
  obtain ⟨d, i, hi, hio, cp, hp, Gp, adjp, ci, hi', Gi, adji, _, hcomp⟩ :=
    integralExceptionalAffineFactorization ℓ E k f c h G _adj U V _hU _hV _hUV
  let := hi
  let := hio
  let : LocallyOfFiniteType
      (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) ≫
        V.toScheme ↘ Spec (.of k)))
  let : QuasiCompact (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact
      ((AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) ≫
        V.toScheme ↘ Spec (.of k)))
  let : IsSeparated (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated
      ((AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) ≫
        V.toScheme ↘ Spec (.of k)))
  obtain ⟨hKV, ⟨e⟩⟩ := hcomp K
  let KV : (localizing Λ V.toScheme).FullSubcategory :=
    ⟨(pull Λ V.ι).obj K.obj, hKV⟩
  obtain ⟨pres, φ, μ, coh⟩ := integralLocalizingCompactSupport ℓ E k
  let VS : Spaces k := ⟨Over.mk (V.toScheme ↘ Spec (.of k)),
    ⟨inferInstanceAs (IsSeparated (V.toScheme ↘ Spec (.of k))),
      inferInstanceAs (LocallyOfFiniteType (V.toScheme ↘ Spec (.of k))),
      inferInstanceAs (QuasiCompact (V.toScheme ↘ Spec (.of k)))⟩⟩
  let YS : Spaces k := ⟨Over.mk (Y ↘ Spec (.of k)),
    ⟨inferInstanceAs (IsSeparated (Y ↘ Spec (.of k))),
      inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of k))),
      inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))⟩⟩
  let vs : VS ⟶ YS := ObjectProperty.homMk (V.ι.asOver (Spec (.of k)))
  have hVgen : generators Λ V.toScheme KV.obj :=
    coh.constructible_pull vs K.obj _hK
  have hPgen := affineBrown_preserves ℓ E k V.toScheme d cp hp Gp adjp KV hVgen
  have hIgen := closedBrown_preserves ℓ E k i ci hi' Gi adji (Gp.obj KV) hPgen
  exact generators_of_iso Λ U.toScheme e.symm hIgen

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
