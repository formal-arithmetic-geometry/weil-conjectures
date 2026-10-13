/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource

/-! # One column step in Cartan–Eilenberg comparison

Source: Stacks Project, Tags 015H, 015I and 015K.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Extend a prescribed augmented boundary comparison through one complex degree.
The conclusion concerns just the column in degree `p` and its outgoing boundary;
no maps in other original-object columns are chosen.

Source: Stacks Project, Tags 015H, 015I and 015K, comparison construction;
(blueprint: lem-weil-pbc-ce-comparison-column-step).

Proof: Write the two short exact sequences of resolution complexes
0 → Bᵖ → Zᵖ → Hᵖ → 0 and 0 → Zᵖ → Iᵖ → Bᵠ → 0, where q = p + 1,
and the corresponding sequences for J. Evaluation in the resolution degree is
exact, so these sequences are degreewise short exact. The exact additive functor
F preserves their exactness and their augmented quasi-isomorphisms. Identify the
boundary of the single-degree augmentation with the single complex on Bᵖ(K).
The displayed equation on Kᵖ⁻¹ is the boundary augmentation equation: cancel the
epimorphism Kᵖ⁻¹ → Bᵖ(K), whose image under F is still an epimorphism.
Lift the cohomology augmentation into the injective homology column of J along
the monomorphic quasi-isomorphism from F(Hᵖ(K))[0] to the source homology column,
using the bounded-below injective lifting property of Tag 013P(2). Apply
exists_horseshoe_morphism_lift_exact_source to the boundary/cycle/homology sequence,
with the prescribed incoming boundary map and this homology map, to obtain a cycle
map. Independently lift the outgoing boundary augmentation by Tag 013P(2). Apply
the same horseshoe theorem to the cycle/object/outgoing-boundary sequence. Its
middle map is x and its chosen outgoing endpoint is c. Its augmentation equation
is the first conclusion and its outgoing endpoint equation is the fourth.
The incoming endpoint equation composed with the boundary-to-cycle inclusion is
the third conclusion. The chosen outgoing endpoint has the second augmentation
equation by its construction. Thus each endpoint is chosen once, and all squares
in the conclusion involve those same chosen maps. -/
theorem exists_cartanEilenberg_comparison_column_step
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (p q : ℤ) (hq : q = p + 1)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIcol : QuasiIso (eI.f p))
    (hIres :
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (hIout : QuasiIso
      (image.map (Arrow.homMk' (eI.f (q - 1)) (eI.f q) (eI.comm (q - 1) q))))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJcol : QuasiIso (eJ.f p))
    (hJinj : ∀ n : ℕ, Injective ((J.X p).X n))
    (hJinj' : ∀ n : ℕ,
      Injective ((J.cycles p).X n) ∧
      Injective ((image (J.d (p - 1) p)).X n) ∧
      Injective ((J.homology p).X n))
    (hJres :
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p))
    (hJout : QuasiIso
      (image.map (Arrow.homMk' (eJ.f (q - 1)) (eJ.f q) (eJ.comm (q - 1) q))))
    (hJoutInj : ∀ n : ℕ, Injective ((image (J.d (q - 1) q)).X n))
    (b : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (image (I.d (p - 1) p)) ⟶ image (J.d (p - 1) p))
    (hb : F.map
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X (p - 1))).inv ≫
          (eI.f (p - 1)).f 0 ≫ (factorThruImage (I.d (p - 1) p)).f 0) ≫ b.f 0 =
      u.f (p - 1) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X (p - 1))).inv ≫
          (eJ.f (p - 1)).f 0 ≫ (factorThruImage (J.d (p - 1) p)).f 0) :
    ∃ (x : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p) ⟶ J.X p)
      (c : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (image (I.d (q - 1) q)) ⟶ image (J.d (q - 1) q)),
      (F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
          (eI.f p).f 0) ≫ x.f 0 =
        u.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
          (eJ.f p).f 0) ∧
      (F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X (q - 1))).inv ≫
          (eI.f (q - 1)).f 0 ≫ (factorThruImage (I.d (q - 1) q)).f 0) ≫ c.f 0 =
        u.f (q - 1) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X (q - 1))).inv ≫
          (eJ.f (q - 1)).f 0 ≫ (factorThruImage (J.d (q - 1) q)).f 0) ∧
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (image.ι (I.d (p - 1) p)) ≫ x =
        b ≫ image.ι (J.d (p - 1) p) ∧
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (factorThruImage (I.d (q - 1) q)) ≫ c =
        eqToHom (congrArg
          (fun k : ℤ ↦ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X k))
          (by omega : q - 1 = p)) ≫ x ≫
        eqToHom (congrArg (fun k : ℤ ↦ J.X k) (by omega : p = q - 1)) ≫
          factorThruImage (J.d (q - 1) q) := by sorry

end CategoryTheory
