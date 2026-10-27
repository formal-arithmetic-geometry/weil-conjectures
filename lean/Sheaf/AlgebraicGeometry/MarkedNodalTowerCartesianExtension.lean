/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.TraceFormula.LocalDimensionFormula
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Cartesian extension of an equivariant marked nodal tower

Source: de Jong, Families of curves and alterations (1997), Situation 5.8,
pp. 615--616, and Theorem 5.9 proof, p. 617, final fibre-product paragraph
(blueprint: lem-sfb-marked-nodal-tower-cartesian-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Append the ordinary fibre product of a marked quasi-split nodal curve to the given
finite tower. Projection equations specify the diagonal action and the pulled-back sections.
The last boundary is the inverse image of the old boundary union the new section images.
Finiteness of function fields always refers to the canonical generic-stalk algebra.

Source: de Jong (1997), Situation 5.8, pp. 615--616, and Theorem 5.9 proof, p. 617
(blueprint: lem-sfb-marked-nodal-tower-cartesian-extension).

Proof (the nine steps of the node):
1. For each element of J use the fibre-product universal property with its action on P
   and its image's action on V. Uniqueness proves identity, multiplication and inverses.
   Use the same universal property for the section (s_j h, id).
2. Apply the arbitrary-base-change clause of lem-sfb-marked-nodal-boundary-control,
   with auxiliary closed subset empty, retaining the given D. This preserves projectivity,
   flatness, finite presentation, geometric nodal, reduced, pure-dimensional fibres,
   quasi-splitting and disjoint smooth sections. Projective properness and finite-type
   composition give finite type over F. Sections of separated morphisms are closed;
   induction makes all boundaries closed.
3. Smooth base change over B minus D gives smoothness over P minus Z_r. Dominance
   identifies the generic fibre with scalar extension of the smooth geometrically integral
   generic fibre of v; both properties persist. Integrality of W is an assumption.
4. The inverse image under pr_V of each section image is its pulled-back section image.
   Equivariance preserves their union. Induct on the boundary recursion for invariance.
   Pull back the boundary containment on V and use h inverse D contained in Z_r.
5. The projection to V is a base change of h. H-projectivity implies properness and
   quasi-compactness, so lem-pc-projective-base-change applies in its exact convention.
6. Surjectivity is preserved by base change and composition. The equivariance equations
   compose, as do the canonical generic-stalk maps between integral schemes.
7. Birationality identifies k(X) with k(C). Multiply finite spanning sets for
   k(W)/k(V) and k(V)/k(C) to obtain a finite spanning set for k(W)/k(X).
8. Apply lem-trf-h-projective-composition twice to pr_V, c and pi.
9. Identify the resulting finite projective space with the projective bundle of the
   standard finite free module by lem-trf-free-projective-bundle-base-change-space.
   Its closed immersion gives exactly IsProjectiveBundle for the composite. -/
theorem marked_nodal_tower_cartesian_extension
    (k e F : Type u) [Field k] [Field e] [Field F]
    [Algebra k e] [Algebra e F] [Algebra k F] [IsScalarTower k e F]
    [Module.Finite k e] [Module.Finite e F]
    (G : Type v) [Group G] [Finite G] (J : Type w) [Group J] [Finite J]
    (ρ : J →* G) (hρ : Function.Surjective ρ)
    (σk : G →* (k ≃+* k)) (σe : G →* (e ≃+* e)) (σF : J →* (F ≃+* F))
    (hke : ∀ (g : G) (x : k), σe g (algebraMap k e x) = algebraMap k e (σk g x))
    (heF : ∀ (j : J) (x : e), σF j (algebraMap e F x) =
      algebraMap e F (σe (ρ j) x))
    (B V : Scheme.{u}) [IsIntegral B] [IsIntegral V]
    (b : B ⟶ Spec (.of e)) (v : V ⟶ B)
    [LocallyOfFiniteType b] [QuasiCompact b]
    [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)]
    [IsHProjective v] [Flat v] [LocallyOfFinitePresentation v]
    (hnodal : HasNodalGeometricFibres v)
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ B),
      IsReduced (pullback v g) ∧ (pullback v g).IsPureDimension 1)
    [Smooth (v.fiberToSpecResidueField (genericPoint B))]
    [GeometricallyIntegral (v.fiberToSpecResidueField (genericPoint B))]
    (hquasi : HasQuasiSplitNodalFibres v)
    (σB : G →* Aut B) (σV : G →* Aut V)
    (hB : ∀ g : G, (σB g).hom ≫ b =
      b ≫ Spec.map (CommRingCat.ofHom (σe g⁻¹).toRingHom))
    (hv : ∀ g : G, (σV g).hom ≫ v = v ≫ (σB g).hom)
    (m : ℕ) (s : Fin m → (B ⟶ V)) (hs : ∀ j : Fin m, s j ≫ v = 𝟙 B)
    (hdisj : Pairwise (fun i j : Fin m ↦ Disjoint (Set.range (s i)) (Set.range (s j))))
    (hsm : ∀ j : Fin m, Set.range (s j) ⊆ (v.smoothLocus : Set V))
    (hmarks : ∀ g : G, (σV g).hom '' (⋃ j : Fin m, Set.range (s j)) =
      ⋃ j : Fin m, Set.range (s j))
    (D : Closeds B) (hD : IsNowhereDense (D : Set B))
    (hDst : ∀ g : G, (σB g).hom '' (D : Set B) = (D : Set B))
    (hvsmooth : Smooth (v ∣_ (⟨(D : Set B)ᶜ, D.isClosed.isOpen_compl⟩ : B.Opens)))
    (r : ℕ) (T : Fin (r + 1) → Scheme.{u}) [∀ i, IsIntegral (T i)]
    (q : ∀ i, T i ⟶ Spec (.of F))
    [∀ i, LocallyOfFiniteType (q i)] [∀ i, QuasiCompact (q i)]
    (e₀ : T 0 ≅ Spec (.of F)) (hq₀ : q 0 = e₀.hom)
    (f : ∀ i : Fin r, T i.succ ⟶ T i.castSucc)
    (hq : ∀ i : Fin r, f i ≫ q i.castSucc = q i.succ)
    [∀ i, IsHProjective (f i)] [∀ i, Flat (f i)]
    [∀ i, LocallyOfFinitePresentation (f i)]
    (hfnodal : ∀ i : Fin r, HasNodalGeometricFibres (f i))
    (hffibres : ∀ (i : Fin r) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ T i.castSucc),
      IsReduced (pullback (f i) g) ∧ (pullback (f i) g).IsPureDimension 1)
    (hfgeneric : ∀ i : Fin r,
      Smooth ((f i).fiberToSpecResidueField (genericPoint (T i.castSucc))) ∧
      GeometricallyIntegral ((f i).fiberToSpecResidueField (genericPoint (T i.castSucc))))
    (hfquasi : ∀ i : Fin r, HasQuasiSplitNodalFibres (f i))
    (τ : ∀ i, J →* Aut (T i))
    (hτq : ∀ (i : Fin (r + 1)) (j : J), (τ i j).hom ≫ q i =
      q i ≫ Spec.map (CommRingCat.ofHom (σF j⁻¹).toRingHom))
    (hτf : ∀ (i : Fin r) (j : J), (τ i.succ j).hom ≫ f i =
      f i ≫ (τ i.castSucc j).hom)
    (n : Fin r → ℕ) (t : ∀ i : Fin r, Fin (n i) → (T i.castSucc ⟶ T i.succ))
    (ht : ∀ (i : Fin r) (j : Fin (n i)), t i j ≫ f i = 𝟙 (T i.castSucc))
    (htdisj : ∀ i : Fin r, Pairwise (fun j l : Fin (n i) ↦
      Disjoint (Set.range (t i j)) (Set.range (t i l))))
    (htsm : ∀ (i : Fin r) (j : Fin (n i)),
      Set.range (t i j) ⊆ ((f i).smoothLocus : Set (T i.succ)))
    (htstable : ∀ (i : Fin r) (j : J),
      (τ i.succ j).hom '' (⋃ l : Fin (n i), Set.range (t i l)) =
        ⋃ l : Fin (n i), Set.range (t i l))
    (Zt : ∀ i, Closeds (T i)) (hZ₀ : (Zt 0 : Set (T 0)) = ∅)
    (hZt : ∀ i : Fin r, (Zt i.succ : Set (T i.succ)) =
      (f i) ⁻¹' (Zt i.castSucc : Set (T i.castSucc)) ∪
        ⋃ j : Fin (n i), Set.range (t i j))
    (hfsmooth : ∀ i : Fin r, Smooth ((f i) ∣_
      (⟨(Zt i.castSucc : Set (T i.castSucc))ᶜ,
        (Zt i.castSucc).isClosed.isOpen_compl⟩ : (T i.castSucc).Opens)))
    (h : T (Fin.last r) ⟶ B) [IsHProjective h] [Surjective h] [IsDominant h]
    (hh : h ≫ b = q (Fin.last r) ≫ Spec.map (CommRingCat.ofHom (algebraMap e F)))
    (hheq : ∀ j : J, (τ (Fin.last r) j).hom ≫ h = h ≫ (σB (ρ j)).hom)
    (hhD : h ⁻¹' (D : Set B) ⊆ (Zt (Fin.last r) : Set (T (Fin.last r))))
    [IsIntegral (pullback (C := Scheme.{u}) v h)]
    (hfield : @Module.Finite V.functionField (pullback (C := Scheme.{u}) v h).functionField _ _
      (Scheme.Hom.dominantFunctionFieldAlgebra (pullback.fst v h)).toModule)
    (C X : Scheme.{u}) [IsIntegral C] [IsIntegral X]
    (pC : C ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType pC] [QuasiCompact pC] [LocallyOfFiniteType pX] [QuasiCompact pX]
    (c : V ⟶ C) (π : C ⟶ X) [IsHProjective c] [Surjective c]
    [IsHProjective π] [Surjective π]
    (hck : c ≫ pC = v ≫ b ≫ Spec.map (CommRingCat.ofHom (algebraMap k e)))
    (hπk : π ≫ pX = pC)
    (σC : G →* Aut C) (σX : G →* Aut X)
    (hC : ∀ g : G, (σC g).hom ≫ pC =
      pC ≫ Spec.map (CommRingCat.ofHom (σk g⁻¹).toRingHom))
    (hX : ∀ g : G, (σX g).hom ≫ pX =
      pX ≫ Spec.map (CommRingCat.ofHom (σk g⁻¹).toRingHom))
    (hceq : ∀ g : G, (σV g).hom ≫ c = c ≫ (σC g).hom)
    (hπeq : ∀ g : G, (σC g).hom ≫ π = π ≫ (σX g).hom)
    (Z : Closeds X) (hZ : ∀ g : G, (σX g).hom '' (Z : Set X) = (Z : Set X))
    (hcontain : (c ≫ π) ⁻¹' (Z : Set X) ⊆
      v ⁻¹' (D : Set B) ∪ ⋃ j : Fin m, Set.range (s j))
    (hcfield : @Module.Finite C.functionField V.functionField _ _
      (Scheme.Hom.dominantFunctionFieldAlgebra c).toModule)
    (hbirational : ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (π ∣_ U)) :
    IsHProjective (pullback.snd v h) ∧ Flat (pullback.snd v h) ∧
    ∃ hfp : LocallyOfFinitePresentation (pullback.snd v h),
      QuasiCompact (pullback.snd v h) ∧ QuasiSeparated (pullback.snd v h) ∧
      @HasNodalGeometricFibres _ _ (pullback.snd v h) hfp ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (g : Spec (.of Ω) ⟶ T (Fin.last r)),
        IsReduced (pullback (pullback.snd v h) g) ∧
          (pullback (pullback.snd v h) g).IsPureDimension 1) ∧
      HasQuasiSplitNodalFibres (pullback.snd v h) ∧
      Smooth ((pullback.snd v h).fiberToSpecResidueField (genericPoint (T (Fin.last r)))) ∧
      GeometricallyIntegral
        ((pullback.snd v h).fiberToSpecResidueField (genericPoint (T (Fin.last r)))) ∧
      LocallyOfFiniteType (pullback.snd v h ≫ q (Fin.last r)) ∧
      QuasiCompact (pullback.snd v h ≫ q (Fin.last r)) ∧
      Smooth ((pullback.snd v h) ∣_ (⟨(Zt (Fin.last r) : Set (T (Fin.last r)))ᶜ,
        (Zt (Fin.last r)).isClosed.isOpen_compl⟩ : (T (Fin.last r)).Opens)) ∧
      ∃ (τW : J →* Aut (pullback (C := Scheme.{u}) v h))
        (s' : Fin m → (T (Fin.last r) ⟶ pullback (C := Scheme.{u}) v h)),
        (∀ j : J, (τW j).hom ≫ pullback.fst v h =
          pullback.fst v h ≫ (σV (ρ j)).hom) ∧
        (∀ j : J, (τW j).hom ≫ pullback.snd v h =
          pullback.snd v h ≫ (τ (Fin.last r) j).hom) ∧
        (∀ j : J, (τW j).hom ≫ pullback.snd v h ≫ q (Fin.last r) =
          (pullback.snd v h ≫ q (Fin.last r)) ≫
            Spec.map (CommRingCat.ofHom (σF j⁻¹).toRingHom)) ∧
        (∀ j : Fin m, s' j ≫ pullback.fst v h = h ≫ s j) ∧
        (∀ j : Fin m, s' j ≫ pullback.snd v h = 𝟙 (T (Fin.last r))) ∧
        Pairwise (fun i j : Fin m ↦ Disjoint (Set.range (s' i)) (Set.range (s' j))) ∧
        (∀ j : Fin m, Set.range (s' j) ⊆
          (@Scheme.Hom.smoothLocus _ _ (pullback.snd v h) hfp :
            Set (pullback (C := Scheme.{u}) v h))) ∧
        (∀ j : J, (τW j).hom '' (⋃ l : Fin m, Set.range (s' l)) =
          ⋃ l : Fin m, Set.range (s' l)) ∧
        (∀ (i : Fin (r + 1)) (j : J),
          (τ i j).hom '' (Zt i : Set (T i)) = (Zt i : Set (T i))) ∧
        ∃ Z' : Closeds (pullback (C := Scheme.{u}) v h),
          (Z' : Set (pullback (C := Scheme.{u}) v h)) =
            (pullback.snd v h) ⁻¹' (Zt (Fin.last r) : Set (T (Fin.last r))) ∪
              ⋃ j : Fin m, Set.range (s' j) ∧
          (∀ j : J, (τW j).hom '' (Z' : Set (pullback (C := Scheme.{u}) v h)) =
            (Z' : Set (pullback (C := Scheme.{u}) v h))) ∧
          (pullback.fst v h ≫ c ≫ π) ⁻¹' (Z : Set X) ⊆ (Z' : Set (pullback (C := Scheme.{u}) v h)) ∧
          (∀ j : J, (τW j).hom ≫ pullback.fst v h ≫ c ≫ π =
            (pullback.fst v h ≫ c ≫ π) ≫ (σX (ρ j)).hom) ∧
          IsHProjective (pullback.fst v h ≫ c ≫ π) ∧
          Surjective (pullback.fst v h ≫ c ≫ π) ∧
          @Module.Finite X.functionField (pullback (C := Scheme.{u}) v h).functionField _ _
            (Scheme.Hom.dominantFunctionFieldAlgebra (pullback.fst v h ≫ c ≫ π)).toModule ∧
          IsProjectiveBundle (pullback.fst v h ≫ c ≫ π) := by
  sorry

end AlgebraicGeometry
