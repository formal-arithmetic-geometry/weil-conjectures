/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Tensor from a specified finite free sheaf resolution

Source: Stacks, Tags 06YQ, 06YS, 06YP and 06YU; Modules on Sites, Section 03EK;
blueprint main-20261015, Local models in det-def-localizing-closure-ctf-equals-bc.
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules.FiniteFreeResolution

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- Finite powers are the existing categorical products, including the empty product.
Source: Stacks, Modules on Sites, Section 03EK
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor). -/
abbrev power (F : Modules R) (n : ℕ) := ∏ᶜ (fun _ : Fin n ↦ F)

/-- The existing single complex in degree zero.
Source: Stacks, Homology, Definition 0115
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor). -/
abbrev single (F : Modules R) :=
  (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj F

/-- Coordinate contraction: project the free factor and use the ordinary right unitor.
It sends z tensor (b_j) to (b_j z); no choice of a tensor comparison is made.
Source: Stacks, Modules on Sites, Section 03EK
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor). -/
def coordinateMap (N : Modules R) (n : ℕ) :
    N ⊗ power R (𝟙_ (Modules R)) n ⟶ power R N n :=
  Pi.lift (fun j ↦ (N ◁ Pi.π (fun _ : Fin n ↦ 𝟙_ (Modules R)) j) ≫ (ρ_ N).hom)

/-- The explicit finite-sum inverse to coordinate contraction.
It sends (z_j) to the sum of z_j tensor e_j.
Source: Stacks, Modules on Sites, Section 03EK
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor). -/
def coordinateInverse (N : Modules R) (n : ℕ) :
    power R N n ⟶ N ⊗ power R (𝟙_ (Modules R)) n :=
  ∑ j : Fin n, Pi.π (fun _ : Fin n ↦ N) j ≫ (ρ_ N).inv ≫
    (N ◁ Pi.ι (fun _ : Fin n ↦ 𝟙_ (Modules R)) j)

/-- Signed interchange on arbitrary resolving complexes, before localization.
Source: Stacks, following Definition 06YU, and blueprint Local models
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).

Proof (step 4 of the node): on the (p,q) summand use (-1)^(pq) times sheaf
symmetry from lem-pc-sheaf-modules-tensor-closed. The two coefficients in the
chain equation are (-1)^(pq+q) and (-1)^(pq), using the differential of
 def-pc-tensor-complex-sheaves. Swapping twice gives (-1)^(2pq)=1. The summand
formulas commute with cochain maps and induce maps on the direct sums. This
applies in particular to the resolving representatives used by the derived tensor.
-/
theorem signedInterchange :
    ∃ sigma : ∀ P L : CochainComplex (Modules R) ℤ,
        ((totalTensor R).obj P).obj L ≅ ((totalTensor R).obj L).obj P,
      (∀ (P L : CochainComplex (Modules R) ℤ) (p q : ℤ),
        CochainComplex.ιMapBifunctor P L (ordinaryTensor R) p q (p + q) rfl ≫
            (sigma P L).hom.f (p + q) =
          (p * q).negOnePow • ((β_ (P.X p) (L.X q)).hom ≫
            CochainComplex.ιMapBifunctor L P (ordinaryTensor R) q p (p + q)
              (add_comm q p))) ∧
      (∀ (P P' L L' : CochainComplex (Modules R) ℤ) (f : P ⟶ P') (g : L ⟶ L'),
        HomologicalComplex.mapBifunctorMap f g (ordinaryTensor R) (ComplexShape.up ℤ) ≫
            (sigma P' L').hom =
          (sigma P L).hom ≫
            HomologicalComplex.mapBifunctorMap g f (ordinaryTensor R) (ComplexShape.up ℤ)) := by
  sorry

variable [HasDerivedCategory.{w} (Modules R)]

/-- The specified finite free resolution computes the ordinary unbounded derived tensor,
with its actual differential and the comparison induced by the given augmentation.
The coordinate equations specify both directions, and the summand equation specifies
signed interchange. The final sectionwise clause includes locally specified matrices,
since it is quantified over every site object U. The last two clauses record the
support of the two-term case and the degree-zero complex, with the same differential.

Source: Stacks, Tags 06YQ, 06YS, 06YP, 06YU and Modules on Sites, Section 03EK;
blueprint main-20261015, det-def-localizing-closure-ctf-equals-bc, Local models
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).

Proof plan:
1. The coordinateMap is induced by balanced tensor maps on sections, via
   def-weil-presheaf-modules-sheafification and def-pur-sheaf-tensor-product.
   Its inverse is coordinateInverse: the composites are the identity by expanding
   the finite sum in the standard basis, also for rank zero.
2. Finite powers preserve kernels and cokernels in the abelian module-sheaf category
   def-weil-sheaf-of-modules-category. Thus the coordinate comparison identifies
   tensoring with each K.X i with an exact functor, giving def-pc-flat-sheaf-modules.
3. Apply lem-weil-pbc-independent-bounded-flat-kflat at the supplied upper bound.
   Essential smallness is relative to the common coefficient universe; no points enter.
4. Sheaf tensor symmetry (lem-pc-sheaf-modules-tensor-closed), multiplied by
   (-1)^(pq) on the (p,q) summand of def-pc-tensor-complex-sheaves, is a cochain
   isomorphism: the two differential coefficients are (-1)^(pq+q) and (-1)^(pq).
   Its square is the identity, and its construction commutes with all cochain maps.
5. lem-weil-pbc-kflat-fixed-tensor-triangulated gives the natural comparison c,
   normalized by lem-weil-pbc-site-derived-tensor-descent on resolving complexes.
   Invert Q epsilon using def-weil-abstract-derived-category. Compose its tensor,
   c inverse, signed interchange, and the localized coordinate cochain isomorphism.
6. In Tot(N[0] tensor K) only (0,i) survives in degree i. Its differential is
   1 tensor d_K. Conjugating by gamma gives delta and delta squared is zero.
   Expand a section in its finite coordinates to obtain the stated matrix formula.
   This computation commutes with restriction and does not assume N flat.
7. Zero ranks give zero terms. For support in {-1,0} this is precisely the two-term
   complex; for support in {0} the identity in degree zero gives the single complex.
-/
theorem finiteFreeResolution_tensor
    (K : CochainComplex (Modules R) ℤ) (b : ℤ)
    (hbound : ∀ i : ℤ, b < i → IsZero (K.X i))
    (rank : ℤ → ℕ) (hrank : ∀ i : ℤ, b < i → rank i = 0)
    (theta : ∀ i : ℤ, K.X i ≅ power R (𝟙_ (Modules R)) (rank i)) :
    ∃ hflat : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (K.X i),
    ∃ hK : K.IsKFlatIndependentCoefficients,
    ∃ c : (totalTensor R).obj K ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (derivedTensor R).obj (DerivedCategory.Q.obj K),
      (∀ (L : CochainComplex (Modules R) ℤ)
        (hL : L.IsKFlatIndependentCoefficients)
        (hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (L.X i)),
        c.app L = representativeIso R K L hK hL hflat hLf) ∧
      ∀ (M : Modules R) (epsilon : K ⟶ single R M) [QuasiIso epsilon] (N : Modules R),
      ∃ gamma : ∀ i : ℤ, N ⊗ K.X i ≅ power R N (rank i),
      ∃ delta : ∀ i : ℤ, power R N (rank i) ⟶ power R N (rank (i + 1)),
      ∃ sq : ∀ i : ℤ, delta i ≫ delta (i + 1) = 0,
      ∃ tau : ((totalTensor R).obj (single R N)).obj K ≅
          CochainComplex.of (fun i ↦ power R N (rank i)) delta sq,
      ∃ sigma : ((totalTensor R).obj K).obj (single R N) ≅
          ((totalTensor R).obj (single R N)).obj K,
      ∃ comparison : ((derivedTensor R).obj (DerivedCategory.Q.obj (single R M))).obj
          (DerivedCategory.Q.obj (single R N)) ≅
          DerivedCategory.Q.obj
            (CochainComplex.of (fun i ↦ power R N (rank i)) delta sq),
        (∀ i : ℤ,
          (gamma i).hom = (N ◁ (theta i).hom) ≫ coordinateMap R N (rank i) ∧
          (gamma i).inv = coordinateInverse R N (rank i) ≫ (N ◁ (theta i).inv)) ∧
        (∀ i : ℤ, delta i =
          (gamma i).inv ≫ (N ◁ K.d i (i + 1)) ≫ (gamma (i + 1)).hom) ∧
        (∀ i : ℤ,
          CochainComplex.ιMapBifunctor (single R N) K (ordinaryTensor R) 0 i i
              (zero_add i) ≫ tau.hom.f i =
            ((ordinaryTensor R).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).hom).app
                (K.X i) ≫ (gamma i).hom) ∧
        (∀ p q : ℤ,
          CochainComplex.ιMapBifunctor K (single R N) (ordinaryTensor R) p q (p + q)
              rfl ≫ sigma.hom.f (p + q) =
            (p * q).negOnePow • ((β_ (K.X p) ((single R N).X q)).hom ≫
              CochainComplex.ιMapBifunctor (single R N) K (ordinaryTensor R) q p (p + q)
                (add_comm q p))) ∧
        comparison =
          (((derivedTensor R).mapIso (asIso (DerivedCategory.Q.map epsilon))).app
            (DerivedCategory.Q.obj (single R N))).symm ≪≫
          (c.app (single R N)).symm ≪≫ DerivedCategory.Q.mapIso sigma ≪≫
          DerivedCategory.Q.mapIso tau ∧
        (∀ (i : ℤ) (U : Cᵒᵖ)
          (a : Fin (rank (i + 1)) → Fin (rank i) → R.obj.obj U),
          (∀ (x : (power R (𝟙_ (Modules R)) (rank i)).val.obj U)
              (k : Fin (rank (i + 1))),
            (Pi.π (fun _ : Fin (rank (i + 1)) ↦ 𝟙_ (Modules R)) k).val.app U
                (((theta i).inv ≫ K.d i (i + 1) ≫ (theta (i + 1)).hom).val.app U x) =
              ∑ j : Fin (rank i), a k j •
                (Pi.π (fun _ : Fin (rank i) ↦ 𝟙_ (Modules R)) j).val.app U x) →
          ∀ (z : (power R N (rank i)).val.obj U) (k : Fin (rank (i + 1))),
            (Pi.π (fun _ : Fin (rank (i + 1)) ↦ N) k).val.app U
                ((delta i).val.app U z) =
              ∑ j : Fin (rank i), a k j •
                (Pi.π (fun _ : Fin (rank i) ↦ N) j).val.app U z) ∧
        ((∀ i : ℤ, i ≠ -1 → i ≠ 0 → rank i = 0) →
          ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
            IsZero ((CochainComplex.of (fun j ↦ power R N (rank j)) delta sq).X i)) ∧
        ((∀ i : ℤ, i ≠ 0 → rank i = 0) →
          ∃ e : CochainComplex.of (fun i ↦ power R N (rank i)) delta sq ≅
              single R (power R N (rank 0)),
            e.hom.f 0 =
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (power R N (rank 0))).inv) := by
  sorry

/-- A specified short exact finite free presentation gives the augmentation of its
actual two-term complex, represented by the standard cone of f[0]. The equality
on the cone inclusion says that its degree-zero component is the specified g.
Source: Stacks, Homology, Definition 0115; blueprint Local models
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).

Proof (step 7 of the node): f followed by g is zero by exactness, hence g[0]
extends to the cone augmentation with zero shifted-source component. Its cohomology
is ker f in degree -1, coker f in degree 0, and zero elsewhere. Short exactness
makes the former zero and identifies the latter with M by g. Thus the augmentation
is a quasi-isomorphism by def-pc-quasi-iso-modules, and finiteFreeResolution_tensor
applies with the specified f and identity coordinates, including rank zero.
-/
theorem shortExact_finiteFree_augmentation
    (m n : ℕ) (M : Modules R)
    (f : power R (𝟙_ (Modules R)) m ⟶ power R (𝟙_ (Modules R)) n)
    (g : power R (𝟙_ (Modules R)) n ⟶ M) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact) :
    ∃ epsilon : CochainComplex.mappingCone
        ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f) ⟶
          single R M,
      CochainComplex.mappingCone.inr
          ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f) ≫
            epsilon =
        (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map g ∧
      QuasiIso epsilon ∧
      ∀ N : Modules R,
        Nonempty
          (((derivedTensor R).obj (DerivedCategory.Q.obj (single R M))).obj
              (DerivedCategory.Q.obj (single R N)) ≅
            DerivedCategory.Q.obj (CochainComplex.mappingCone
              ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
                (coordinateInverse R N m ≫ (N ◁ f) ≫ coordinateMap R N n)))) := by
  sorry

/-- A specified finite free isomorphism gives its specified degree-zero augmentation.
Source: Stacks, Homology, Definition 0115; blueprint Local models
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).

Proof (step 7 of the node): applying the single-complex functor to the supplied
isomorphism gives a cochain isomorphism and hence a quasi-isomorphism. The general
formula then has support {0}, and is N^r[0], including r=0.
-/
theorem finiteFree_iso_augmentation (n : ℕ) (M : Modules R)
    (e : power R (𝟙_ (Modules R)) n ≅ M) :
    QuasiIso ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map e.hom) ∧
      ∀ N : Modules R,
        Nonempty
          (((derivedTensor R).obj (DerivedCategory.Q.obj (single R M))).obj
              (DerivedCategory.Q.obj (single R N)) ≅
            DerivedCategory.Q.obj (single R (power R N n))) := by
  sorry

end SheafOfModules.FiniteFreeResolution
