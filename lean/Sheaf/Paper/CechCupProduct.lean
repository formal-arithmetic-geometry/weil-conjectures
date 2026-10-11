/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.ModuleCohomologyCupProduct

/-! # The Cech cup product

Source: Stacks Project, Cohomology, Tag 07MB
(blueprint: def-sc-cech-cup-product).
For coefficient sheaves in degree zero the total-complex sign is +1 on each
Alexander--Whitney component; the differential still has the signed Leibniz rule.
-/

@[expose] public section

universe uC
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The front face of a tuple for the Alexander--Whitney product.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def cupFront (p q : ℕ) : Fin (p + 1) → Fin (p + q + 1) :=
  fun i ↦ ⟨i.val, by omega⟩

/-- The back face, sharing the vertex of index p with the front face.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def cupBack (p q : ℕ) : Fin (q + 1) → Fin (p + q + 1) :=
  fun j ↦ ⟨p + j.val, by omega⟩

/-- Restriction to a face intersection; tuples may have repeated indices.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def cupFaceRestriction {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    {n m : ℕ} (y : Fin n → ι) (face : Fin m → Fin n) :
    (⨅ i, U (y i)) ⟶ (⨅ j, U (y (face j))) :=
  homOfLE (le_iInf fun j ↦ iInf_le (fun i ↦ U (y i)) (face j))

/-- The cochain cup product: restrict the front and back factors to the common
intersection and tensor their sections. For sheaves in degree zero this is precisely
the component of the signed total tensor map of Tag 07MB.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def cechCupCochain {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).X (p + q) :=
  (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (F ⊗ G).presheafModuleCat (p + q)).symm
    (fun y ↦ tmulSection
      (F.presheaf.map (cupFaceRestriction U y (cupFront p q)).op
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat p a
          (y ∘ cupFront p q)))
      (G.presheaf.map (cupFaceRestriction U y (cupBack p q)).op
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U G.presheafModuleCat q b
          (y ∘ cupBack p q))))

/-- The signed Leibniz identity makes the cochain pairing a map out of the total
 tensor complex. In degree zero the sign on the second differential is +1.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product).
Proof: expand the alternating restriction differential. Faces lying entirely in the
front or back factors give the two displayed terms; the shared-vertex terms cancel.
The remaining back terms have the sign (-1)^p. Restriction commutes with tensor
sections, so this calculation is valid on every intersection. -/
theorem cechCupCochain_leibniz {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).d
        (p + q) (p + q + 1) (cechCupCochain U F G p q a b) =
      (eqToHom (congrArg
        (fun n ↦ ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).X n)
        (Nat.add_right_comm p 1 q)))
          (cechCupCochain U F G (p + 1) q
            (((cechComplexFunctor U).obj F.presheafModuleCat).d p (p + 1) a) b) +
      (-1 : ℤ) ^ p • (eqToHom (congrArg
        (fun n ↦ ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).X n)
        (Nat.add_assoc p q 1).symm))
          (cechCupCochain U F G p (q + 1) a
            (((cechComplexFunctor U).obj G.presheafModuleCat).d q (q + 1) b)) := by
  sorry

/-- The induced bilinear product on Cech cohomology is fixed by its values on cocycles,
using the explicit Alexander--Whitney formula, rather than arbitrary unary maps.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def IsCechCupProduct {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ)
    (cup : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q)) : Prop :=
  ∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K),
    c.val = cechCupCochain U F G p q a.val b.val →
      cup (cupCycleClass _ p a) (cupCycleClass _ q b) = cupCycleClass _ (p + q) c

/-- The cochain cup product descends uniquely to a bilinear map on Cech cohomology.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product).
Proof: expand the alternating restriction differential of the front/back formula.
The interior omitted-vertex terms cancel in pairs, giving
 d(a cup b) = d(a) cup b + (-1)^p a cup d(b).
Thus products of cocycles are cocycles. The same equation shows that a product with
a boundary is a boundary. Section tensor is bilinear over global sections, so the
formula descends to the two quotient modules. Every cohomology class is represented
by a cocycle, which gives uniqueness. This holds for every index set, without a
cover condition or finiteness assumption. -/
theorem exists_unique_cechCupProduct {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ) :
    ∃! cup : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q),
      IsCechCupProduct U F G p q cup := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
