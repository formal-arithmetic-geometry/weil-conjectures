/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.SimplicialHomObject
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Hom objects of standard simplices and their boundaries

Source: Stacks Project, Tags 0177, 018V and 0186
(blueprint: lem-weil-pbc-simplicial-hom-object-standard-simplex).
-/

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tags 0177, 018V and 0186
(blueprint: lem-weil-pbc-simplicial-hom-object-standard-simplex).

Proof: each degree consists of finitely many monotone maps, including constant maps.
Nondegenerate maps are exactly the injections, hence occur in only finitely many degrees.
A family on the standard simplex is determined by its identity component: compatibility
forces the component at `φ` to be that component followed by `K(φ)`. Conversely these
components are compatible by functoriality (def-weil-pbc-simplicial-hom-object and
 def-weil-pbc-simplicial-object). Evaluation at the identity gives the representing bijection.
-/
theorem simplicial_hom_standard_simplex {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) :
    (∀ m : ℕ, Finite ((Δ[n] : SSet.{t}).obj (op ⦋m⦌)) ∧
      Nonempty ((Δ[n] : SSet.{t}).obj (op ⦋m⦌))) ∧
    SSet.Finite (Δ[n] : SSet.{t}) ∧
    (∀ (m : ℕ) (s : (Δ[n] : SSet.{t}).obj (op ⦋m⦌)),
      s ∈ (Δ[n] : SSet.{t}).nonDegenerate m ↔ Function.Injective s) ∧
    (∃ f : SimplicialHomFamily K (Δ[n] : SSet.{t}) (K.obj (op ⦋n⦌)),
      (∀ (m : ℕ) (s : (Δ[n] : SSet.{t}).obj (op ⦋m⦌)),
        f.val m s = K.map (SSet.stdSimplex.objEquiv s).op) ∧
      (simplicialHomFamilyFunctor K Δ[n]).IsRepresentedBy f) ∧
    (∀ (W : FormalCoproduct.{w} X.Etale) (f : SimplicialHomFamily K Δ[n] W),
      ∃! g : W ⟶ K.obj (op ⦋n⦌),
        g = f.val n (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) ∧
        ∀ (m : ℕ) (s : (Δ[n] : SSet.{t}).obj (op ⦋m⦌)),
          f.val m s = g ≫ K.map (SSet.stdSimplex.objEquiv s).op) := by
  sorry

/-- Source: Stacks Project, Tags 018V and 0186
(blueprint: lem-weil-pbc-simplicial-hom-object-standard-simplex).

Proof: in positive degree constant maps lie in the boundary, so every degree is nonempty;
its nondegenerate simplices are a subset of those of the finite standard simplex.
Restrict a boundary family to the codimension-one faces. Conversely extend a compatible
face tuple to any nonsurjective map `φ` by factoring it through a face missing from its
image (lem-weil-pbc-simplex-face-factorization). Independence of the omitted value follows
from the face identity (lem-weil-pbc-simplex-face-face-identity) and the matching equations.
Functoriality gives compatibility; restriction and extension are inverse and natural.
The matching universal property (lem-weil-pbc-simplicial-matching-object, or
lem-weil-pbc-matching-object-proper-faces) and the Hom representing property give inverse
comparison maps, and their projection equations imply uniqueness. Finally the operators
`K(φ)` give a boundary family and therefore a unique restriction morphism `ρ`.
Its composite with the comparison has projections `K(δ_i) = d_i`, exactly those of the
canonical matching map (def-weil-pbc-semi-representable-object), so they coincide.
-/
theorem simplicial_hom_boundary_matching {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) :
    (∀ m : ℕ, Finite ((SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌)) ∧
      Nonempty ((SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌))) ∧
    SSet.Finite (SSet.boundary.{t} (n + 1)).toSSet ∧
    (∀ (H : FormalCoproduct.{w} X.Etale)
      (u : SimplicialHomFamily K (SSet.boundary.{t} (n + 1)).toSSet H),
      (simplicialHomFamilyFunctor K (SSet.boundary (n + 1)).toSSet).IsRepresentedBy u →
      (∃! θ : H ≅ semiRepresentableMatchingObject K (n + 1),
        ∀ i : Fin (n + 2), θ.hom ≫
          ((fun r => match r with
            | 0 => fun i => Pi.π (fun _ : Fin 2 => K.obj (op ⦋0⦌)) i
            | r + 1 => fun i =>
              Multiequalizer.ι (SimplicialObject.matchingBoundaryIndex K r) i) :
            (r : ℕ) → Fin (r + 2) →
              (semiRepresentableMatchingObject K (r + 1) ⟶ K.obj (op ⦋r⦌))) n i =
          u.val n ((SSet.boundary.ι i).app (op ⦋n⦌)
            (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))) ∧
      (∃! ρ : K.obj (op ⦋n + 1⦌) ⟶ H,
        ∀ (m : ℕ) (s : (SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌)),
          ρ ≫ u.val m s = K.map (SSet.stdSimplex.objEquiv s.val).op) ∧
      ∀ θ : H ≅ semiRepresentableMatchingObject K (n + 1),
      (∀ i : Fin (n + 2), θ.hom ≫
          ((fun r => match r with
            | 0 => fun i => Pi.π (fun _ : Fin 2 => K.obj (op ⦋0⦌)) i
            | r + 1 => fun i =>
              Multiequalizer.ι (SimplicialObject.matchingBoundaryIndex K r) i) :
            (r : ℕ) → Fin (r + 2) →
              (semiRepresentableMatchingObject K (r + 1) ⟶ K.obj (op ⦋r⦌))) n i =
          u.val n ((SSet.boundary.ι i).app (op ⦋n⦌)
            (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))) →
      ∀ ρ : K.obj (op ⦋n + 1⦌) ⟶ H,
        (∀ (m : ℕ) (s : (SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌)),
          ρ ≫ u.val m s = K.map (SSet.stdSimplex.objEquiv s.val).op) →
        ρ ≫ θ.hom = semiRepresentableMatchingMap K (n + 1)) := by
  sorry

end AlgebraicGeometry.Scheme
