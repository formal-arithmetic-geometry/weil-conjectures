/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Canonical affine base change of finite étale section coordinates

Source: Stacks Project, Tag 02KG, with the naturality of the affine tensor comparison.
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S) (V : (Spec (.of R)).Opens) (P : V.toScheme.FiniteEtale)

/-- The structure morphism of the cover over the thickened base open. -/
def coverToBase (n : ℕ) : cover f V P n ⟶ Limits.pullback V.ι (baseMap f n) :=
  pullback.lift (coverMap f V P n ≫ P.obj.hom) (pullback.snd _ _)
    (by simp only [Category.assoc, coverMap]; exact pullback.condition)

/-- The canonical comparison from the pulled-back finite algebra to the thickened cover's
structure sheaf. It is the adjoint of restriction of functions along `coverMap`, transported
through the commuting pushforwards. No inverse or existence witness enters its construction. -/
def pushforwardComparison (n : ℕ) :
    (Modules.pullback (pullback.fst V.ι (baseMap f n))).obj
        ((Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left)) ⟶
      (Modules.pushforward (coverToBase f V P n)).obj (Modules.unit (cover f V P n)) :=
  ((Modules.pullbackPushforwardAdjunction (pullback.fst V.ι (baseMap f n))).homEquiv _ _).symm
    ((Modules.pushforward P.obj.hom).map
        (unitToPushforwardObjUnit (coverMap f V P n).toRingCatSheafHom) ≫
      (Modules.pushforwardComp (coverMap f V P n) P.obj.hom).hom.app _ ≫
      (Modules.pushforwardCongr
        (by simp [coverToBase])).hom.app _ ≫
      (Modules.pushforwardComp (coverToBase f V P n)
        (pullback.fst V.ι (baseMap f n))).inv.app _)

/-- The inverse on sections of the canonical affine base-change comparison. -/
def liftSection (n : ℕ) (a : Γ(cover f V P n, ⊤)) :
    Γ((Modules.pullback (pullback.fst V.ι (baseMap f n))).obj
      ((Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left)), ⊤) :=
  Function.invFun ((pushforwardComparison f V P n).app ⊤) a

/-- Coordinates of a lifted section, for a specified finite free embedding of the direct image.
This construction works for any morphism into finite free, without an injectivity hypothesis. -/
def coordinates {r : ℕ}
    (α : (Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left) ⟶
      free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))
    (n : ℕ) (a : Γ(cover f V P n, ⊤)) :
    Fin r → Γ(Limits.pullback V.ι (baseMap f n), ⊤) :=
  fun i ↦ Modules.freeSectionsEquiv (ULift.{u} (Fin r))
    (((Modules.pullback (pullback.fst V.ι (baseMap f n))).map α ≫
      (Modules.pullbackFreeIso (pullback.fst V.ι (baseMap f n))
        (ULift.{u} (Fin r))).hom).app ⊤ (liftSection f V P n a)) (ULift.up i)

/-- Coordinates from the canonical finite affine base-change comparison are natural
under successive thickenings.

Source: Stacks Project, Tag 02KG, affine base change, and Tag 0EKP, restriction of the
finite free embedding to infinitesimal neighbourhoods.
(blueprint: new-sbc-finite-etale-adic-pushforward-coordinates)

Proof: The square formed by coverMap, coverToBase, P's structure map and the projection
of the thickened base is cartesian, by pasting the two defining pullback squares.
P's structure morphism is finite, hence affine. The affine base-change comparison for
its quasi-coherent structure sheaf is an isomorphism. Its composition with the
pullback-of-structure-sheaf isomorphism is exactly pushforwardComparison: both are
adjoint to restriction of functions along coverMap. Evaluation on the top open is bijective,
so liftSection is its unique inverse. For transitions, the two cartesian
squares paste; the affine tensor comparison is associative. Thus restriction along
coverTransition corresponds to pulling the section of the direct image along the
base transition. Apply the pulled-back map alpha and its finite free coordinate
projections. Pullback of the structure sheaf acts on these scalar coordinates by
appTop, giving the transition formula. No freeness, injectivity, matrix-kernel lifting,
Noetherian hypothesis, or inverse-limit comparison is needed in this argument.
Empty schemes and zero ranks use the same canonical maps. -/
theorem pushforward_coordinates_transition :
    ∀ (r : ℕ)
      (α : (Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left) ⟶
        free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))),
      (∀ (n : ℕ) (a : Γ(cover f V P (n + 1), ⊤)) (i : Fin r),
        coordinates f V P α n ((coverTransition f V P n).appTop a) i =
          (pullback.lift (pullback.fst V.ι (baseMap f n))
            (pullback.snd V.ι (baseMap f n) ≫ baseTransition f n)
            (by rw [Category.assoc, baseTransition_comp_baseMap]
                exact pullback.condition)).appTop
                  (coordinates f V P α (n + 1) a i)) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
