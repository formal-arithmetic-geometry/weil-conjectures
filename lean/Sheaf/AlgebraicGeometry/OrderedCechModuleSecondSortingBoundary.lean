/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.OrderedCechModuleProjectionLift
public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy
import Sheaf.AlgebraicGeometry.AlternatingCechSecondSortingIdentity

/-! # The second sorting boundary for module Čech cochains

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

open Classical in
/-- The second sorting operator assembles into module-sheaf maps.
Source: Stacks Project, Tag 01FM, equation 20.23.6.2.
(blueprint: lem-pc-ordered-cech-module-second-sorting-boundary).

Proof: On an open B of X', identify the full cochains of D with sections on the
products of the W₀ using e. Apply the explicit first-repeat sum cechSecondSortingHom:
sum over the stable permutation and its first adjacent equality, inserting a copy with coefficient
sign(sigma) (-1)^a.
The intersection arrows are the unique arrows of opens with the prescribed tuple
projections. Transport the output back through e inverse. Every summand is additive.
Naturality of e and functoriality of restriction show naturality in B. For local
linearity, apply hlinear to each input coordinate; the two paths restricting a
scalar to the output intersection agree in the poset of opens. Since e is bijective,
the output coordinates determine a locally linear section map. These maps define
morphisms of module sheaves in adjacent natural degrees. Push them forward along f'
and conjugate by extendXIso in nonnegative degrees; put zero in all other degrees.
Apply cechSecondSortingIdentity on each open, using hd for the transported
differential. The categorical products of opens identify with the intersections in
SiteCechComplex, by their universal properties. The stable-sorting term is exactly
the displayed permutation sum, with prod.map giving the same unique restriction.
For the alternating term, the strict filter gives exactly hP: its ordered-coordinate transport
followed by orderedCechProjectionOpenMap is the same unique open map as the permutation transport.
Thus the boundary is stable sorting minus P.
In degree zero the incoming term vanishes in both natural and extended complexes.
For r=0 the products of section groups indexed by tuples are empty, hence zero;
no nonempty or covering assumption is used. Repeated tuples are retained by stable sorting,
including in degrees above r;
the alternating projection is zero there and the first-repeat formula still applies. -/
theorem orderedCech_module_secondSorting_boundary {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W₀ (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B ⟶ B).op a • c s)
    (P : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat) ⟶
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat))
    (hP : IsOrderedCechModuleProjection f' M W₀ D e P) :
    let L := ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat)
    ∃ H : ∀ i j : ℤ, (ComplexShape.up ℤ).Rel j i → (L.X i ⟶ L.X j),
      ∀ (p : ℕ) (B : T'.Opens) (y : Fin (p + 1) → ULift.{u} (Fin r))
        (s : Γ(L.X (p : ℤ), B)),
        orderedCechFullCoordinate f' M W₀ D e p B y
          (((Homotopy.nullHomotopicMap' H).f (p : ℤ)).app B s) =
          (∑ σ : Equiv.Perm (Fin (p + 1)),
        if cechStableSort (fun l ↦ (y l).down) σ then
          (Equiv.Perm.sign σ : ℤ) •
            M.presheaf.map (prod.map
              (Pi.lift fun l ↦ Pi.π (fun k ↦ W₀ (y k)) (σ l)) (𝟙 _)).op
                (orderedCechFullCoordinate f' M W₀ D e p B (y ∘ σ) s)
        else 0) -
          orderedCechFullCoordinate f' M W₀ D e p B y ((P.f (p : ℤ)).app B s)
        := by sorry

end AlgebraicGeometry.Scheme.Modules
