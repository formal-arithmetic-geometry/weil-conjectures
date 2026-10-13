/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # The completed affine comparison is invertible off the exceptional ideal

Source: Stacks Project, Tag 088B, proof, completed-base adjunction argument.
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-restriction-iso)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A coherent realization of the canonical comparison is invertible off the
extended exceptional ideal. Unlike the model theorem, this supplies no objects,
map, or limit isomorphisms: all are inputs and the commuting square is a hypothesis.
Source: Stacks Project, Tag 088B, proof from the flat completed-base change through
invertibility of the algebraized adjunction off V(K).
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-restriction-iso)

Proof: First reduce to the standard tensor adjunction: uniqueness of adjunctions
for the same functors relates the supplied unit to the standard unit by a natural
automorphism of tensor pullback. Absorb that automorphism in β, which stays an
isomorphism and gives the same hα equation for the standard unit.
Restrict the data to U=Spec B, and base change along B to its J(U)-adic
completion R. This map is flat and its positive ideal-power quotients agree with
those of B. Flat base change identifies pushforwards, quotient maps and adjunction
units. The quotient equation determines κ since its quotient projections are epi;
formal functions makes its inverse-limit map invertible, so the adjunction equation
determines the limit of α. Over R, algebraize the pulled-back formal source using
087W. Tensor pullback commutes with completion, and the fully faithful completion
functor on the proper source lifts β and its inverse to mutually inverse coherent
maps b and b inverse. The canonical comparison is therefore the completion of the
adjunction unit followed by pushforward of b. It is invertible off the extended
K-support because f is an isomorphism there. The displayed square identifies c
with that coherent map up to coherent isomorphisms: finite R-modules are complete
for J(U)R, and B-linear maps between them are R-linear by continuity (they preserve
J(U)^n and the B-image is dense modulo these powers). Indeed, J(U)^nR times a
module equals J(U)^n times its underlying B-module, by the finite generators of
J(U)^n. Thus eA,eD transport the
canonical realization to the supplied A,D. Quasi-coherent modules on Spec R are
fully faithfully recovered from sections, so this conjugacy holds as sheaf maps.
Restriction preserves conjugacy, proving IsIso of the restriction of c. If R=0
all modules vanish, so the conclusion still holds.
-/
theorem formalComparison_completed_affine_restriction_isIso
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) =
      (Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (hα : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward f).map (β.hom.app (op n))) :
    ∀ U : Y.affineOpens,
      let B := Γ(Y, U.1)
      let R := AdicCompletion (J.ideal U) B
      let L := (K.ideal U).map (algebraMap B R)
      let Q := Scheme.IdealSheafData.ofIdealTop
        (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      ∀ (A D : CoherentModules (Spec (CommRingCat.of R))) (c : A.obj ⟶ D.obj),
        ∀ eA : limit (G.obj ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj A.obj),
        ∀ eD : limit (((completion Y J).obj
            ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
              SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj D.obj),
          (lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1))) ≫ eD.hom =
          eA.hom ≫ (ModuleCat.restrictScalars (algebraMap B R)).map
            ((moduleSpecΓFunctor (R := CommRingCat.of R)).map c)) →
          IsIso ((Scheme.Modules.restrictFunctor
            (Scheme.Opens.ι Q.support.compl)).map c) := by sorry

end AlgebraicGeometry
