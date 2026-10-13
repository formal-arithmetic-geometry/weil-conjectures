/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde

import Sheaf.AlgebraicGeometry.FormalSystemsPullback

/-! # Affine section comparisons for coherent formal modules

Source: Stacks Project, Lemmas 087W and 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Transport coherent formal modules from an affine open to its canonical spectrum,
including the natural comparison of the underlying A-module section diagrams.
Source: Stacks Project, Lemma 087X, affine reduction, and Lemma 087W.
(blueprint: lem-weil-pbc-formal-affine-spec-transport)

Proof: Put A=Γ(X,V) and J=I(V). Use IsAffineOpen.isoSpec to identify V with Spec A.
The ideal comapped along its inverse is ofIdealTop (J.map ΓSpecIso.inv): the inverse
has top ring map V.topIso.hom followed by ΓSpecIso.inv, and extension of I to V has
top ideal J transported by V.topIso.inv. Check equality on the affine basis using
quasi-coherence. Termwise tensor pullback along the inverse isomorphism gives T.
The functor in the other direction is tensor pullback along the isomorphism, with
the ideal equality just checked. Pullback composition and identity isomorphisms
supply inverse comparisons; lift these through the fully faithful full-subcategory
inclusions to obtain the transport equivalence. At each term, pullback along this
isomorphism is restriction, whose top sections are identified by restrictAppIso.
Restrict scalars along V.topIso.inv on the V side and ΓSpecIso.inv on the Spec side.
The top-ring equation makes this an A-linear comparison. Its naturality in sheaf
maps gives both transition compatibility and naturality in formal modules; assemble
the resulting natural diagram isomorphism. Empty V and zero or unit ideals obey the
same formulas, since none of the argument requires a nonzero ring or proper ideal.
-/
theorem coherentFormalModule_affine_spec_transport
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) (V : X.affineOpens)
    [IsNoetherian V.1.toScheme] :
    letI : IsNoetherianRing Γ(X, V.1) :=
      IsLocallyNoetherian.component_noetherian V
    ∃ T : CoherentFormalModule V.1.toScheme (I.comap V.1.ι) ≌
      CoherentFormalModule (Spec (CommRingCat.of Γ(X, V.1)))
        (Scheme.IdealSheafData.ofIdealTop
          ((I.ideal V).map (Scheme.ΓSpecIso (CommRingCat.of Γ(X, V.1))).inv.hom)),
    Nonempty
      (((IsCoherentFormalModule (I.comap V.1.ι)).ι ⋙
          (Functor.whiskeringRight ℕᵒᵖ V.1.toScheme.Modules (ModuleCat Γ(X, V.1))).obj
            (SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤) ⋙
              ModuleCat.restrictScalars V.1.topIso.inv.hom)) ≅
        T.functor ⋙
          (IsCoherentFormalModule (Scheme.IdealSheafData.ofIdealTop
            ((I.ideal V).map
              (Scheme.ΓSpecIso (CommRingCat.of Γ(X, V.1))).inv.hom))).ι ⋙
          (Functor.whiskeringRight ℕᵒᵖ
            (Spec (CommRingCat.of Γ(X, V.1))).Modules (ModuleCat Γ(X, V.1))).obj
              (moduleSpecΓFunctor (R := CommRingCat.of Γ(X, V.1)))) := by sorry

end AlgebraicGeometry
