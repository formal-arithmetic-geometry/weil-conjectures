/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink
public import Sheaf.Paper.DerivedHomMayerVietoris

/-! # Lifting a perfect stalk chain map

Source: Stacks Project, Tag 09RE, affine proof, and Tag 0BC7 (2).
(blueprint: lem-sc-perfect-open-stalk-chain-map-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

-- Retain the original interface even though affineness of U and perfectness of Q are unused.
set_option linter.unusedVariables false in
/-- An arbitrary chain map of perfect stalk complexes lifts on an affine neighbourhood.
Source: Stacks Project, Tag 09RE, affine proof's finite-presentation calculation;
Tag 0BC7 (2), chain representatives, and Tag 00CR.
(blueprint: lem-sc-perfect-open-stalk-chain-map-lift).

Proof: Extend the degreewise stalk maps by
`exists_affine_perfect_open_stalk_degreewise_lift`. The given chain map makes
their stalks commute with the differentials, by conjugating with the comparison
isomorphism. Apply `exists_affine_perfect_open_stalk_degreewise_shrink`, assemble
its components with `CochainComplex.ofHom`, and cancel the intermediate
comparison isomorphisms degreewise. The two component lemmas implement the
finite-presentation argument: only finitely many components and differential
defects have nonzero source, their germs have common representatives, and the
zero defect germs vanish on a common smaller neighbourhood. Only strict
perfectness of P is needed; the signature retains the original hypotheses on
U and Q. No inverse or quasi-isomorphism condition is required. Empty source
support and zero ranks use zero maps. -/
theorem exists_affine_perfect_open_stalk_chainMap_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (t : ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj Q) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      ∃ (e : R ⋙ S ≅ T) (g : R.obj P ⟶ R.obj Q),
        S.map g = (e.app P).hom ≫ t ≫ (e.app Q).inv := by
  clear hU hQ
  obtain ⟨W, hxW, _, hWU, eW, g, hg⟩ :=
    exists_affine_perfect_open_stalk_degreewise_lift X U x hxU P Q hP t.f
  let RW := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
  let SW := (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)
  have hcomm (n : ℤ) :
      (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
        (SW.obj (RW.obj Q)).d n (n + 1) =
      (SW.obj (RW.obj P)).d n (n + 1) ≫
        (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g (n + 1)) := by
    rw [hg n, hg (n + 1)]
    change (eW.app P).hom.f n ≫ t.f n ≫ (eW.app Q).inv.f n ≫
        (SW.obj (RW.obj Q)).d n (n + 1) = _
    exact ((eW.app P).hom ≫ t ≫ (eW.app Q).inv).comm n (n + 1)
  obtain ⟨V, hxV, hV, _, hVU, k, hk, hkg⟩ :=
    exists_affine_perfect_open_stalk_degreewise_shrink
      X U x hxU P Q hP W hxW hWU g hcomm
  -- Transport the canonical shrink coordinates to the comparison returned by the lift.
  let cW := Functor.mapHomologicalComplexCompIso
    (openModuleStalkRestrictionComparison X U W hWU x hxU hxW) (.up ℤ)
  let cV := Functor.mapHomologicalComplexCompIso
    (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
  let eV := cV ≪≫ cW.symm ≪≫ eW
  let fV := CochainComplex.ofHom k hk
  refine ⟨V, hxV, hV, hVU, eV, fV, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  change (openModuleStalkFunctor X V ⟨x, hxV⟩).map (k n) = _
  rw [hkg n, hg n]
  simp only [eV, NatIso.trans_app, Iso.trans_hom, Iso.trans_inv,
    HomologicalComplex.comp_f, Category.assoc]
  rfl

end
end AlgebraicGeometry.Scheme
