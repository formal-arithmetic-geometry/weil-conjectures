/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Coherence of twice-restricted coefficients

Source: Stacks Project, Tags 0D5S and 0DJ9.
(blueprint: lem-pc-single-complex-nested-coefficient-coherence).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The coefficient map obtained by restricting twice agrees with the once-restricted
map in the canonical smaller-open and pullback-pasting coordinates. No direct image,
base scheme or base-change comparison occurs in this statement.
Source: Stacks Project, cohomology.tex, Tag 0D5S (associativity of derived pullback),
and perfect.tex, Tag 0DJ9 (source-open restriction in the induction).
(blueprint: lem-pc-single-complex-nested-coefficient-coherence).

Proof: Expand phiW, phiZ and phiA using the coherent pullback comparisons c.
Naturality of c at phi moves its pullback through the target comparisons. Apply
associativity of c first along A to W to X and the map t to A, then along the two
pullback projections to X'. The pullback conditions identify the composites from
the twice-pulled-back source to X. The equations hp and hq identify its projections
in the once-pulled-back coordinates e'. The equality e.hom followed by Z.ι equals
A.ι followed by W.ι identifies the two source-coordinate compositions. Naturality
of the comparisons under these equalities moves the eqToHom factors together;
proof irrelevance identifies the transports. Inverse and forward comparisons
cancel, leaving the displayed equality. This computation uses only composition
and naturality: zero objects, empty opens and equal opens satisfy the same laws.
The isomorphisms alpha and beta are the displayed real composites, not arbitrary
witnesses chosen from an existence assertion. -/
theorem singleComplex_nested_coefficient_coherence
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (phi : (derivedPullback g').obj K ⟶ K')
    (W Z : X.Opens) (hZW : Z ≤ W)
    (e' : pullback (pullback.snd g' W.ι) (W.ι ⁻¹ᵁ Z).ι ≅ pullback g' Z.ι)
    (hp : e'.hom ≫ pullback.fst g' Z.ι =
      pullback.fst (pullback.snd g' W.ι) (W.ι ⁻¹ᵁ Z).ι ≫ pullback.fst g' W.ι)
    (hq : e'.hom ≫ pullback.snd g' Z.ι =
      pullback.snd (pullback.snd g' W.ι) (W.ι ⁻¹ᵁ Z).ι ≫
        (Scheme.Opens.isoOfLE hZW).hom) :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    let A := W.ι ⁻¹ᵁ Z
    let e := Scheme.Opens.isoOfLE hZW
    let q := pullback.snd g' W.ι
    let p := pullback.fst g' W.ι
    let t := pullback.snd q A.ι
    let r := pullback.fst q A.ι
    let KW := (derivedPullback W.ι).obj K
    let KW' := (derivedPullback p).obj K'
    let phiW := (c q W.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (c p g').inv.app K ≫ (derivedPullback p).map phi
    let phiZ := (c (pullback.snd g' Z.ι) Z.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := Z.ι)).symm) ≫
      (c (pullback.fst g' Z.ι) g').inv.app K ≫
      (derivedPullback (pullback.fst g' Z.ι)).map phi
    let phiA := (c t A.ι).hom.app KW ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj KW)
        (pullback.condition (f := q) (g := A.ι)).symm) ≫
      (c r q).inv.app KW ≫ (derivedPullback r).map phiW
    let alpha := (c e.hom Z.ι).app K ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj K)
        (Scheme.Opens.isoOfLE_hom_ι hZW)) ≪≫ (c A.ι W.ι).symm.app K
    let beta := (c e'.hom (pullback.fst g' Z.ι)).app K' ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj K') hp) ≪≫
      (c r p).symm.app K'
    (derivedPullback t).map alpha.hom ≫ phiA =
      (c t e.hom).hom.app ((derivedPullback Z.ι).obj K) ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj
        ((derivedPullback Z.ι).obj K)) hq.symm) ≫
      (c e'.hom (pullback.snd g' Z.ι)).inv.app ((derivedPullback Z.ι).obj K) ≫
      (derivedPullback e'.hom).map phiZ ≫ beta.hom := by sorry

end AlgebraicGeometry
