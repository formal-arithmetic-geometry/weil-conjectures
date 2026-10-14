/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # The cartesian open square commutes with pullback Hom transport

Source: Stacks Project, Cohomology, Tag 0D5S; perfect.tex, Tag 09RE.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Open restriction commutes with transport along any morphism over the base.
Source: Stacks Project, Cohomology, Tag 0D5S; perfect.tex, Tag 09RE.
(blueprint: lem-pc-perfect-hom-open-transport-square).

Proof: Substitute the supplied equations for κ. The two composites of cartesian
arrows from B x_S T' to Y x_S T agree:
check their first and second projections using pullback.hom_ext. Paste the
counit-pinned composition comparisons for these arrows and their projections.
The associativity equation of exists_derivedPullbackComposition equates the two
pasted comparisons; naturality of sigma, the mate of the identity on the open
right adjoint, equates their final whiskered factors. Apply both comparisons at
M and Q. Pullback of f is natural with respect to their components. Expanding
the two conjugated Hom maps, cancel adjacent inverse and forward components.
The remaining composites are the two sides below. This is an identity of the
canonical maps and does not assert bijectivity of pullback. It remains valid
for empty opens, identity arrows and zero objects. -/
theorem perfect_hom_open_transport_square
    {S Y : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    {T T' : Over S} (g : T' ⟶ T) (M Q : schemeDerivedCategory Y)
    (f : (derivedPullback (pullback.fst s T.hom)).obj M ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    let b (r : Over S) :=
      pullback.map (B.ι ≫ s) r.hom s r.hom B.ι (𝟙 r.left) (𝟙 S) (by simp) (by simp)
    let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
      (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
    let he (r : Over S) :
        b r ≫ pullback.fst s r.hom = pullback.fst (B.ι ≫ s) r.hom ≫ B.ι := by
      simp [b, pullback.map]
    let κ₀ (r : Over S) := perfectHomComposition (b r) (pullback.fst s r.hom) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) (he r)) ≪≫
      (perfectHomComposition (pullback.fst (B.ι ≫ s) r.hom) B.ι).symm ≪≫
      Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r.hom))
    ∀ κ : (r : Over S) →
        derivedPullback (pullback.fst s r.hom) ⋙ derivedPullback (b r) ≅
          schemeMVDerivedRestriction Y B ⋙ derivedPullback (pullback.fst (B.ι ≫ s) r.hom),
      (∀ r, κ r = κ₀ r) →
    (κ T').inv.app M ≫ (derivedPullback (b T')).map (perfectHomMap s g f) ≫
        (κ T').hom.app Q =
      perfectHomMap (B.ι ≫ s) g
        ((κ T).inv.app M ≫ (derivedPullback (b T)).map f ≫ (κ T).hom.app Q) := by sorry

end
end AlgebraicGeometry
