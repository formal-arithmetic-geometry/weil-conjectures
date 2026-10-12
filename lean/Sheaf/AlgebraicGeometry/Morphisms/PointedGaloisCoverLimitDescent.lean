/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import Sheaf.AlgebraicGeometry.DescendFinite
import Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of a pointed finite torsor along affine inverse limits

Source: Stacks Project, Tags 0EZJ, 0BTV and 01ZM.
(blueprint: lem-sbc-pointed-galois-cover-limit-descent)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Descend a finite torsor and a point above a compatible section. The two inverse
systems need only be qcqs with affine transitions, and need not be Noetherian or normal.

Source: Stacks Project, Tag 0EZJ, last paragraph of the limit reduction; Lemma 58.14.1
(Tag 0BTV) and finite-presentation descent (Tag 01ZM).
(blueprint: lem-sbc-pointed-galois-cover-limit-descent)

Proof:
First reindex the small cofiltered category by a coinitial directed poset. Limits
and affine-transition hypotheses are preserved. A stage found there maps to an
object of I, giving the required stage in the original system.
1. A finite étale cover is of finite presentation. Descend its underlying scheme and
   structure map along D. Increase the stage so that the descended map is finite,
   étale and surjective. Finiteness and étaleness descend for finitely presented maps.
   Surjectivity follows after increasing the stage because the image of a finite
   étale map is clopen and its complement has empty pullback to the limit. These
   complements form a qcqs affine-transition inverse system. If every complement
   were nonempty, compactness for inverse limits would make its limit nonempty;
   hence some complement is empty.
2. Descend the finitely many action maps and the finitely many equations for the unit,
   multiplication, and compatibility with the projection. The torsor comparison map
   from the finite coproduct to the fibre square descends as well. Descend its inverse
   and the two inverse equations by full faithfulness at sufficiently large stages.
   This gives a GaloisCover Z₀ at a stage i, together with a cartesian comparison χ.
3. Pull Z₀ back along s at that stage. The point z at the limit lifts to a section of
   this pullback, because z ≫ Z.π = sη and sη is compatible with the two cones. The
   pullback cover is finite étale, hence finitely presented, over K at that stage.
   Finite-presentation descent of morphisms along K descends this section at a later
   stage, including its equality with the identity on K. Base change Z₀ to the same
   later stage of D. Naturality of s identifies its pullback to K with the pullback
   used to descend the section. Composing the descended section with the projection
   to the cover gives z₀ and z₀ ≫ Z₀.π = s.app i. Pasting the two cartesian comparison
   squares preserves the required pullback with the original cover. -/
theorem GaloisCover.exists_pointed_stage_of_affine_limits
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D K : I ⥤ Scheme.{u})
    (hDqc : ∀ i, CompactSpace (D.obj i)) (hDqs : ∀ i, QuasiSeparatedSpace (D.obj i))
    (hKqc : ∀ i, CompactSpace (K.obj i)) (hKqs : ∀ i, QuasiSeparatedSpace (K.obj i))
    (hDa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f))
    (hKa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (K.map f))
    {X T : Scheme.{u}} (κ : (Functor.const I).obj X ⟶ D)
    (b : (Functor.const I).obj T ⟶ K)
    (hκ : IsLimit (Cone.mk X κ)) (hb : IsLimit (Cone.mk T b))
    (s : K ⟶ D) (sη : T ⟶ X) (hs : ∀ i, sη ≫ κ.app i = b.app i ≫ s.app i)
    (G : Type (u + 1)) [Group G] [Finite G] (Z : GaloisCover G X)
    (hZ : ∃ z : T ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (i : I) (Z₀ : GaloisCover G (D.obj i)) (χ : Z.P ⟶ Z₀.P),
      IsPullback χ Z.π Z₀.π (κ.app i) ∧
      ∃ z₀ : K.obj i ⟶ Z₀.P, z₀ ≫ Z₀.π = s.app i := by sorry

end AlgebraicGeometry.Scheme
