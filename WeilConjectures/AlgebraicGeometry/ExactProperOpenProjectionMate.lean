/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProductOpenTensorProjectionData

/-! # Proper/open projection mates in exact inverse-image coordinates

Source: the third step of lem-pur-product-open-tensor-projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open SheafOfModules.OpenTensorNormalization WeilConjectures.FiniteOpenProduct

namespace WeilConjectures.ProductOpenTensorProjection

/-- The proper/open projection equation, after canonical exact-pullback transport
and the identification P_k k_!N=N. This is independent of any product diagram,
compactification exchange B0, or subsequent tensor morphism d.

Source: Stacks 0F7B--0F7D and blueprint latest,
sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md,
symmetry paragraph; parent proof Step 3.
(blueprint: lem-pur-exact-proper-open-projection-mate).

Proof: apply properOpenProjectionMate to (i,v,t,k), Q and k_!N. Transport each
left-derived pullback by leftDerivedUpperStarIsoMapDerivedCategory. Naturality
of these isomorphisms moves them through tensor maps and derived direct image.
The transported properOpenTensorIso is gamma; the transported projection is
projection, by their definitions. The transported square comparison is square
for the exact pullbacks, since both are obtained by localization of the same
upperStar square and the canonical derived comparison. Compose with the inverse
open unit at N. Naturality of the projection in its second input moves this
inverse unit through projection for v. Naturality of properOpenMate moves its
tensor image to the final position. The resulting equality is exactly the one
displayed, with the original proper mate and no projection map inverted.
This uses arbitrary unbounded Q,N; an empty open gives the zero equality, and
identity opens reduce to naturality of the ordinary projection. -/
theorem exactProperOpenProjectionMate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W C Z Zb : Scheme.{u}} (i : W ⟶ C) (v : W ⟶ Z)
    (t : C ⟶ Zb) (k : Z ⟶ Zb)
    [IsOpenImmersion i] [IsOpenImmersion k] [QuasiCompact i] [QuasiCompact k]
    [IsProper v] [IsProper t] (h : i ≫ t = v ≫ k)
    (Q : FiniteD A W) (N : FiniteD A Z) :
    (gamma A k ((ProperOpenPush A v).obj Q) ((finiteShriek A k).obj N) ≫
        (finiteShriek A k).map (tensorMap A Z (𝟙 _) (openUnit A k N).inv)) ≫
      (finiteShriek A k).map (projection A v Q N) ≫
      (properOpenMate A i v t k h).app
        (tensor A W Q ((pull A v).obj N)) =
    tensorMap A Zb ((properOpenMate A i v t k h).app Q)
        (𝟙 ((finiteShriek A k).obj N)) ≫
      projection A t ((finiteShriek A i).obj Q) ((finiteShriek A k).obj N) ≫
      (ProperOpenPush A t).map
        (gamma A i Q ((pull A t).obj ((finiteShriek A k).obj N)) ≫
          (finiteShriek A i).map (tensorMap A W (𝟙 Q)
            (((square A i t v k h).app ((finiteShriek A k).obj N) ≪≫
              (pull A v).mapIso (openUnit A k N).symm).hom))) := by sorry

end WeilConjectures.ProductOpenTensorProjection
