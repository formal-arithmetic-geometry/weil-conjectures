module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-! # Fpqc descent of universal closedness for algebraic spaces

Source: Stacks Project, Spaces Descent, Tag 041O,
lemma-descending-property-universally-closed, for a scheme target and a scheme covering
(blueprint: lem-sfb-space-fpqc-descend-universally-closed).

Universal closedness is the existing predicate using the atlas topology on field-valued
point classes after every algebraic-space base change. The cover is an fpqc family;
its members need not individually be quasi-compact.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universal closedness descends under an fpqc covering of a scheme target.
Source: Stacks Project, Spaces Descent, Tag 041O,
lemma-descending-property-universally-closed
(blueprint: lem-sfb-space-fpqc-descend-universally-closed).

Proof, following the five steps of the node:
1. The continuity assertion of lem-a1-space-affine-etale-cover, combined with the
   final-topology criterion of def-a1-space-point-topology, makes every space point map
   continuous. Thus all inverse images of closed sets below are closed.
2. For p : E -> Z, a scheme map a : U -> Z and C contained in |E|, the inverse image
   a⁻¹(p(C)) equals p_U(r⁻¹(C)). The forward inclusion lifts a pair of matching points:
   choose a field representative Spec K -> E and apply lem-a1-space-fibre-product-point
   to the two scheme sources Spec K and U. Map its lifted point into E x_Z U using
   lem-trf-space-fibre-products-etale-covers. The reverse inclusion is commutativity.
3. After any algebraic-space base change Z -> T, take closed C in |X x_T Z| and any
   representable etale scheme chart U -> Z. The schemes U_i = U x_T T_i form an fpqc
   cover by lem-weil-pbc-fpqc-covering-axioms(3). The inverse images C_i of C are closed
   by step 1. Fibre-product associativity identifies X x_T U_i -> U_i with a base
   change of f_i, so its image of C_i is closed. By step 2 that image is the inverse
   image under U_i -> U of the image A_U of the pulled-back C in U.
4. Give {0,1} the topology with opens empty, {0}, and the whole set. The function
   which is 1 on A_U and 0 elsewhere becomes continuous on each U_i. These functions
   agree on overlaps. Apply lem-sfb-set-continuous-functions-fpqc-sheaf to glue them.
   Joint surjectivity from def-weil-pbc-fpqc-covering identifies the result with the
   original function, so the complement of A_U is open. No separation property of
   this two-point space, or quasi-compactness of individual covering maps, is needed.
5. Step 2 identifies A_U with the inverse image in U of the image of C in Z. Step 4
   and the final topology of def-a1-space-point-topology show that this image is
   closed. This holds for every closed C and every algebraic-space Z -> T, which is
   precisely MapIsUniversallyClosed of def-sfb-space-morphism-properties. -/
theorem universallyClosed_of_fpqc_cover {S : Scheme.{u}} {I : Type w}
    (T : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)
    (Tᵢ : I → Over S) (g : ∀ i : I, Tᵢ i ⟶ T)
    (hcover : Presieve.ofArrows (fun i : I ↦ (Tᵢ i).left) (fun i : I ↦ (g i).left) ∈
      Scheme.fpqcPrecoverage T.left)
    (hclosed : ∀ i : I,
      MapIsUniversallyClosed (enlargedFibreProductFst
        (ObjectProperty.homMk ⟨yoneda.map (g i)⟩ : schemeSpace (Tᵢ i) ⟶ schemeSpace T)
        f)) :
    MapIsUniversallyClosed f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
