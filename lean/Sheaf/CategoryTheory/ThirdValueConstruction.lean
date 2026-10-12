module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Yoneda
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit
import Sheaf.CategoryTheory.LeftDerivedValueMorphism
import Sheaf.CategoryTheory.TriangleMorphismCategory
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- The third denominator diagram has a stage whose map to a candidate value induces
Hom-colimit bijections. This supplies the comparison maps, rather than constructing
an essentially constant cone; the latter is the separate pro-criterion 05PY.

Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause, dualized;
Categories, initial-functor colimit comparison in Tag 0A1T.
(blueprint: lem-pur-derived-functor-triangles-05sc-third-value-core).

Proof: Extract the essential-constancy cones for the supplied values A and B at
the first two vertices. The value-morphism lemma 05SA gives a map a : A -> B. Choose a retraction
stage for B. MS2 lifts the first triangle map to a denominator square at that stage.
The common-stage factorization of the A cone and cofiltered equalization refine this
square to a stage at which the two retractions alpha and beta satisfy
alpha followed by a = F(f') followed by beta. Complete f' to a distinguished triangle;
MS6 supplies its third denominator. Complete a to a distinguished triangle (A,B,Y).
Exactness of F and TR3 extend alpha and beta to gamma : F(Z') -> Y.

Index by the cofiltered category of incoming denominator triangles of 05R9. Its
first two initial projections restrict the given cones. Apply Hom(-,W) to the
F-image triangles and take the filtered colimit of the five-term exact sequences
of abelian groups. The morphism of triangles (alpha,beta,gamma) supplies a comparison
from the five-term sequence of (A,B,Y). The outer unshifted comparisons are inverse
to the cone Hom-colimit bijections, since the cone legs followed by alpha and beta
are identities. For the shifted positions use the same bijections with W[-1] and
the shift equivalence. Exactness of filtered colimits and the five lemma give the
middle bijection induced by gamma. The third projection is initial, so its
opposite is final: the canonical map on Hom-colimits is bijective and takes the
class of gamma followed by phi at the chosen triangle to the same class at its
third denominator s. Compose these bijections for every W. This gives the stated
candidate Y, denominator s and r = gamma. No essential-constancy cone at the third
vertex, nor the original third-value theorem, is used. -/
theorem thirdValue_core
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (A B : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ A)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ B) :
    ∃ (Y : D) (s : S.Over ⊤ T.obj₃) (r : F.obj s.left ⟶ Y),
      ∀ W : D, Function.Bijective (fun φ : Y ⟶ W ↦
        (((MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F).op ⋙
          yoneda.obj W).ιColimitType (Opposite.op s) (r ≫ φ))) := by
  sorry

end CategoryTheory.Functor
