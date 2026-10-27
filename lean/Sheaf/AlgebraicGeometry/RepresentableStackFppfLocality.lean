module

public import Sheaf.AlgebraicGeometry.RepresentableSpacePropertyTest
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Fppf locality of four representable stack properties

Source: Stacks Project, stacks-properties.tex, Section 04XB, Tags 04XC and 04XD;
spaces-descent.tex, Tags 041Z, 041U, 0427 and 0421
(blueprint: lem-sfb-representable-stack-fppf-locality).

Each of the four choices of property is treated independently. Flatness and local
finite presentation of the cover are tested after scheme base change on etale charts;
no quasi-compactness assumption on that cover is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- Affine, finite type, quasi-finite and separated representable stack morphisms are
preserved by arbitrary algebraic-stack base change and detected on an fppf space cover.
The displayed space presentation retains the actual 2-fibre-product projection.
Source: Stacks Project, Tags 04XC, 04XD; Spaces Descent, Tags 041Z, 041U, 0427, 0421
(blueprint: lem-sfb-representable-stack-fppf-locality).

Proof:
1. Fix one P from the four-property list. The space four-property fppf descent lemma
   supplies its base-change stability and descent. For each scheme T → Y put
   A = T ×_Y Z and B = T ×_Y W. Representability makes A a space. B is a space
   because the diagonal of Y is representable: pull it back along the space T × W,
   using representable-pullback-over-space and space fibre products. The hypotheses
   on q make B → T surjective, flat and locally finitely presented.
2. Under arbitrary stack base change Y' → Y, every scheme test of the projection
   identifies over T with T ×_Y Z. Compose the comparison isomorphisms to forget
   the redundant Y' coordinate, and insert its prescribed image for the inverse.
   The algebraic-stack fibre-product lemma supplies algebraicity. Thus the projection
   is representable and its scheme tests inherit P.
3. Representable-pullback-over-space presents V = W ×_Y Z as a space. If f has P,
   choose an etale surjective scheme atlas U → W. The scheme-test definition gives
   P(U ×_Y Z → U). This is the pullback of V → W. The chartwise smooth-etale calculus
   makes the atlas fppf, so space-level descent proves P(V → W).
4. Conversely, reassociation gives A ×_T B ≅ V ×_W B over B: compose one of the
   comparisons to Y with the inverse of the other; reversing this is the inverse
   functor, including on compatible arrows. Base change gives P on this map from
   P(V → W). Descend along the fppf cover B → T by the space four-property lemma.
   Every scheme test of f has P. None of the other three properties is assumed.
   The covering object here is B = T ×_Y W, correcting the V/W typo in the source. -/
theorem representable_stack_fppf_locality (k : Type u) [Field k]
    (Z : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (Y : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (hZ : IsAlgebraicModuliStack Z) (hY : IsAlgebraicModuliStack Y)
    (f : BasedFunctor Z Y) (hf : IsRepresentableByAlgebraicSpaces f)
    (P : MorphismProperty (AlgebraicSpace (Spec (.of k))))
    (hP : P = @MapIsAffine (Spec (.of k)) ∨ P = @MapIsFiniteType (Spec (.of k)) ∨
      P = @MapIsQuasiFinite (Spec (.of k)) ∨ P = @MapIsSeparated (Spec (.of k)))
    (W : AlgebraicSpace (Spec (.of k))) (q : BasedFunctor (discreteModuli W.obj.obj) Y)
    (hq : ∀ (T : Over (Spec (.of k))) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
      ∃ (B : AlgebraicSpace (Spec (.of k))) (b : B.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange q T t B b ∧ SpaceMapIsSurjective B T b ∧
          ∀ (U : Over (Spec (.of k))) (a : yoneda.obj U ⟶ B.obj.obj), IsEtale a →
            Flat (yoneda.preimage (a ≫ b)).left ∧
              LocallyOfFinitePresentation (yoneda.preimage (a ≫ b)).left) :
    (∀ (Y' : BasedCategory.{v₃, w₃} (Over (Spec (.of k))))
      (_ : IsAlgebraicModuliStack Y') (g : BasedFunctor Y' Y),
      IsRepresentableByAlgebraicSpaces (moduliTwoFiberFst g f) ∧
        (ModuliAlgebraicSpaceTest P f →
          ModuliAlgebraicSpaceTest P (moduliTwoFiberFst g f))) ∧
    (∃ (V : AlgebraicSpace (Spec (.of k))) (p : V ⟶ W),
      HasSpaceTargetBaseChange f W q V p ∧ (ModuliAlgebraicSpaceTest P f ↔ P p)) := by
  sorry

end CategoryTheory
