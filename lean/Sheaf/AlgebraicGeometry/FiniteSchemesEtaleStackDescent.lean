module

public import Sheaf.AlgebraicGeometry.FiniteStackDescentData
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import Sheaf.AlgebraicGeometry.RelativeSpecBaseChange
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import Sheaf.AlgebraicGeometry.RepresentableFiniteStackProperties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # Effective descent of finite schemes on an étale stack presentation

Source: Stacks Project, Descent, Tags 0245 and 02LA; Sheaves on Algebraic Stacks,
Tag 06WV(1),(5) (blueprint: lem-sfb-finite-schemes-etale-stack-descent).

The equivalence uses relative-section presheaves and the canonical restriction functor.
The final clauses identify this encoding with arbitrary finite representable maps
and all their morphisms modulo the specified 2-isomorphism over the target.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry Opposite

namespace CategoryTheory

/-- Finite schemes with a cocycle on a surjective étale atlas descend effectively,
including all compatible morphisms. Their sources are DM; a normal input gives a
normal étale scheme atlas of the descended source. No normality of the base stack
is assumed. The relative-section encoding represents every finite representable
map and identifies all maps up to 2-isomorphism over the target.

Source: Stacks 0245, 02LA, and 06WV(1),(5)
(blueprint: lem-sfb-finite-schemes-etale-stack-descent).

Proof:
1. For a finite scheme b:Z → T, take the quasi-coherent algebra b_* O_Z using
`lem-weil-pbc-affine-morphism-relative-spec`. Relative-spectrum base change
(`lem-weil-pbc-relative-spec-base-change`) converts the overlap isomorphism theta
into theta-sharp in the opposite direction. Its inverse delta has the usual
module cocycle delta23 delta12 = delta13. This is checked on scheme charts of
the algebraic-space overlap, without assuming that the overlap is a scheme.
2. Descend this cartesian quasi-coherent module by
`lem-sfb-qcoh-presentation-tensor-equivalence`, retaining its atlas identification
and the tensor and unit comparisons.
3. Fullness descends the multiplication and unit. Faithfulness checks associativity,
both unit laws and commutativity after restriction to T. This gives an actual
cartesian commutative algebra A, not an arbitrary choice of a finite covering.
4. At an object x over U construct P_x = Spec_U A_x. Its sections form the
presheaf P, and its total groupoid is explicitly `stackSectionTotal P`. Algebra
pullback and relative-spectrum base change give its restriction maps and coherence.
5. Over every test x, the relative fibre is represented by P_x: an object with
its comparison to x is exactly a section of P_x. The arrows preserving this
comparison are unique. `lem-sfb-representable-fibred-category-stack` makes this
total groupoid a stack, since the target is a stack and all these fibres are schemes.
6. Over the atlas the algebra identification gives P_a ≅ Z. Its transport is
theta, since its algebra map is delta inverse = theta-sharp, and the affine-algebra
functor is faithful. Thus the entire given datum is recovered.
7. For a test U → X, refine the algebraic space U ×_X T by étale scheme charts U_i.
They cover U étale and identify P_x over U_i with Z ×_T U_i, which is finite by
`lem-trf-finite-radicial-basechange`. The family is fpqc by
`lem-weil-pbc-fpqc-finer-than-etale` (on U's small étale site). Finiteness descends
by `lem-weil-pbc-fpqc-descend-finite`. The original atlas need not be quasi-compact.
8. A compatible scheme map reverses to an algebra map. Module descent's fullness
descends it; faithfulness checks its algebra laws and gives uniqueness. Spectrum
then supplies the natural map of section presheaves, including noninvertible maps.
9. Conversely, for any representable finite q:Y → X, take the structure algebras
of its actual finite scheme fibres. Their affine base-change identifications form
a cartesian algebra, recovered by descent from the atlas. A y over U gives its
section (y,id), while a relative-fibre section (y,alpha:q(y) ≅ x) gives y with
that comparison. These operations are inverse up to their specified comparisons,
commute with restriction and identify arrows modulo 2-isomorphism over X. This
also proves the final unique-natural-transformation clause, including its triangle.
10. Apply `lem-sfb-representable-finite-stack-properties` to obtain the DM conclusion.
The recovered Z → Y is the pullback of the original atlas: its base changes are
U ×_X T → U, hence it is a surjective étale atlas. If every stalk of Z is an
integrally closed domain, this is the required normal atlas. Empty Z, a nonnormal
X and arbitrary noninvertible compatible maps are all permitted. -/
theorem finiteSchemes_etale_stack_descent (S : Scheme.{u})
    (X : BasedCategory.{v, w} (Over S)) (hX : IsDeligneMumfordModuliStack X)
    (T : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj T)) X)
    (ha : IsEtaleModuliAtlas a) :
    (finiteStackRestriction a).IsEquivalence ∧
    (∀ P : FiniteStackSections X,
      IsDeligneMumfordModuliStack (stackSectionTotal P.obj) ∧
      IsRepresentableFiniteModuliMap (stackSectionProjection P.obj) ∧
      (∀ (Z : Over S) (p : Z ⟶ T), IsFinite p.left →
        Nonempty (a.toFunctor.op ⋙ P.obj ≅ finiteSchemeSections p) →
        (∀ z : Z.left, IsDomain (Z.left.presheaf.stalk z) ∧
          IsIntegrallyClosed (Z.left.presheaf.stalk z)) →
        ∃ (U : Over S)
            (b : BasedFunctor (discreteModuli (yoneda.obj U)) (stackSectionTotal P.obj)),
          IsEtaleModuliAtlas b ∧
          ∀ z : U.left, IsDomain (U.left.presheaf.stalk z) ∧
            IsIntegrallyClosed (U.left.presheaf.stalk z))) ∧
    (∀ (Y : BasedCategory.{v', w'} (Over S)) (q : BasedFunctor Y X),
      IsFibredInGroupoids Y → IsRepresentableFiniteModuliMap q →
      ∃ (P : FiniteStackSections X) (e : BasedFunctor Y (stackSectionTotal P.obj)),
        e.toFunctor.IsEquivalence ∧
        Nonempty (ModuliTwoIso (e.comp (stackSectionProjection P.obj)) q)) ∧
    (∀ (P Q : FiniteStackSections X)
        (f : BasedFunctor (stackSectionTotal P.obj) (stackSectionTotal Q.obj))
        (β : ModuliTwoIso (f.comp (stackSectionProjection Q.obj))
          (stackSectionProjection P.obj)),
      ∃! η : P.obj ⟶ Q.obj,
        ∃ γ : ModuliTwoIso f (stackSectionMap η),
          ∀ z : (stackSectionTotal P.obj).obj,
            (stackSectionProjection Q.obj).map (γ.val.hom.app z) = β.val.hom.app z) := by
  sorry

end CategoryTheory
