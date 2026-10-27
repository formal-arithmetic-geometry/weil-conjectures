module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Precoverage

/-! # Fppf presentations and restriction of quotient stacks

Source: Stacks Project, algebraic.tex, Tag 04WY; spaces-groupoids.tex,
Tags 04M9, 046S and 046T (blueprint: lem-sfb-fppf-groupoid-stack-presentations).

The existing quotient-presentation interface specifies the stackification up to
compatible equivalence. The comparison maps below retain their action on arrows,
so that the equivalences are the canonical ones induced by the groupoids.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

namespace CategoryTheory

/-- Clause (1): a flat locally finitely presented space groupoid gives a representable
surjective flat locally finitely presented object map and a representable diagonal.
The comparison to the self two-fibre product uses exactly the presentation's arrow map;
its two projections are therefore the supplied source and target maps.
Source: Stacks 04M9, 04WZ and 04X0
(blueprint: lem-sfb-fppf-groupoid-stack-presentations).

Proof (step 1 of the node): apply lem-sfb-flat-groupoid-algebraic-quotient to the
specified groupoid and its flat locally finitely presented projections. It gives the
representable diagonal and the representable surjective flat locally finitely presented
object map. The arrow comparison is the equivalence of 04M9, sending r to its source,
target and specified isomorphism; its projections are s and t. The stronger theorem's
smooth-atlas conclusion is not used. -/
theorem fppf_groupoid_stack_presentation
    {S : Scheme.{u}} {U R : AlgebraicSpace S} (s t : R ⟶ U)
    (e : U.obj.obj ⟶ R.obj.obj) (i : R.obj.obj ⟶ R.obj.obj)
    (c : pullback s.hom.hom t.hom.hom ⟶ R.obj.obj)
    (F : BasedCategory.{v, w} (Over S)) (a : BasedFunctor (discreteModuli U.obj.obj) F)
    (P : SpaceGroupoidQuotientPresentation s.hom.hom t.hom.hom e i c F a)
    (hs : MapIsFlat s) (ht : MapIsFlat t)
    (hsfp : MapIsLocallyOfFinitePresentation s) (htfp : MapIsLocallyOfFinitePresentation t) :
    HasAlgebraicSpaceDiagonal F ∧ IsRepresentableByAlgebraicSpaces a ∧
      IsSurjectiveModuliMap a ∧ ModuliSpaceTest @Flat a ∧
      ModuliSpaceTest @LocallyOfFinitePresentation a ∧
      (moduliTwoFiberLift (discreteModuliMap s.hom.hom) (discreteModuliMap t.hom.hom)
        (BasedNatIso.mkNatIso P.arrows.val P.arrows.property)).toFunctor.IsEquivalence := by
  sorry

/-- Clause (2): the self-relation of a representable surjective flat locally finitely
presented scheme map to an algebraic stack presents that stack. Any quotient presentation
of that relation has a canonical equivalence to the original stack, commuting with the
scheme map and the actual arrow isomorphisms.
Source: Stacks 04WY and 04T4; fppf descent comparison 076V
(blueprint: lem-sfb-fppf-groupoid-stack-presentations).

Proof (steps 2--4 of the node): 076V makes Z an fppf stack. Apply
lem-sfb-self-relation-quotient-embedding to a, using def-trf-scheme-algebraic-space.
The relation R is an algebraic space; its operations are identity, inverse and composition
of isomorphisms. Its two projections are base changes of a and hence flat and locally of
finite presentation. For z over T, choose an etale surjective scheme chart W of U x_Z T.
The chart test lem-sfb-space-local-properties-chart-test makes W -> T flat and locally
finitely presented. It is surjective: lift each residue-field object along a after a
field extension, then lift to W after a further extension. Thus W -> T is an fppf cover.
The tautological object gives a local lift of z to U. The self-relation embedding is
fully faithful and these lifts make it locally essentially surjective; apply
lem-sfb-stack-fully-faithful-local-equivalence. Stackification's extension property gives
the comparison for any presentation, with the displayed compatibility on objects and
arrows. Full faithfulness and the same local lifts make it an equivalence. -/
theorem fppf_self_relation_stack_presentation
    {S : Scheme.{u}} (Z : BasedCategory.{v, w} (Over S))
    (hZ : IsAlgebraicModuliStack Z) (U : Over S)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) Z)
    (ha : IsRepresentableByAlgebraicSpaces a) (hasurj : IsSurjectiveModuliMap a)
    (haflat : ModuliSpaceTest @Flat a)
    (hafp : ModuliSpaceTest @LocallyOfFinitePresentation a) :
    ∃ (R : AlgebraicSpace S) (s t : R ⟶ schemeSpace U)
      (e : (yoneda.obj U) ⟶ R.obj.obj) (i : R.obj.obj ⟶ R.obj.obj)
      (c : pullback s.hom.hom t.hom.hom ⟶ R.obj.obj)
      (P : SpaceGroupoidQuotientPresentation s.hom.hom t.hom.hom e i c Z a),
      MapIsFlat s ∧ MapIsFlat t ∧
      MapIsLocallyOfFinitePresentation s ∧ MapIsLocallyOfFinitePresentation t ∧
      (moduliTwoFiberLift (discreteModuliMap s.hom.hom) (discreteModuliMap t.hom.hom)
        (BasedNatIso.mkNatIso P.arrows.val P.arrows.property)).toFunctor.IsEquivalence ∧
      ∀ (F : BasedCategory.{v', w'} (Over S))
        (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
        (Q : SpaceGroupoidQuotientPresentation s.hom.hom t.hom.hom e i c F b),
        ∃ (H : BasedFunctor F Z) (κ : ModuliTwoIso (b.comp H) a),
          H.toFunctor.IsEquivalence ∧
          ∀ r : (discreteModuli R.obj.obj).obj,
            H.map (Q.arrows.val.hom.app r) ≫
                κ.val.hom.app ((discreteModuliMap t.hom.hom).obj r) =
              κ.val.hom.app ((discreteModuliMap s.hom.hom).obj r) ≫
                P.arrows.val.hom.app r := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- Clause (3): restriction along a surjective flat locally finitely presented scheme
map preserves the quotient stack. The Cartesian square is exactly
R = (U x_S U) x_(V x_S V) Q. All operations and the quotient arrow maps are retained.
No flatness or finite-presentation assumption is imposed on either groupoid's projections.
Source: Stacks 046S and 046T
(blueprint: lem-sfb-fppf-groupoid-stack-presentations).

Proof (steps 5--7 of the node): the groupoid morphism extends to a map of
stackifications by lem-sfb-groupoid-stackification-local-description, with the indicated
object and arrow compatibility. The restriction square identifies the two arrow presheaves
for objects lifted from U. These are algebraic spaces by
lem-trf-space-fibre-products-etale-covers and hence fppf sheaves. Their sheafifications
are their Isom sheaves; def-weil-pbc-sheafification fixes them. For arbitrary objects,
use a common fppf covering to lift both to U. Conjugation reduces the Isom comparison
to the preceding one. Injectivity is sheaf uniqueness; local inverse images agree on
overlaps by injectivity and glue by the sheaf axiom. This proves full faithfulness.
Every target object lifts locally to V; pulling back the fppf cover q along that lift
is still an fppf cover by lem-trf-fppf-covering-base-change. Its tautological U point
gives a local preimage. Apply lem-sfb-stack-fully-faithful-local-equivalence to these
fppf stacks. The comparison with the canonical object maps is the specified κ. -/
theorem fppf_groupoid_stack_restriction_equivalence
    {S : Scheme.{u}} (U V : Over S) (q : U ⟶ V)
    (hqsurj : Surjective q.left) (hqflat : Flat q.left)
    (hqfp : LocallyOfFinitePresentation q.left)
    (R Q : AlgebraicSpace S)
    (s t : R.obj.obj ⟶ yoneda.obj U) (e : yoneda.obj U ⟶ R.obj.obj)
    (i : R.obj.obj ⟶ R.obj.obj) (c : pullback s t ⟶ R.obj.obj)
    (s' t' : Q.obj.obj ⟶ yoneda.obj V) (e' : yoneda.obj V ⟶ Q.obj.obj)
    (i' : Q.obj.obj ⟶ Q.obj.obj) (c' : pullback s' t' ⟶ Q.obj.obj)
    (f : R.obj.obj ⟶ Q.obj.obj)
    (hs : s ≫ yoneda.map q = f ≫ s') (ht : t ≫ yoneda.map q = f ≫ t')
    (he : e ≫ f = yoneda.map q ≫ e') (hi : i ≫ f = f ≫ i')
    (hc : c ≫ f = pullback.map s t s' t' f f (yoneda.map q) hs ht ≫ c')
    (hrestrict : IsPullback (prod.lift s t) f
      (prod.map (yoneda.map q) (yoneda.map q)) (prod.lift s' t'))
    (F : BasedCategory.{v, w} (Over S)) (G : BasedCategory.{v', w'} (Over S))
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj V)) G)
    (P : SpaceGroupoidQuotientPresentation (U := schemeSpace U) s t e i c F a)
    (P' : SpaceGroupoidQuotientPresentation (U := schemeSpace V) s' t' e' i' c' G b) :
    ∃ (H : BasedFunctor F G)
      (κ : ModuliTwoIso (a.comp H) ((discreteModuliMap (yoneda.map q)).comp b)),
      H.toFunctor.IsEquivalence ∧
      ∀ (T : Over S) (x y : yoneda.obj T ⟶ yoneda.obj U)
        (r : {r : yoneda.obj T ⟶ R.obj.obj // r ≫ s = x ∧ r ≫ t = y}),
        H.map (spaceGroupoidPresentationArrow (U := schemeSpace U) (R := R)
          s t a P.arrows x y r) ≫
            κ.val.hom.app (CostructuredArrow.mk y) =
          κ.val.hom.app (CostructuredArrow.mk x) ≫
            spaceGroupoidPresentationArrow (U := schemeSpace V) (R := Q)
              s' t' b P'.arrows
              (x ≫ yoneda.map q) (y ≫ yoneda.map q)
              ⟨r.val ≫ f, by rw [Category.assoc, ← hs, ← Category.assoc, r.property.1],
                by rw [Category.assoc, ← ht, ← Category.assoc, r.property.2]⟩ := by
  sorry

end CategoryTheory
