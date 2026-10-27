module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Sheaf.AlgebraicGeometry.ArtinLocalTestAlgebra

/-! # Marked lift bijections for an (RS) fibre square

Source: Stacks Project, formal-defos.tex, Tags 06JE (definition-lifts) and
06JH (remark-lift-bijections)
(blueprint: lem-sfb-rs-marked-lift-pullback-bijections).

Marked lifts are Mathlib costructured arrows. All their markings and all fibre
arrows are invertible, since the fibres are groupoids. The quotient is the
ordinary quotient by isomorphism, without a choice of representatives.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ArtinDeformation

variable {k : Type u} [Field k]

/-- A functor on marked lifts induces its actual map on isomorphism classes.
Source: Stacks, Tags 06JE and 06JH
(blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftClassesMap {F G : CofibredGroupoids.{u, v, w} k k}
    {B A B' A' : TestCategory k k} {f : B ⟶ A} {f' : B' ⟶ A'}
    {x : fibre F A} {x' : fibre G A'}
    (T : (CostructuredArrow (push F f) x) ⥤ (CostructuredArrow (push G f') x')) :
    (Quotient (isIsomorphicSetoid (CostructuredArrow (push F f) x))) → (Quotient
      (isIsomorphicSetoid (CostructuredArrow (push G f') x'))) :=
  Quotient.map T.obj (fun _ _ h ↦ h.map (fun i ↦ T.mapIso i))

/-- Restriction, including the compositor identifying f_* a_* with r_*.
On objects it sends (y,α) to (a_*y,c_{f,a}(y) ≫ α).
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftRestriction (F : CofibredGroupoids.{u, v, w} k k)
    {P B A : TestCategory k k} (a : P ⟶ B) (f : B ⟶ A) (r : P ⟶ A)
    (h : a ≫ f = r) (x : fibre F A) :
    (Quotient (isIsomorphicSetoid (CostructuredArrow (push F r) x))) → (Quotient
      (isIsomorphicSetoid (CostructuredArrow (push F f) x))) :=
  markedLiftClassesMap (CostructuredArrow.map₂
    (F := push F a) (G := 𝟭 (fibre F A))
    ((compIso F a f ≪≫ eqToIso (congrArg (push F) h) ≪≫
      (Functor.rightUnitor (push F r)).symm).hom) (𝟙 x))

/-- Restriction to the second corner with the marking through a fixed first lift.
The comparison is δ⁻¹, so the marking is δ⁻¹ ≫ p_*η ≫ α₁.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftFixedRestriction (F : CofibredGroupoids.{u, v, w} k k)
    {P A₁ A₂ A : TestCategory k k} (a₁ : P ⟶ A₁) (a₂ : P ⟶ A₂)
    (p : A₁ ⟶ A) (q : A₂ ⟶ A) (h : a₁ ≫ p = a₂ ≫ q)
    {x : fibre F A} (x₁ : (CostructuredArrow (push F p) x)) :
    (Quotient (isIsomorphicSetoid (CostructuredArrow (push F a₁) x₁.left))) → (Quotient
      (isIsomorphicSetoid (CostructuredArrow (push F q) x))) :=
  markedLiftClassesMap (CostructuredArrow.map₂
    (F := push F a₂) (G := push F p)
    ((compIso F a₂ q ≪≫ eqToIso (congrArg (push F) h.symm) ≪≫
      (compIso F a₁ p).symm).hom) x₁.hom)

/-- Change marking by a specified isomorphism of the base object.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftChange (F : CofibredGroupoids.{u, v, w} k k)
    {B A : TestCategory k k} (f : B ⟶ A) {x x' : fibre F A} (i : x ≅ x') :
    (Quotient (isIsomorphicSetoid (CostructuredArrow (push F f) x))) → (Quotient
      (isIsomorphicSetoid (CostructuredArrow (push F f) x'))) :=
  markedLiftClassesMap (CostructuredArrow.map i.hom)

/-- Transport of marked lifts along a commuting square of test arrows.
The comparison is c_{f',a} followed by c_{b,f}⁻¹; β specifies the new base marking.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftSquareMap (F : CofibredGroupoids.{u, v, w} k k)
    {B A B' A' : TestCategory k k} (f : B ⟶ A) (f' : B' ⟶ A')
    (a : B ⟶ B') (b : A ⟶ A') (h : a ≫ f' = f ≫ b)
    {x : fibre F A} {x' : fibre F A'} (β : (push F b).obj x ≅ x') :
    (Quotient (isIsomorphicSetoid (CostructuredArrow (push F f) x))) → (Quotient
      (isIsomorphicSetoid (CostructuredArrow (push F f') x'))) :=
  markedLiftClassesMap (CostructuredArrow.map₂
    (F := push F a) (G := push F b)
    ((compIso F a f' ≪≫ eqToIso (congrArg (push F) h) ≪≫
      (compIso F f b).symm).hom) β.hom)

/-- The component functor of a coherent morphism of the groupoid pseudofunctors.
Source: Stacks, Tag 06GJ (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
abbrev markedLiftComponent {F G : CofibredGroupoids.{u, v, w} k k}
    (T : Pseudofunctor.StrongTrans F.transport G.transport) (A : TestCategory k k) :
    fibre F A ⥤ fibre G A :=
  (T.app ⟨A⟩).toFunctor

/-- A coherent morphism sends (y,α) to (T_By,t_f(y) ≫ T_A(α)).
Source: Stacks, Tags 06GJ and 06JH
(blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftMorphismMap {F G : CofibredGroupoids.{u, v, w} k k}
    (T : Pseudofunctor.StrongTrans F.transport G.transport)
    {B A : TestCategory k k} (f : B ⟶ A) (x : fibre F A) :
    (Quotient (isIsomorphicSetoid (CostructuredArrow (push F f) x))) →
      (Quotient (isIsomorphicSetoid (CostructuredArrow (push G f) ((markedLiftComponent T A).obj
      x)))) :=
  markedLiftClassesMap (CostructuredArrow.map₂
    (F := markedLiftComponent T B) (G := markedLiftComponent T A)
    ((Cat.Hom.toNatIso (T.naturality f.toLoc)).inv) (𝟙 _))

end AlgebraicGeometry.ArtinDeformation

namespace AlgebraicGeometry.ArtinDeformation

/-- An actual fibre square of Artinian k-tests, with either leg surjective.
The pullback condition is on the underlying k-algebras, so P is precisely the
ring fibre product up to its unique projection-preserving isomorphism.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
structure MarkedLiftSquare (k : Type u) [Field k] where
  base : TestCategory k k
  first : TestCategory k k
  second : TestCategory k k
  product : TestCategory k k
  p : first ⟶ base
  q : second ⟶ base
  a₁ : product ⟶ first
  a₂ : product ⟶ second
  comm : a₁ ≫ p = a₂ ≫ q
  isPullback : IsPullback (CommAlgCat.ofHom (map a₁)) (CommAlgCat.ofHom (map a₂))
    (CommAlgCat.ofHom (map p)) (CommAlgCat.ofHom (map q))
  surjective : Function.Surjective (map p) ∨ Function.Surjective (map q)

variable {k : Type u} [Field k]

/-- The two restrictions of a marked lift to the two corners of a fibre square.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftPairRestriction (F : CofibredGroupoids.{u, v, w} k k)
    (S : MarkedLiftSquare k) (x : fibre F S.base) :
    (Quotient (isIsomorphicSetoid (CostructuredArrow (push F (S.a₁ ≫ S.p)) x))) →
      (Quotient (isIsomorphicSetoid (CostructuredArrow (push F S.p) x))) × (Quotient
      (isIsomorphicSetoid (CostructuredArrow (push F S.q) x))) :=
  fun z ↦ (markedLiftRestriction F S.a₁ S.p (S.a₁ ≫ S.p) rfl x z,
    markedLiftRestriction F S.a₂ S.q (S.a₁ ≫ S.p) S.comm.symm x z)

/-- The second bijection's canonical forward map for a fixed first lift.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftSecondRestriction (F : CofibredGroupoids.{u, v, w} k k)
    (S : MarkedLiftSquare k) {x : fibre F S.base} (x₁ : (CostructuredArrow (push F S.p) x)) :
    (Quotient (isIsomorphicSetoid (CostructuredArrow (push F S.a₁) x₁.left))) → (Quotient
      (isIsomorphicSetoid (CostructuredArrow (push F S.q) x))) :=
  markedLiftFixedRestriction F S.a₁ S.a₂ S.p S.q S.comm x₁

/-- A map of fibre-square diagrams, with no surjectivity condition on its four maps.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
structure MarkedLiftSquareMap (S S' : MarkedLiftSquare k) where
  base : S.base ⟶ S'.base
  first : S.first ⟶ S'.first
  second : S.second ⟶ S'.second
  product : S.product ⟶ S'.product
  first_base : first ≫ S'.p = S.p ≫ base
  second_base : second ≫ S'.q = S.q ≫ base
  product_first : product ≫ S'.a₁ = S.a₁ ≫ first
  product_second : product ≫ S'.a₂ = S.a₂ ≫ second

/-- A diagram map also commutes from its product corner to its base.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections).
Proof: associate product ≫ a₁' ≫ p', use product_first and first_base,
and reassociate to a₁ ≫ p ≫ base. -/
theorem markedLiftSquareMap_base {S S' : MarkedLiftSquare k}
    (D : MarkedLiftSquareMap S S') :
    D.product ≫ (S'.a₁ ≫ S'.p) = (S.a₁ ≫ S.p) ≫ D.base := sorry

/-- Transport a concrete marked lift through a commuting test square.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftSquareObject (F : CofibredGroupoids.{u, v, w} k k)
    {B A B' A' : TestCategory k k} (f : B ⟶ A) (f' : B' ⟶ A')
    (a : B ⟶ B') (b : A ⟶ A') (h : a ≫ f' = f ≫ b)
    {x : fibre F A} {x' : fibre F A'} (β : (push F b).obj x ≅ x')
    (y : (CostructuredArrow (push F f) x)) : (CostructuredArrow (push F f') x') :=
  (CostructuredArrow.map₂ (F := push F a) (G := push F b)
    ((compIso F a f' ≪≫ eqToIso (congrArg (push F) h) ≪≫
      (compIso F f b).symm).hom) β.hom).obj y

/-- Transport a concrete marked lift through a coherent pseudofunctor morphism.
Source: Stacks, Tags 06GJ and 06JH
(blueprint: lem-sfb-rs-marked-lift-pullback-bijections). -/
def markedLiftMorphismObject {F G : CofibredGroupoids.{u, v, w} k k}
    (T : Pseudofunctor.StrongTrans F.transport G.transport)
    {B A : TestCategory k k} (f : B ⟶ A) {x : fibre F A} (y : (CostructuredArrow (push F f) x)) :
    (CostructuredArrow (push G f) ((markedLiftComponent T A).obj x)) :=
  (CostructuredArrow.map₂
    (F := markedLiftComponent T B) (G := markedLiftComponent T A)
    ((Cat.Hom.toNatIso (T.naturality f.toLoc)).inv) (𝟙 _)).obj y

/-- Both canonical marked restriction maps are bijections for every (RS) square.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections).

Proof:
1. By lem-sfb-artin-local-test-algebra the literal ring fibre product is a test.
Identify the given pullback with it by the unique projection-preserving algebra
isomorphism. If only p is onto, exchange the two factors and invert the gluing
isomorphism. IsRimSchlessinger then makes the comparison fully faithful and
essentially surjective.
2. Write c_i : p_{i*}a_{i*} ≅ r_* and δ = c_1 ≫ c_2⁻¹. Restriction of (y,α)
is (a_{i*}y,c_i(y) ≫ α). Naturality of c_i makes marked isomorphisms restrict.
3. For two marked lifts (y_i,α_i), glue along α_1 ≫ α_2⁻¹. Essential surjectivity
gives y and v_i : a_{i*}y ≅ y_i. Give y the marking c_1⁻¹ ≫ p_*v_1 ≫ α_1;
the gluing equation identifies it with c_2⁻¹ ≫ q_*v_2 ≫ α_2. This proves onto.
4. Equality of both restricted classes supplies marked isomorphisms u_i. Their
marking equations imply δ_y ≫ q_*u_2 = p_*u_1 ≫ δ_z. Full faithfulness gives a
unique u restricting to u_i. Naturality of c_1 makes it marked, proving injectivity.
5. For fixed (x₁,α₁), restriction of (y,η) has marking δ_y⁻¹ ≫ p_*η ≫ α₁.
Glue x₁ and an arbitrary second lift as in step 3 to get surjectivity. For
injectivity combine a marked second isomorphism with η ≫ θ⁻¹ in the first
factor; full faithfulness gives the required marked isomorphism over P.
The quotient maps are therefore bijective, independently of all gluing choices. -/
theorem rs_marked_lift_pullback_bijections
    (F : CofibredGroupoids.{u, v, w} k k) (hRS : IsRimSchlessinger F)
    (S : MarkedLiftSquare k) (x : fibre F S.base) :
    Function.Bijective (markedLiftPairRestriction F S x) ∧
      ∀ x₁ : (CostructuredArrow (push F S.p) x),
        Function.Bijective (markedLiftSecondRestriction F S x₁) := sorry

end AlgebraicGeometry.ArtinDeformation

namespace AlgebraicGeometry.ArtinDeformation

variable {k : Type u} [Field k]

/-- Naturality of the first bijection under an isomorphism of the marked base.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections).
Proof: changing α to α ≫ i changes each restricted marking c_i ≫ α to
c_i ≫ α ≫ i. Associativity identifies both resulting marked objects, so the
quotient maps agree. Bijectivity gives the same identity for the inverse. -/
theorem rs_marked_lift_pair_iso
    (F : CofibredGroupoids.{u, v, w} k k) (hRS : IsRimSchlessinger F)
    (S : MarkedLiftSquare k) {x x' : fibre F S.base} (i : x ≅ x')
    (z : (Quotient (isIsomorphicSetoid (CostructuredArrow (push F (S.a₁ ≫ S.p)) x)))) :
    markedLiftPairRestriction F S x'
        (markedLiftChange F (S.a₁ ≫ S.p) i z) =
      Prod.map (markedLiftChange F S.p i) (markedLiftChange F S.q i)
        (markedLiftPairRestriction F S x z) := sorry

/-- Naturality of the second bijection under an isomorphism of marked first lifts.
Both the base isomorphism and the specified compatible first-lift isomorphism
are retained. Source: Stacks, Tag 06JH
(blueprint: lem-sfb-rs-marked-lift-pullback-bijections).
Proof: the compatibility p_*j ≫ α₁' = α₁ ≫ i changes the marking formula
δ⁻¹ ≫ p_*η ≫ α₁ into the same formula postcomposed by i when η is postcomposed
by j. Functoriality and associativity give equality on classes. The inverse
naturality follows from bijectivity. -/
theorem rs_marked_lift_second_iso
    (F : CofibredGroupoids.{u, v, w} k k) (hRS : IsRimSchlessinger F)
    (S : MarkedLiftSquare k) {x x' : fibre F S.base} (i : x ≅ x')
    (x₁ : (CostructuredArrow (push F S.p) x)) (x₁' : (CostructuredArrow (push F S.p) x'))
    (j : x₁.left ≅ x₁'.left)
    (hj : (push F S.p).map j.hom ≫ x₁'.hom = x₁.hom ≫ i.hom)
    (z : (Quotient (isIsomorphicSetoid (CostructuredArrow (push F S.a₁) x₁.left)))) :
    markedLiftSecondRestriction F S x₁' (markedLiftChange F S.a₁ j z) =
      markedLiftChange F S.q i (markedLiftSecondRestriction F S x₁ z) := sorry

/-- Naturality of the first bijection under arbitrary maps of fibre-square diagrams.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections).
Proof: for each corner, the induced marking is c_{a,f'} ≫ c_{f,b}⁻¹ ≫ b_*α ≫ β.
Apply pseudofunctor associativity to (a_i,p_i,b), (a_i,b_i,p_i') and
(d,a_i',p_i'); use the four diagram equations. These identify the corner
markings from the two routes. The intermediate objects are identified by
c_{d,a_i'} ≫ c_{a_i,b_i}⁻¹, which is a marked isomorphism. Thus both quotient
classes agree in both factors. Bijectivity gives naturality of the inverse. -/
theorem rs_marked_lift_pair_diagram
    (F : CofibredGroupoids.{u, v, w} k k) (hRS : IsRimSchlessinger F)
    {S S' : MarkedLiftSquare k} (D : MarkedLiftSquareMap S S')
    {x : fibre F S.base} {x' : fibre F S'.base}
    (β : (push F D.base).obj x ≅ x')
    (z : (Quotient (isIsomorphicSetoid (CostructuredArrow (push F (S.a₁ ≫ S.p)) x)))) :
    markedLiftPairRestriction F S' x'
        (markedLiftSquareMap F (S.a₁ ≫ S.p) (S'.a₁ ≫ S'.p)
          D.product D.base (markedLiftSquareMap_base D) β z) =
      Prod.map
        (markedLiftSquareMap F S.p S'.p D.first D.base D.first_base β)
        (markedLiftSquareMap F S.q S'.q D.second D.base D.second_base β)
        (markedLiftPairRestriction F S x z) := sorry

/-- Naturality of the second bijection under maps of fibre-square diagrams.
The target first lift is the actual transported marked object.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections).
Proof: apply the compositor identity in rs_marked_lift_pair_diagram for each
corner to the formula δ⁻¹ ≫ p_*η ≫ α₁. The first-corner comparison identifies
the transported η, and the second-corner comparison is a marked isomorphism
between the resulting lifts. Their quotient classes agree. The specified base
isomorphism β is postcomposed in both markings. Bijectivity gives inverse
naturality. No surjectivity of any component of D is used. -/
theorem rs_marked_lift_second_diagram
    (F : CofibredGroupoids.{u, v, w} k k) (hRS : IsRimSchlessinger F)
    {S S' : MarkedLiftSquare k} (D : MarkedLiftSquareMap S S')
    {x : fibre F S.base} {x' : fibre F S'.base}
    (β : (push F D.base).obj x ≅ x') (x₁ : (CostructuredArrow (push F S.p) x))
    (z : (Quotient (isIsomorphicSetoid (CostructuredArrow (push F S.a₁) x₁.left)))) :
    markedLiftSecondRestriction F S'
        (markedLiftSquareObject F S.p S'.p D.first D.base D.first_base β x₁)
        (markedLiftSquareMap F S.a₁ S'.a₁ D.product D.first D.product_first
          (Iso.refl _) z) =
      markedLiftSquareMap F S.q S'.q D.second D.base D.second_base β
        (markedLiftSecondRestriction F S x₁ z) := sorry

/-- Naturality of the first bijection under coherent pseudofunctor morphisms.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections).
Proof: write t_f : f_*^G T ≅ T f_*^F. The strong transformation composition
axiom says c_i^G ≫ t_r = p_{i*}^G(t_{a_i}) ≫ t_{p_i} ≫ T(c_i^F).
Consequently t_{a_i} identifies the two restrictions as marked objects after
applying T to α. Hence both quotient classes agree. Since both pseudofunctors
satisfy (RS), bijectivity implies naturality of the inverse bijections too. -/
theorem rs_marked_lift_pair_morphism
    (F G : CofibredGroupoids.{u, v, w} k k)
    (hF : IsRimSchlessinger F) (hG : IsRimSchlessinger G)
    (T : Pseudofunctor.StrongTrans F.transport G.transport)
    (S : MarkedLiftSquare k) (x : fibre F S.base)
    (z : (Quotient (isIsomorphicSetoid (CostructuredArrow (push F (S.a₁ ≫ S.p)) x)))) :
    markedLiftPairRestriction G S ((markedLiftComponent T S.base).obj x)
        (markedLiftMorphismMap T (S.a₁ ≫ S.p) x z) =
      Prod.map (markedLiftMorphismMap T S.p x) (markedLiftMorphismMap T S.q x)
        (markedLiftPairRestriction F S x z) := sorry

/-- Naturality of the second bijection under coherent pseudofunctor morphisms.
Source: Stacks, Tag 06JH (blueprint: lem-sfb-rs-marked-lift-pullback-bijections).
Proof: substitute the strong transformation compositor equation for both corners
from rs_marked_lift_pair_morphism into δ⁻¹ ≫ p_*η ≫ α₁. The comparison t_{a₂}
is a marked isomorphism between the two outputs; the first comparison t_{a₁}
occurs in the marking of the actual transported fixed lift. Thus the quotient
classes agree. Bijectivity gives the corresponding equality for the inverses. -/
theorem rs_marked_lift_second_morphism
    (F G : CofibredGroupoids.{u, v, w} k k)
    (hF : IsRimSchlessinger F) (hG : IsRimSchlessinger G)
    (T : Pseudofunctor.StrongTrans F.transport G.transport)
    (S : MarkedLiftSquare k) {x : fibre F S.base} (x₁ : (CostructuredArrow (push F S.p) x))
    (z : (Quotient (isIsomorphicSetoid (CostructuredArrow (push F S.a₁) x₁.left)))) :
    markedLiftSecondRestriction G S (markedLiftMorphismObject T S.p x₁)
        (markedLiftMorphismMap T S.a₁ x₁.left z) =
      markedLiftMorphismMap T S.q x (markedLiftSecondRestriction F S x₁ z) := sorry

end AlgebraicGeometry.ArtinDeformation
