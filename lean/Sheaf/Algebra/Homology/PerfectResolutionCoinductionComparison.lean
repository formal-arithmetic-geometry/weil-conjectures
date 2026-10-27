module

public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.ModuleHomComplexQuotient
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.CoinductionTotalHomModel
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Flat.Basic

/-! # Coinduction comparison on two finite projective resolutions

Source: Stacks Project, dualizing.tex, Tag 0C0F, lemma-composition-right-adjoints;
more-algebra.tex, Tags 0917 and 0A5Y, and the explicit resolution-normalized square
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison).

The coordinate predicates below specify canonical maps, rather than allowing an
arbitrary comparison. In the bottom formula only the degree-zero component of P
survives its augmentation to B[0]. Thus the signed flip has sign 1 there; all other
components vanish. This is exactly the stated unsigned currying followed by the
Koszul flip, including when the complexes have positive and negative degrees.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wS wB wD

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped TensorProduct ChangeOfRings

namespace ModuleCat.PerfectResolutionCoinduction

/-- Ordinary unbounded complexes. Source: Stacks 05RU
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
abbrev Complex (S : Type u) [CommRing S] := CochainComplex (ModuleCat.{u} S) ℤ

/-- Restriction on complexes. Source: Stacks 0C0F
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
abbrev restriction {S B : Type u} [CommRing S] [CommRing B] (f : S →+* B) :=
  (restrictScalars f).mapHomologicalComplex (.up ℤ)

/-- Extension on complexes, with degreewise B tensor_S -. Source: Stacks 0A5Y
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
abbrev extension {S B : Type u} [CommRing S] [CommRing B] (f : S →+* B) :=
  (extendScalars f).mapHomologicalComplex (.up ℤ)

/-- A module in degree zero. Source: Stacks 0C0F
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
abbrev single {S : Type u} [CommRing S] (M : ModuleCat.{u} S) : Complex S :=
  (CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj M

/-- Signed direct-sum total tensor. Source: Stacks 0A5Y
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
abbrev tensor {S : Type u} [CommRing S] (P Q : Complex S) : Complex S :=
  mapBifunctor P Q (MonoidalCategory.curriedTensor _)

/-- The actual tensor summand inclusion. Source: Stacks 0A5Y
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
abbrev inclusion {S : Type u} [CommRing S] (P Q : Complex S)
    (i k l : ℤ) (h : i + k = l) :=
  ιMapBifunctor P Q (MonoidalCategory.curriedTensor _) i k l h

/-- The coordinate formula for b(a tensor 1), including its zero components.
Source: the explicit square refining Stacks 0C0F
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
def AugmentationFormula {S B D : Type u} [CommRing S] [CommRing B] [CommRing D]
    (f : S →+* B) (g : B →+* D) (P Q : Complex S)
    (a : P ⟶ single ((restrictScalars f).obj (of B B)))
    (b : (extension f).obj Q ⟶ single ((restrictScalars g).obj (of D D)))
    (w : tensor P Q ⟶ (restriction f).obj (single ((restrictScalars g).obj (of D D)))) :
    Prop :=
  (∀ (k : ℤ) (p : P.X 0) (q : Q.X k),
    w.f k (inclusion P Q 0 k k (zero_add k) (p ⊗ₜ[S] q)) =
      b.f k (((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        ((restrictScalars f).obj (of B B))).hom (a.f 0 p)) ⊗ₜ[S,f] q)) ∧
  (∀ (i k : ℤ) (_ : i ≠ 0) (p : P.X i) (q : Q.X k),
    w.f (i + k) (inclusion P Q i k (i + k) rfl (p ⊗ₜ[S] q)) = 0)

/-- The entire bottom comparison on homogeneous tensor generators. This is
F ↦ ((p tensor q) ↦ (-1)^(ij) F(1 tensor q)(a(p))): a(p)=0 unless i=0.
It specifies the original composite of extension adjunction, a*, unsigned currying
and the signed flip without choosing a second currying construction.
Source: Stacks 0A5Y and the explicit square refining 0C0F
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
def KappaFormula {S B : Type u} [CommRing S] [CommRing B]
    (f : S →+* B) (P Q I : Complex S)
    (a : P ⟶ single ((restrictScalars f).obj (of B B)))
    (κ : (restriction f).obj
        (moduleHomComplex ((extension f).obj Q) ((coinductionComplexFunctor f).obj I)) ⟶
      moduleHomComplex (tensor P Q) I) : Prop :=
  (∀ (n k l : ℤ) (h : k + n = l)
      (z : (moduleHomComplex ((extension f).obj Q)
        ((coinductionComplexFunctor f).obj I)).X n) (p : P.X 0) (q : Q.X k),
    ((κ.f n z).v k l h) (inclusion P Q 0 k k (zero_add k) (p ⊗ₜ[S] q)) =
      CoextendScalars.equiv f (I.X l) ((z.v k l h) ((1 : B) ⊗ₜ[S,f] q))
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((restrictScalars f).obj (of B B))).hom (a.f 0 p))) ∧
  (∀ (n i k l : ℤ) (h : (i + k) + n = l) (_ : i ≠ 0)
      (z : (moduleHomComplex ((extension f).obj Q)
        ((coinductionComplexFunctor f).obj I)).X n) (p : P.X i) (q : Q.X k),
    ((κ.f n z).v (i + k) l h)
      (inclusion P Q i k (i + k) rfl (p ⊗ₜ[S] q)) = 0)

/-- The commuting square, its specified cochain models, and the D-linear top lift.
Source: the explicit resolution-normalized square refining Stacks 0C0F
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
structure Square {S B D : Type u} [CommRing S] [CommRing B] [CommRing D]
    (f : S →+* B) (g : B →+* D) (P Q I : Complex S)
    (a : P ⟶ single ((restrictScalars f).obj (of B B)))
    (b : (extension f).obj Q ⟶ single ((restrictScalars g).obj (of D D)))
    (w : tensor P Q ⟶ (restriction f).obj (single ((restrictScalars g).obj (of D D)))) where
  /-- The top evaluation-at-one isomorphism. -/
  e : (restriction f).obj (moduleHomComplex (single ((restrictScalars g).obj (of D D)))
      ((coinductionComplexFunctor f).obj I)) ≅
    moduleHomComplex ((restriction f).obj (single ((restrictScalars g).obj (of D D)))) I
  /-- Evaluation at one on every homogeneous cochain. -/
  evaluation : ∀ (n i k : ℤ) (h : i + n = k)
    (z : (moduleHomComplex (single ((restrictScalars g).obj (of D D)))
      ((coinductionComplexFunctor f).obj I)).X n)
    (d : (single ((restrictScalars g).obj (of D D))).X i),
    ((e.hom.f n z).v i k h) d =
      CoextendScalars.equiv f (I.X k) ((z.v i k h) d) (1 : B)
  /-- The bottom map, fixed by the complete generator formula. -/
  κ : (restriction f).obj
      (moduleHomComplex ((extension f).obj Q) ((coinductionComplexFunctor f).obj I)) ⟶
    moduleHomComplex (tensor P Q) I
  /-- Normalization by a*, unsigned currying and the signed flip. -/
  formula : KappaFormula f P Q I a κ
  /-- Strict chain-level commutativity. -/
  commutes : (restriction f).map
      (moduleHomPrecomp ((coinductionComplexFunctor f).obj I) b) ≫ κ =
    e.hom ≫ moduleHomPrecomp I w
  /-- The left vertical arrow is a quasi-isomorphism. -/
  left_quasiIso : QuasiIso ((restriction f).map
    (moduleHomPrecomp ((coinductionComplexFunctor f).obj I) b))
  /-- The right vertical arrow is a quasi-isomorphism. -/
  right_quasiIso : QuasiIso (moduleHomPrecomp I w)
  /-- The bottom arrow is a quasi-isomorphism. -/
  bottom_quasiIso : QuasiIso κ
  /-- The top map retains the actual D-action before localization. -/
  topD : (coinductionComplexFunctor g).obj ((coinductionComplexFunctor f).obj I) ≅
    (coinductionComplexFunctor (g.comp f)).obj I
  /-- The D-linear lift evaluates the iterated coinduced function at 1_B. -/
  topD_formula : ∀ (n : ℤ)
    (z : ((coinductionComplexFunctor g).obj ((coinductionComplexFunctor f).obj I)).X n)
    (d : D),
    CoextendScalars.equiv (g.comp f) (I.X n) (topD.hom.f n z) d =
      CoextendScalars.equiv f (I.X n)
        (CoextendScalars.equiv g (((coinductionComplexFunctor f).obj I).X n) z d) (1 : B)
  /-- The left Hom model, normalized on the only nonzero source degree. -/
  modelLeft : (restriction (g.comp f)).obj
      ((coinductionComplexFunctor g).obj ((coinductionComplexFunctor f).obj I)) ≅
    (restriction f).obj (moduleHomComplex (single ((restrictScalars g).obj (of D D)))
      ((coinductionComplexFunctor f).obj I))
  /-- Coordinate normalization of the left model. -/
  modelLeft_formula : ∀ (n : ℤ)
    (z : ((coinductionComplexFunctor g).obj ((coinductionComplexFunctor f).obj I)).X n)
    (d : (single ((restrictScalars g).obj (of D D))).X 0),
    ((modelLeft.hom.f n z).v 0 n (zero_add n)) d =
      CoextendScalars.equiv g (((coinductionComplexFunctor f).obj I).X n) z
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((restrictScalars g).obj (of D D))).hom d)
  /-- The direct coinduction Hom model. -/
  modelRight : (restriction (g.comp f)).obj
      ((coinductionComplexFunctor (g.comp f)).obj I) ≅
    moduleHomComplex ((restriction f).obj (single ((restrictScalars g).obj (of D D)))) I
  /-- Coordinate normalization of the direct model. -/
  modelRight_formula : ∀ (n : ℤ)
    (z : ((coinductionComplexFunctor (g.comp f)).obj I).X n)
    (d : (single ((restrictScalars g).obj (of D D))).X 0),
    ((modelRight.hom.f n z).v 0 n (zero_add n)) d =
      CoextendScalars.equiv (g.comp f) (I.X n) z
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((restrictScalars g).obj (of D D))).hom d)
  /-- The top of the displayed square is the restriction of the D-linear lift. -/
  model_commutes : (restriction (g.comp f)).map topD.hom ≫ modelRight.hom =
    modelLeft.hom ≫ e.hom

section Derived

variable {S B D : Type u} [CommRing S] [CommRing B] [CommRing D]
  [HasDerivedCategory.{wS} (ModuleCat.{u} S)]
  [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
  [HasDerivedCategory.{wD} (ModuleCat.{u} D)]

/-- Canonical associativity of exact scalar restriction, with the ordinary identity
normalization. Source: Stacks 0C0F
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
def restrictionComp (f : S →+* B) (g : B →+* D) :
    (restrictScalars (g.comp f)).mapDerivedCategory ≅
      (restrictScalars g).mapDerivedCategory ⋙ (restrictScalars f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (restrictScalarsComp f g) ≪≫
    Functor.mapDerivedCategoryCompIso (restrictScalars g) (restrictScalars f)

/-- Counit normalization characterizing the actual composition of right adjoints.
Source: Stacks 0C0F (blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
def CounitFormula (f : S →+* B) (g : B →+* D)
    (η : derivedCoinduction f ⋙ derivedCoinduction g ≅ derivedCoinduction (g.comp f)) :
    Prop :=
  ∀ X : DerivedCategory (ModuleCat.{u} S),
    (restrictScalars (g.comp f)).mapDerivedCategory.map (η.hom.app X) ≫
        (derivedCoinductionAdjunction (g.comp f)).counit.app X =
      (restrictionComp f g).hom.app ((derivedCoinduction g).obj ((derivedCoinduction f).obj X)) ≫
        (restrictScalars f).mapDerivedCategory.map
          ((derivedCoinductionAdjunction g).counit.app ((derivedCoinduction f).obj X)) ≫
        (derivedCoinductionAdjunction f).counit.app X

/-- The localized top lift is this counit-normalized comparison on every K-injective.
The source K-injective model is used twice, without claiming UJ is K-injective.
Source: Stacks 0C0F and 0917
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison). -/
def DerivedFormula (f : S →+* B) (g : B →+* D)
    (η : derivedCoinduction f ⋙ derivedCoinduction g ≅ derivedCoinduction (g.comp f))
    {P Q I : Complex S} [I.IsKInjective]
    {a : P ⟶ single ((restrictScalars f).obj (of B B))}
    {b : (extension f).obj Q ⟶ single ((restrictScalars g).obj (of D D))}
    {w : tensor P Q ⟶ (restriction f).obj (single ((restrictScalars g).obj (of D D)))}
    (s : Square f g P Q I a b w) : Prop :=
  ((coinductionComplexFunctor f).obj I).IsKInjective ∧
  ∀ [((coinductionComplexFunctor f).obj I).IsKInjective],
    η.hom.app (DerivedCategory.Q.obj I) ≫ (derivedCoinductionModel (g.comp f) I).hom =
      (derivedCoinduction g).map (derivedCoinductionModel f I).hom ≫
        (derivedCoinductionModel g ((coinductionComplexFunctor f).obj I)).hom ≫
        DerivedCategory.Q.map s.topD.hom

/-- Coinduction transitivity on a double finite projective resolution, with the full
chain square, its canonical derived D-action, and the map from unbounded coefficients.
Source: Stacks 0C0F, 0917 and 0A5Y, with the explicit double-resolution refinement
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison).

Proof:
1. Each P^i tensor Q^j is a retract of a finite free module. Boundedness makes each
W^n a finite sum of these retracts, hence finite projective.
2. Projective modules are flat (lem-weil-pbc-projective-module-flat). Bounded-flat
K-flatness (lem-pc-module-bounded-flat-kflat and def-pc-module-kflat-complex) implies
that a tensor 1 is a quasi-isomorphism. Restriction preserves cohomology, so b and
w=b(a tensor 1) are quasi-isomorphisms over S.
3. By lem-sc-module-hom-complex-quotient and
lem-sc-hom-cocycle-homotopy-quotient-formulas, H^n Hom(-,I) is Hom into I[n] modulo
homotopy. The K-injective localization bijection
lem-sc-kinjective-quasi-iso-comparison makes precomposition by a quasi-isomorphism
bijective. This works in every degree and is natural in the source.
4. lem-trf-coinduction-total-hom-model makes J K-injective over B and gives the
specified evaluation isomorphism and its inverse g ↦ (d ↦ (c ↦ g(cd))). Step 3
applied over B to b and over S to w proves both vertical quasi-isomorphisms.
5. Extension adjunction evaluates at 1 tensor q; precompose with a, then use
lem-trf-bimodule-chain-currying-descent with the identity ring map. Its currying is
h(q)(p), without a sign, and is an entire-complex isomorphism.
6. The signed flip p tensor q ↦ (-1)^(ij) q tensor p is a chain isomorphism:
the two differential terms have exponents ij and ij+j on both sides; its square
has even exponent 2ij. Precomposition by this flip gives κ.
7. The square evaluated at p tensor q has values (-1)^(ij)h(b(1 tensor q))(a(p))
and h(b(a(p) tensor q))(1). Both vanish for i ≠ 0. For i=0, B-linearity makes
them equal. Three arrows are quasi-isomorphisms, hence κ is too.
8. The top lift is D-linear by precomposition: e(th)(d)=h(dt)(1). Its counit is
h(1_D)(1_B). lem-trf-derived-coinduction-adjunction and det-sp-unique-right-adjoint
identify it with the unique counit-compatible composition comparison η.
9. Invert the localized vertical arrows. The commutative square identifies the
bottom arrow with η, carrying exactly the D-actions transported from the top.
10. Step 1 and lem-sc-bounded-above-projective-kprojective make W K-projective.
lem-coef-kprojective-derived-hom-bijection and the Hom cohomology identification
then make Hom(W,j) a quasi-isomorphism, for arbitrary unbounded N.
11. All formulas commute with postcomposition and augmentation-preserving maps.
lem-weil-pbc-kinjective-hom-derived represents arbitrary derived coefficient maps
by homotopy classes between K-injectives. Their canonical comparisons and the
naturality of η make the identifications independent of j. The separate naturality
statement below records the corresponding chain-map squares. -/
theorem perfect_resolution_coinduction_comparison (f : S →+* B) (g : B →+* D) :
    ∃ η : derivedCoinduction f ⋙ derivedCoinduction g ≅ derivedCoinduction (g.comp f),
      CounitFormula f g η ∧
      ∀ (P Q : Complex S)
        (a : P ⟶ single ((restrictScalars f).obj (of B B)))
        (b : (extension f).obj Q ⟶ single ((restrictScalars g).obj (of D D))),
        QuasiIso a → QuasiIso b →
        (∃ l r : ℤ, P.IsStrictlyGE l ∧ P.IsStrictlyLE r) →
        (∃ l r : ℤ, Q.IsStrictlyGE l ∧ Q.IsStrictlyLE r) →
        (∀ n : ℤ, Module.Finite S (P.X n) ∧ Module.Projective S (P.X n)) →
        (∀ n : ℤ, Module.Finite S (Q.X n) ∧ Module.Projective S (Q.X n)) →
        ∃ w : tensor P Q ⟶
            (restriction f).obj (single ((restrictScalars g).obj (of D D))),
          AugmentationFormula f g P Q a b w ∧ QuasiIso w ∧
          (∀ (I : Complex S) [I.IsKInjective],
            ∃ s : Square f g P Q I a b w, DerivedFormula f g η s) ∧
          (∀ (N I : Complex S) [I.IsKInjective] (j : N ⟶ I) [QuasiIso j],
            ∃ jW : moduleHomComplex (tensor P Q) N ⟶ moduleHomComplex (tensor P Q) I,
              (∀ (n i k : ℤ) (h : i + n = k)
                (z : (moduleHomComplex (tensor P Q) N).X n) (x : (tensor P Q).X i),
                ((jW.f n z).v i k h) x = j.f k ((z.v i k h) x)) ∧ QuasiIso jW) := by
  sorry

/-- Naturality of the normalized square under maps of both augmented resolutions
and coefficient maps between K-injectives. The induced maps F and R are fixed on
all homogeneous cochains, not just cohomology. Inverting quasi-isomorphisms gives
naturality for arbitrary derived coefficient morphisms.
Source: Stacks 0C0F, 0A5Y and 070I, explicit naturality of the resolution square
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison).

Proof: Evaluate both composites on p' tensor q'. The augmentation equation a u=a'
and B-linearity give the same value t(F(1 tensor v(q'))(a(u(p')))) in degree zero
of P'; all other degrees vanish. The tensor augmentation calculation likewise uses
b(1 tensor v)=b'. Hom cochains and total tensor summands jointly detect equality.
For the top row evaluate at 1_B, which commutes with postcomposition. The
K-injective localization bijection of lem-weil-pbc-kinjective-hom-derived represents
every derived map by a homotopy class, so the chain equalities descend and can be
inverted for quasi-isomorphisms. -/
theorem perfect_resolution_coinduction_naturality (f : S →+* B) (g : B →+* D)
    {P Q P' Q' I I' : Complex S} [I.IsKInjective] [I'.IsKInjective]
    {a : P ⟶ single ((restrictScalars f).obj (of B B))}
    {a' : P' ⟶ single ((restrictScalars f).obj (of B B))}
    {b : (extension f).obj Q ⟶ single ((restrictScalars g).obj (of D D))}
    {b' : (extension f).obj Q' ⟶ single ((restrictScalars g).obj (of D D))}
    {w : tensor P Q ⟶ (restriction f).obj (single ((restrictScalars g).obj (of D D)))}
    {w' : tensor P' Q' ⟶ (restriction f).obj (single ((restrictScalars g).obj (of D D)))}
    (hw : AugmentationFormula f g P Q a b w)
    (hw' : AugmentationFormula f g P' Q' a' b' w')
    (s : Square f g P Q I a b w) (s' : Square f g P' Q' I' a' b' w')
    (u : P' ⟶ P) (v : Q' ⟶ Q) (t : I ⟶ I')
    (ha : u ≫ a = a') (hb : (extension f).map v ≫ b = b') :
    HomologicalComplex.mapBifunctorMap u v (MonoidalCategory.curriedTensor _)
        (.up ℤ) ≫ w = w' ∧
    ∃ (F : (restriction f).obj
          (moduleHomComplex ((extension f).obj Q) ((coinductionComplexFunctor f).obj I)) ⟶
        (restriction f).obj
          (moduleHomComplex ((extension f).obj Q') ((coinductionComplexFunctor f).obj I')))
      (R : moduleHomComplex (tensor P Q) I ⟶ moduleHomComplex (tensor P' Q') I'),
      (∀ (n i k : ℤ) (h : i + n = k)
        (z : (moduleHomComplex ((extension f).obj Q)
          ((coinductionComplexFunctor f).obj I)).X n) (x : ((extension f).obj Q').X i),
        ((F.f n z).v i k h) x = ((coinductionComplexFunctor f).map t).f k
          ((z.v i k h) (((extension f).map v).f i x))) ∧
      (∀ (n i k : ℤ) (h : i + n = k)
        (z : (moduleHomComplex (tensor P Q) I).X n) (x : (tensor P' Q').X i),
        ((R.f n z).v i k h) x = t.f k ((z.v i k h)
          ((HomologicalComplex.mapBifunctorMap u v (MonoidalCategory.curriedTensor _)
            (.up ℤ)).f i x))) ∧
      F ≫ s'.κ = s.κ ≫ R := by
  sorry

/-- Naturality of both presentations of the top evaluation map, including the
D-linear lift. Source: Stacks 0C0F and 0917
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison).

Proof: Both paths send a homogeneous h and d to t(h(d)(1_B)). Evaluation commutes
with postcomposition. The D-linear equality is checked at every d using the same
formula. The coordinate descriptions of modelLeft and modelRight then give the
same equalities in the Hom presentations, before localization. -/
theorem perfect_resolution_coinduction_top_naturality (f : S →+* B) (g : B →+* D)
    {P Q I I' : Complex S} [I.IsKInjective] [I'.IsKInjective]
    {a : P ⟶ single ((restrictScalars f).obj (of B B))}
    {b : (extension f).obj Q ⟶ single ((restrictScalars g).obj (of D D))}
    {w : tensor P Q ⟶ (restriction f).obj (single ((restrictScalars g).obj (of D D)))}
    (s : Square f g P Q I a b w) (s' : Square f g P Q I' a b w) (t : I ⟶ I') :
    ∃ (L : (restriction f).obj
          (moduleHomComplex (single ((restrictScalars g).obj (of D D)))
            ((coinductionComplexFunctor f).obj I)) ⟶
        (restriction f).obj
          (moduleHomComplex (single ((restrictScalars g).obj (of D D)))
            ((coinductionComplexFunctor f).obj I')))
      (R : moduleHomComplex
          ((restriction f).obj (single ((restrictScalars g).obj (of D D)))) I ⟶
        moduleHomComplex
          ((restriction f).obj (single ((restrictScalars g).obj (of D D)))) I'),
      (∀ (n i k : ℤ) (h : i + n = k)
        (z : (moduleHomComplex (single ((restrictScalars g).obj (of D D)))
          ((coinductionComplexFunctor f).obj I)).X n)
        (d : (single ((restrictScalars g).obj (of D D))).X i),
        ((L.f n z).v i k h) d =
          ((coinductionComplexFunctor f).map t).f k ((z.v i k h) d)) ∧
      (∀ (n i k : ℤ) (h : i + n = k)
        (z : (moduleHomComplex
          ((restriction f).obj (single ((restrictScalars g).obj (of D D)))) I).X n)
        (d : (single ((restrictScalars g).obj (of D D))).X i),
        ((R.f n z).v i k h) d = t.f k ((z.v i k h) d)) ∧
      L ≫ s'.e.hom = s.e.hom ≫ R ∧
      (coinductionComplexFunctor g).map ((coinductionComplexFunctor f).map t) ≫
          s'.topD.hom = s.topD.hom ≫ (coinductionComplexFunctor (g.comp f)).map t := by
  sorry

/-- Independence from K-injective replacements, through the canonical homotopy
comparison representing [j'] [j]⁻¹, together with its effect on the actual D-linear
composition comparison. Source: Stacks 070I and 0C0F
(blueprint: lem-sfb-perfect-resolution-coinduction-comparison).

Proof: The K-injective localization bijection
lem-weil-pbc-kinjective-hom-derived represents [j'] [j]⁻¹ by t, uniquely up to
homotopy. Its composite with j is homotopic to j'. The inverse localized map gives
a homotopy inverse for t, hence t is a quasi-isomorphism. The natural isomorphism η
commutes with [t]. Apply the preceding naturality statement to both normalized
squares; invert their vertical quasi-isomorphisms. This gives the same comparison
on N, with the D-action inherited from η, independently of either replacement. -/
theorem perfect_resolution_coinduction_resolution_independence
    (f : S →+* B) (g : B →+* D)
    (η : derivedCoinduction f ⋙ derivedCoinduction g ≅ derivedCoinduction (g.comp f))
    (N I I' : Complex S) [I.IsKInjective] [I'.IsKInjective]
    (j : N ⟶ I) (j' : N ⟶ I') [QuasiIso j] [QuasiIso j'] :
    ∃ t : I ⟶ I', Nonempty (Homotopy (j ≫ t) j') ∧ QuasiIso t ∧
      (∀ t' : I ⟶ I', Nonempty (Homotopy (j ≫ t') j') → Nonempty (Homotopy t t')) ∧
      (derivedCoinduction g).map ((derivedCoinduction f).map (DerivedCategory.Q.map t)) ≫
          η.hom.app (DerivedCategory.Q.obj I') =
        η.hom.app (DerivedCategory.Q.obj I) ≫
          (derivedCoinduction (g.comp f)).map (DerivedCategory.Q.map t) := by
  sorry

end Derived
end ModuleCat.PerfectResolutionCoinduction
