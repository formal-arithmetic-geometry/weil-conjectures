/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.AffineSchemeDeformationComparison
public import Sheaf.AlgebraicGeometry.SchemeCotangentOpenRestriction
public import Sheaf.AlgebraicGeometry.SchemeCoefficientExtensionProblems
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.RingTheory.NilpotentIdealFlatnessCriterion
import Sheaf.AlgebraicGeometry.ZariskiSquareZeroSchemeRealization
import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Cotangent Ext classification of marked scheme lifts
Source: Stacks 0D14, 0GPZ, 0GQ0--0GQ2, 08UW and 08UZ
(blueprint: lem-sfb-scheme-square-zero-lift-torsor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.CotangentResolution
namespace AlgebraicGeometry.SchemeDeformation
variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
  [∀ X : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]

/-- Simultaneous classification, so the open and coefficient equations refer to the
same torsor and automorphism identifications. Source: Stacks 0D14, 0GQ1 and 08UZ
(blueprint: lem-sfb-scheme-square-zero-lift-torsor). -/
structure Classification (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C) where
  torsor : ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S'),
    Flat f → IsFirstOrderThickening i → Nonempty (Lift f i) → LiftTorsor C D f i
  kernel : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'},
    IsFirstOrderThickening i → (Y : Lift f i) → LiftKernel Y
  automorphisms : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'},
    IsFirstOrderThickening i → (Y : Lift f i) → AutomorphismIdentification C D Y
  derivation : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    (ξ : Ext C D f G 0), DerivationRepresentative C D f G ξ
  automorphism_formula : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (hi : IsFirstOrderThickening i) (Y : Lift f i) (a : Aut Y) (V : Y.space.Opens)
    (e : Γ(Y.space, V)) (W : X.Opens) (h : W ≤ Y.marking ⁻¹ᵁ V)
    (h' : W ≤ Y.marking ⁻¹ᵁ ((liftMap a.hom) ⁻¹ᵁ V)),
    inverseSection Y.marking ((liftMap a.hom) ⁻¹ᵁ V) W h'
      ((liftMap a.hom).app V e) =
      inverseSection Y.marking V W h e +
        (kernel hi Y).inclusion W
          ((coefficient f i).val.map (homOfLE h).op
            ((derivation f (coefficient f i)
              ((automorphisms hi Y a).toAdd)).derivation.d (Y.marking.app V e)))
  opens : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens), OpenComparison C D f U
  restrict : ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S') (U : X.Opens),
    Classes f i → Classes (U.ι ≫ f) i
  restrict_exists : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (_hi : IsFirstOrderThickening i) (U : X.Opens) (Y : Lift f i),
    ∃ (Z : Lift (U.ι ≫ f) i) (q : Z.space ⟶ Y.space), IsRestriction U.ι Y Z q
  restrict_class : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (_hi : IsFirstOrderThickening i) (U : X.Opens) (Y : Lift f i)
    (Z : Lift (U.ι ≫ f) i) (q : Z.space ⟶ Y.space),
    IsRestriction U.ι Y Z q → restrict f i U Y.class = Z.class
  restrict_translate : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (hf : Flat f) (hi : IsFirstOrderThickening i) (h : Nonempty (Lift f i))
    (U : X.Opens) (hfU : Flat (U.ι ≫ f)) (hU : Nonempty (Lift (U.ι ≫ f) i))
    (a : Ext C D f (coefficient f i) 1) (x : Classes f i),
    restrict f i U ((torsor f i hf hi h).translate a x) =
      (torsor (U.ι ≫ f) i hfU hi hU).translate
        (extMap C D (U.ι ≫ f) (coefficientRestriction f i U).hom 1
          ((opens f U).ext _ 1 a)) (restrict f i U x)
  restrict_automorphism : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (hi : IsFirstOrderThickening i) (U : X.Opens) (Y : Lift f i)
    (Z : Lift (U.ι ≫ f) i) (q : Z.space ⟶ Y.space) (a : Aut Y) (b : Aut Z),
    IsRestriction U.ι Y Z q → liftMap b.hom ≫ q = q ≫ liftMap a.hom →
      (automorphisms hi Z b).toAdd =
        extMap C D (U.ι ≫ f) (coefficientRestriction f i U).hom 0
          ((opens f U).ext _ 0 ((automorphisms hi Y a).toAdd))
  sheaf : TopCat.SquareZeroSheaf.Classification C D
  problem : ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S'),
    SchemeProblem f i (coefficient f i)
  problem_base : ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S')
    (_hi : IsFirstOrderThickening i) (V : S'.Opens) (a : Γ(i.ker.toModules, V)) (W : X.Opens)
    (h : W ≤ f ⁻¹ᵁ (i ⁻¹ᵁ V)) (h' : W ≤ (f ≫ i) ⁻¹ᵁ V)
    (r : RingHom.ker ((baseReduction f i).hom.app (op W)).hom),
    r.val = inverseSection (f ≫ i) V W h' (i.ker.toModulesι.app V a) →
      (problem f i).baseIdeal (op W) r = (coefficient f i).val.map (homOfLE h).op
        (Scheme.Modules.tensorPullbackSection f _ (i ⁻¹ᵁ V)
          (Scheme.Modules.tensorPullbackSection i _ V a))
  solution : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (hi : IsFirstOrderThickening i) (Y : Lift f i),
    LiftSolution (problem f i) Y (kernel hi Y)
  solutions : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (_hf : Flat f) (_hi : IsFirstOrderThickening i),
    Classes f i ≃ (problem f i).Classes
  solution_class : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (hf : Flat f) (hi : IsFirstOrderThickening i) (Y : Lift f i),
    solutions hf hi Y.class = (solution hi Y).solution.class
  problem_torsor : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'},
    IsFirstOrderThickening i → ∀ (G : X.Modules) (P : SchemeProblem f i G),
    Nonempty P.Solution → SolutionTorsor C D P
  solution_translate : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (hf : Flat f) (hi : IsFirstOrderThickening i) (h : Nonempty (Lift f i))
    (hP : Nonempty (problem f i).Solution) (a : Ext C D f (coefficient f i) 1)
    (x : Classes f i),
    solutions hf hi ((torsor f i hf hi h).translate a x) =
      (problem_torsor hi _ (problem f i) hP).translate a (solutions hf hi x)
  translation_normalization : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (hi : IsFirstOrderThickening i) {G : X.Modules} (P : SchemeProblem f i G)
    (hP : Nonempty P.Solution) (E H : P.Solution)
    (F : TopCat.SquareZeroSheaf.Extension (Scheme.Modules.tensorPullbackRingMap f) G)
    (a : TopCat.SquareZeroSheaf.ConormalClass C D F
      (sheaf.standardPresentation _) (sheaf.projection _) (sheaf.extensionPresentation F)
      (sheaf.cl _ G F)),
    TopCat.SquareZeroSheaf.Baer E.val (rebaseExtension (baseReduction f i) F) H.val →
      (problem_torsor hi G P hP).translate (extensionClass sheaf F a) E.class = H.class
  coefficient_translate : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (hi : IsFirstOrderThickening i) {G H : X.Modules}
    (P : SchemeProblem f i G) (Q : SchemeProblem f i H) (a : G ⟶ H),
    P.Compatible Q a → ∀ (hP : Nonempty P.Solution) (hQ : Nonempty Q.Solution)
    (E E' : P.Solution) (F F' : Q.Solution)
    (_m : TopCat.SquareZeroSheaf.Hom E.val F.val a)
    (_m' : TopCat.SquareZeroSheaf.Hom E'.val F'.val a) (ξ : Ext C D f G 1),
    (problem_torsor hi G P hP).translate ξ E.class = E'.class →
      (problem_torsor hi H Q hQ).translate (extMap C D f a 1 ξ) F.class = F'.class
  coefficient_exists : ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (_hi : IsFirstOrderThickening i) {G H : X.Modules}
    (P : SchemeProblem f i G) (Q : SchemeProblem f i H) (a : G ⟶ H),
    P.Compatible Q a → ∀ E : P.Solution,
      ∃ F : Q.Solution, Nonempty (TopCat.SquareZeroSheaf.Hom E.val F.val a)
  coefficient_derivation : ∀ {X S : Scheme.{u}} (f : X ⟶ S) {G H : X.Modules}
    (a : G ⟶ H) (ξ : Ext C D f G 0)
    (V : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj V),
    (derivation f H (extMap C D f a 0 ξ)).derivation.d b =
      a.val.app V ((derivation f G ξ).derivation.d b)
  split : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)),
    SplitClassification C D k f
  split_coefficient : ∀ (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : ModuleCat.{u} k),
    coefficient f (directionReduction k M) ≅ directionModule f M
  split_coefficient_sections : ∀ (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : ModuleCat.{u} k) (m : M)
    (g : Γ((directionReduction k M).ker.toModules, ⊤)) (W : X.Opens)
    (h : W ≤ f ⁻¹ᵁ ((directionReduction k M) ⁻¹ᵁ ⊤)) (h' : W ≤ f ⁻¹ᵁ ⊤),
    (directionReduction k M).ker.toModulesι.app ⊤ g =
      (Scheme.ΓSpecIso (.of (TrivSqZeroExt k M))).inv (TrivSqZeroExt.inr m) →
    (split_coefficient k f M).hom.app W
      ((coefficient f (directionReduction k M)).val.map (homOfLE h).op
        (Scheme.Modules.tensorPullbackSection f _ ((directionReduction k M) ⁻¹ᵁ ⊤)
          (Scheme.Modules.tensorPullbackSection (directionReduction k M) _ ⊤ g))) =
      (directionModule f M).val.map (homOfLE h').op
        (Scheme.Modules.tensorPullbackSection f _ ⊤ (tilde.toOpen (R := .of k) M ⊤ m))
  split_extension : ∀ (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : ModuleCat.{u} k)
    (hi : IsFirstOrderThickening (directionReduction k M))
    (Y : Lift f (directionReduction k M)),
    SplitLiftExtension Y (kernel hi Y) (split_coefficient k f M)
  split_normalization : ∀ (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : ModuleCat.{u} k) (hM : FiniteDimensional k M)
    (hi : IsFirstOrderThickening (directionReduction k M))
    (Y : Lift f (directionReduction k M))
    (a : TopCat.SquareZeroSheaf.ConormalClass C D (split_extension k f M hi Y).extension
      (sheaf.standardPresentation _) (sheaf.projection _)
      (sheaf.extensionPresentation (split_extension k f M hi Y).extension)
      (sheaf.cl _ _ (split_extension k f M hi Y).extension)),
    (split k f).classes M hM Y.class =
      extensionClass sheaf (split_extension k f M hi Y).extension a
  split_translate : ∀ (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : ModuleCat.{u} k) (hM : FiniteDimensional k M)
    (hf : Flat f) (hi : IsFirstOrderThickening (directionReduction k M))
    (h : Nonempty (Lift f (directionReduction k M)))
    (ξ : Ext C D f (coefficient f (directionReduction k M)) 1)
    (x : Classes f (directionReduction k M)),
    (split k f).classes M hM
      ((torsor f (directionReduction k M) hf hi h).translate ξ x) =
        extMap C D f (split_coefficient k f M).hom 1 ξ + (split k f).classes M hM x
  split_restrict : ∀ (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : ModuleCat.{u} k) (hM : FiniteDimensional k M)
    (U : X.Opens) (x : Classes f (directionReduction k M)),
    (split k (U.ι ≫ f)).classes M hM (restrict f (directionReduction k M) U x) =
      extMap C D (U.ι ≫ f) (directionRestriction f M U).hom 1
        ((opens f U).ext _ 1 ((split k f).classes M hM x))
  affine : ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
    AffineComparison C D k A
  affine_bijective : ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (_hA : Algebra.EssFiniteType k A) (κ : Naive.Comparison C)
    (P : Naive.Presentation (affineArrow k A)) (hP : Naive.IsLocalizedPolynomial P)
    (M : ModuleCat.{u} k) (_hM : FiniteDimensional k M),
    Function.Bijective ((affine k A).naiveExt κ P hP M)
  affine_classes : ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (_hA : Algebra.EssFiniteType k A) (_κ : Naive.Comparison C)
    (P : Naive.Presentation (affineArrow k A)) (_hP : Naive.IsLocalizedPolynomial P)
    (M : ModuleCat.{u} k) (_hM : FiniteDimensional k M),
    Classes (affineMorphism k A) (directionReduction k M) ≃
      (DerivedCategory.Q.obj (Naive.complex P) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj
          (ModuleCat.of A (TensorProduct k A M)))⟦(1 : ℤ)⟧)
  affine_agrees : ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (hA : Algebra.EssFiniteType k A) (κ : Naive.Comparison C)
    (P : Naive.Presentation (affineArrow k A)) (hP : Naive.IsLocalizedPolynomial P)
    (M : ModuleCat.{u} k) (hM : FiniteDimensional k M)
    (x : Classes (affineMorphism k A) (directionReduction k M)),
    (affine k A).naiveExt κ P hP M (affine_classes k A hA κ P hP M hM x) =
      (split k (affineMorphism k A)).classes M hM x
  localization_coefficients : ∀ {k A B : Type u} [Field k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B]
    (q : affineArrow k A ⟶ affineArrow k B) (_hk : q.left = 𝟙 _)
    (M : ModuleCat.{u} k), TensorCoefficientRestriction q M
  affine_localization : ∀ {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (hA : Algebra.EssFiniteType k A) (hB : Algebra.EssFiniteType k B)
    (W : Submonoid A) (_hW : IsLocalization W B)
    (q : affineArrow k A ⟶ affineArrow k B)
    (_hq : q.right.hom = algebraMap A B) (hk : q.left = 𝟙 _)
    (κ : Naive.Comparison C) (P : Naive.Presentation (affineArrow k A))
    (P' : Naive.Presentation (affineArrow k B))
    (hP : Naive.IsLocalizedPolynomial P) (hP' : Naive.IsLocalizedPolynomial P')
    (M : ModuleCat.{u} k) (hM : FiniteDimensional k M)
    (Y : Lift (affineMorphism k A) (directionReduction k M))
    (Z : Lift (affineMorphism k B) (directionReduction k M)) (b : Z.space ⟶ Y.space),
    IsPullback Z.marking (Spec.map q.right) b Y.marking →
    b ≫ Y.projection = Z.projection →
      IsAffineExtRestriction C q M (localization_coefficients q hk M)
        (κ.comparison P hP ≫ affine_classes k A hA κ P hP M hM Y.class)
        (κ.comparison P' hP' ≫ affine_classes k B hB κ P' hP' M hM Z.class)

/-- Flat marked lifts form a cotangent-Ext torsor; automorphisms and the split-base
classification have the stated sectionwise normalizations and naturality.
Source: Stacks 0D14, 0GPZ, 0GQ0--0GQ2, 08U8 and 08UZ
(blueprint: lem-sfb-scheme-square-zero-lift-torsor).

Proof:

1. Identify the underlying spaces of $S$ and $S'$ and put $B=\mathcal O_X$, $R=f^{-1}\mathcal O_S$,
$R'=f^{-1}\mathcal O_{S'}$, $K=f^{-1}\mathcal J$, so $R'/K=R$. The ideal $\mathcal J$ is quasi-
coherent on $S$ (as an $\mathcal O_S$-module it is its own conormal module, because $\mathcal
J^2=0$); hence $G=B\otimes_R K=f^*\mathcal J$ is quasi-coherent by module pullback. A marked flat
lift gives a ring extension $0\to G\to E\to B\to0$ with an $R'$-algebra structure whose map on $K$
is $k\mapsto1\otimes k$: the flat cartesian conormal comparison identifies its actual ideal with
$G$. Conversely realize any such extension as a scheme by the Zariski realization lemma. On affine
charts write $R'_0\twoheadrightarrow R_0$, kernel $I$, and $E_0\twoheadrightarrow B_0$, kernel
$B_0\otimes_{R_0}I$. The prescribed map on $I$ implies $IE_0=G_0$ and $E_0/IE_0=B_0$. The quotient-
tensor identification gives $I\otimes_{R'_0}E_0\cong I\otimes_{R_0}B_0=G_0$, and multiplication is
the injection $G_0\hookrightarrow E_0$. The nilpotent-ideal flatness criterion now makes $E_0$ flat
over $R'_0$, since $B_0$ is flat over $R_0$. The affine flatness criterion gives flatness globally;
the quotient says its special fibre is precisely the marked $X$. The realization lemma identifies
all marked isomorphisms. Thus marked lifts are exactly these extensions, with their specified base-
ideal map.
Uses: def-sbc-first-order-thickening, lem-weil-pbc-module-pullback-quasi-coherent, lem-weil-pbc-
module-pullback-affine-sections, lem-weil-pbc-closed-immersion-conormal-flat-base-change, lem-sfb-
zariski-square-zero-scheme-realization, lem-weil-pbc-tensor-over-quotient-ring, lem-sfb-nilpotent-
ideal-flatness-criterion, lem-weil-pbc-flat-morphism-affine-criterion.

2. Fix a lift extension $E_0$. If $F$ is an $R$-algebra extension of $B$ by $G$, form $E_0+F$ by
taking $E_0\times_BF$ and quotienting its kernel by $\{(g,-g):g\in G\}$. Give it the $R'$-structure
$r'\mapsto[\rho_0(r'),\rho_F(\bar r')]$, where $\rho_F$ is the base map $R\to F$. It still sends
$k\in K$ to $1\otimes k$, so step 1 realizes it as a flat marked lift. Conversely for a lift $E$
form $E-E_0=(E\times_BE_0)/\{(g,g):g\in G\}$. The map $r'\mapsto[\rho(r'),\rho_0(r')]$ kills $K$ and
factors through $R$; its kernel is identified with $G$ by $(g,h)\mapsto g-h$. The cancellation
$E_0+(E-E_0)\cong E$ sends a local representative $(a_0,[e,b_0])$ to $e+i(g)$, where
$a_0-b_0=i_0(g)$. Replacing $(e,b_0)$ by $(e+i(h),b_0+i_0(h))$ replaces $g$ by $g-h$, leaving this
formula unchanged; the outer antidiagonal relation also cancels. The same formula, replacing $e$ by
a section of $F$, identifies $(E_0+F)-E_0$ with $F$. These maps are local isomorphisms on both
kernel and quotient and therefore are isomorphisms of extensions. For three factors the relation is
always that the sum of kernel coordinates is zero. Hence $(E_0+F_1)+F_2=E_0+(F_1+F_2)$, and
$E_0+(B\oplus G)=E_0$. The sheaf-algebra classification identifies these Baer classes and their
addition with $\operatorname{Ext}^1_B(L_{B/R},G)$. Taking $F=E-E_0$ proves both existence and
uniqueness of a translating element. This proves the asserted torsor, independently of any
properness or dimension assumption.
Uses: lem-sfb-zariski-sheaf-algebra-extension-ext.

3. Every $R'$-automorphism of a lift that is the identity on $B$ is also the identity on $G$, since
$G$ is generated as a $B$-module by the image of $K$. For such an automorphism $\phi$, $\phi(e)-e$
depends only on $p(e)$ and defines $d:B\to G$. Expanding $\phi(ee')$ and using $G^2=0$ gives
$d(bb')=b\,d(b')+b'\,d(b)$; $R'$-linearity makes it vanish on $R$. Conversely $e\mapsto
e+i(d(p(e)))$ for an $R$-derivation fixes the base and quotient and has inverse given by $-d$. The
cross term is zero, so composition corresponds to addition. The derivation identification in the
sheaf-algebra Ext lemma gives exactly $\operatorname{Ext}^0_B(L_{B/R},G)$, with no chosen origin.
Uses: lem-sfb-zariski-sheaf-algebra-extension-ext.

4. Restriction to an open applies every displayed formula sectionwise. For a coefficient map $u:G\to
H$, push out the kernels and the base-ideal map: on the displayed kernel coordinates it sends
$[g,h]$ to $[u(g),u(h)]$. It therefore commutes with Baer addition and difference, and sends $d$ to
$ud$. The sheaf-algebra Ext lemma identifies these operations with the induced Ext maps; its open-
restriction compatibility uses the same standard sheaf cotangent complex. For general $H$ this
assertion is at the level of square-zero extension problems with base-ideal map $uc$; when both
problems arise as flat lifts the scheme identification of step 1 applies. Thus no arbitrary
coefficient pushout is falsely asserted to remain a flat lift of the same base.
Uses: lem-sfb-zariski-sheaf-algebra-extension-ext.

5. For the split base $k\oplus M$, the projection $k\oplus M\to k$ is split by $k\to k\oplus M$. A
lift extension is therefore a sheaf of $k$-algebras with square-zero kernel $G=\mathcal
O_X\otimes_kM$. Conversely every such extension has the unique base structure $(a,m)\mapsto
a\,1+i(1\otimes m)$; multiplication gives $ab\,1+i(a\otimes n+b\otimes m)$, as required. Step 1
makes it a flat lift. The split extension $B\oplus G$ is the trivial family by the fibre-product
affine tensor description, and the base-change flatness lemma guarantees it is flat. The sheaf-
algebra class map consequently gives the canonical classification, taking the trivial family to
zero. A linear map $M\to N$ induces kernel pushout $B\otimes M\to B\otimes N$; it is the base change
of the lift. Indeed base change is flat, so step 1 identifies its kernel with $B\otimes_kN$ and
quotient with $B$. The base-change map from the old extension induces $1\otimes u$ on its kernel.
The induced map from its kernel pushout is the identity on kernel and quotient, hence is an
isomorphism. For addition first take the fibre product of two extensions over $B$ (directions
$M\oplus M$), then push out the kernel along addition. The Ext lemma sends these operations to
coefficient maps and addition. Scalar multiplication is the coefficient map $m\mapsto am$, giving
the stated $k$-linearity.
Uses: lem-sfb-zariski-sheaf-algebra-extension-ext, lem-weil-pbc-flat-morphism-base-change, def-pc-
fibre-product, def-pur-sheaf-tensor-product.

6. For $X=\operatorname{Spec}A$, use the intrinsic affine cotangent comparison to identify the full
sheaf complex with $\widetilde{L_{A/k}}$, and $G$ with $\widetilde{A\otimes_kM}$. The affine quasi-
coherent derived equivalence identifies their derived Hom groups with those in $D(A)$. The localized
polynomial presentation lemma identifies $C=[J/J^2\to\Omega^1_{P/k}\otimes_PA]$ with
$\tau_{\geq-1}L_{A/k}$. In the truncation triangle $Q\to L_{A/k}\to C\to Q[1]$, $Q\in D^{\leq-2}$,
hence both $\operatorname{Hom}(Q,G[1])$ and $\operatorname{Hom}(Q[1],G[1])$ vanish by t-structure
orthogonality. Exactness of Hom out of the triangle makes
$\operatorname{Ext}^1_A(C,G)\to\operatorname{Ext}^1_A(L_{A/k},G)$ bijective. This is the required
affine model, without a regular-sequence hypothesis on $J$. Every map used here is the canonical
presentation or restriction map. The presentation comparison commutes with maps of localized
presentations and the intrinsic comparison with smaller affine charts; the standard cotangent
localization comparison handles successive localizations. Thus the Ext description and the
deformation class commute with every further localization.
Uses: lem-trf-lci-cotangent-presentation, lem-pc-affine-qcoh-derived-equivalence, lem-trf-lci-naive-
cotangent-model, def-sbc-standard-tstructure-derived-category, lem-pc-derived-tstructure-
orthogonality, lem-weil-pbc-hom-out-of-triangle-exact, lem-trf-affine-cotangent-comparison.
-/
theorem exists_classification (C : Coherence.{u})
    (D : TopCat.SheafCotangent.Comparison C) : Nonempty (Classification C D) := by
  sorry

end AlgebraicGeometry.SchemeDeformation
