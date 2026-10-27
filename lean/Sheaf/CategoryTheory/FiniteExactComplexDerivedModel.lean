module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # A finite exact cochain model for a total right derived functor

Source: Stacks Project, Homological Algebra, Tag 0133; Derived Categories, Tags
013P, 013S and 05TH; blueprint direct-image stability proof, paragraph (3)
(blueprint: lem-sfb-finite-exact-complex-derived-model).

The bicomplex and its total, inclusions, induced maps and transpose use Mathlib's
constructions. The two augmentations in the main theorem are characterized in every
cochain degree, so they are the prescribed axis maps. The same natural isomorphism
satisfies the resolution formula for every resolution, expressing independence before
passing to cohomology. The derived pair is arbitrary with its specified universal unit;
no existence of unbounded K-injective resolutions is additionally assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FiniteExactComplex

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The actual bicomplex functor, with outer index the finite model degree and inner
index the resolution degree: B(I)^{a,b} = F^a(I^b).
Source: Stacks Tag 0133 (blueprint: lem-sfb-finite-exact-complex-derived-model). -/
def bicomplexFunctor (F : A ⥤ CochainComplex B ℤ) [F.Additive] :
    CochainComplex A ℤ ⥤ HomologicalComplex₂ B (.up ℤ) (.up ℤ) :=
  F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex₂.flipFunctor B (.up ℤ) (.up ℤ)

/-- The first-quadrant bicomplex admits finite diagonal totals.
Source: Stacks Tag 0133 (blueprint: lem-sfb-finite-exact-complex-derived-model).
Proof: F is zero in negative model degrees. In negative resolution degrees I is zero,
and additivity carries zero objects to zero objects. Thus B(I) is first-quadrant.
Apply `HomologicalComplex₂.hasTotal_of_firstQuadrant`: only 0 ≤ a ≤ n contribute
in degree n, so finite coproducts in the abelian category suffice, also for n < 0. -/
theorem hasTotal (F : A ⥤ CochainComplex B ℤ) [F.Additive] (r : ℕ)
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (I : CochainComplex A ℤ) (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b)) :
    ((bicomplexFunctor F).obj I).HasTotal (.up ℤ) := by
  sorry

/-- Totalization with d = d_F + (-1)^a d_I, using finite first-quadrant diagonals.
Source: Stacks Tag 0133 (blueprint: lem-sfb-finite-exact-complex-derived-model). -/
def total (F : A ⥤ CochainComplex B ℤ) [F.Additive] (r : ℕ)
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (I : CochainComplex A ℤ) (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b)) :
    CochainComplex B ℤ :=
  letI := hasTotal F r hF I hI
  ((bicomplexFunctor F).obj I).total (.up ℤ)

/-- The (a,b) inclusion into degree n; it is zero if a+b differs from n.
Source: Stacks Tag 0133 (blueprint: lem-sfb-finite-exact-complex-derived-model). -/
def inclusion (F : A ⥤ CochainComplex B ℤ) [F.Additive] (r : ℕ)
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (I : CochainComplex A ℤ) (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b)) (a b n : ℤ) :
    (F.obj (I.X b)).X a ⟶ (total F r hF I hI).X n :=
  letI := hasTotal F r hF I hI
  ((bicomplexFunctor F).obj I).ιTotalOrZero (.up ℤ) a b n

/-- The total map induced by the actual maps F^a(g^b).
Source: Stacks Tags 0133 and 013P
(blueprint: lem-sfb-finite-exact-complex-derived-model). -/
def totalMap (F : A ⥤ CochainComplex B ℤ) [F.Additive] (r : ℕ)
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    {I J : CochainComplex A ℤ}
    (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b))
    (hJ : ∀ b : ℤ, b < 0 → IsZero (J.X b)) (g : I ⟶ J) :
    total F r hF I hI ⟶ total F r hF J hJ :=
  letI := hasTotal F r hF I hI
  letI := hasTotal F r hF J hJ
  HomologicalComplex₂.total.map ((bicomplexFunctor F).map g) (.up ℤ)

/-- The transposed total, with differential d_I + (-1)^b d_F.
Source: Stacks Tag 0133 (blueprint: lem-sfb-finite-exact-complex-derived-model). -/
def transposedTotal (F : A ⥤ CochainComplex B ℤ) [F.Additive] (r : ℕ)
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (I : CochainComplex A ℤ) (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b)) :
    CochainComplex B ℤ :=
  letI := hasTotal F r hF I hI
  ((bicomplexFunctor F).obj I).flip.total (.up ℤ)

/-- The transposed inclusion, labelled by the original bidegree (a,b).
Source: Stacks Tag 0133 (blueprint: lem-sfb-finite-exact-complex-derived-model). -/
def transposedInclusion (F : A ⥤ CochainComplex B ℤ) [F.Additive] (r : ℕ)
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (I : CochainComplex A ℤ) (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b)) (a b n : ℤ) :
    (F.obj (I.X b)).X a ⟶ (transposedTotal F r hF I hI).X n :=
  letI := hasTotal F r hF I hI
  ((bicomplexFunctor F).obj I).flip.ιTotalOrZero (.up ℤ) b a n

/-- The canonical signed interchange of the two total conventions.
Source: Stacks Tag 0133 (blueprint: lem-sfb-finite-exact-complex-derived-model). -/
def transpose (F : A ⥤ CochainComplex B ℤ) [F.Additive] (r : ℕ)
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (I : CochainComplex A ℤ) (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b)) :
    total F r hF I hI ≅ transposedTotal F r hF I hI :=
  letI := hasTotal F r hF I hI
  (((bicomplexFunctor F).obj I).totalFlipIso (.up ℤ)).symm

/-- Interchange multiplies bidegree (a,b) by (-1)^(ab), and is the identity on both axes.
Source: Stacks Tag 0133 (blueprint: lem-sfb-finite-exact-complex-derived-model).
Proof (node step 1): naturality of the model differential gives d_F d_I = d_I d_F.
For the horizontal arrow the two signs are (-1)^((a+1)b) and (-1)^(ab+b);
for the vertical arrow they are (-1)^a(-1)^(a(b+1)) and (-1)^(ab).
Thus the signed interchange is a chain map, its square is one, and ab=0 on either axis. -/
theorem transpose_components (F : A ⥤ CochainComplex B ℤ) [F.Additive] (r : ℕ)
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (I : CochainComplex A ℤ) (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b)) :
    (∀ a b n : ℤ,
      inclusion F r hF I hI a b n ≫ (transpose F r hF I hI).hom.f n =
        ((-1 : ℤˣ) ^ (a * b)) • transposedInclusion F r hF I hI a b n) ∧
    (∀ n : ℤ, inclusion F r hF I hI n 0 n ≫ (transpose F r hF I hI).hom.f n =
      transposedInclusion F r hF I hI n 0 n) ∧
    (∀ n : ℤ, inclusion F r hF I hI 0 n n ≫ (transpose F r hF I hI).hom.f n =
      transposedInclusion F r hF I hI 0 n n) := by
  sorry

/-- The total homotopy has component (-1)^a F^a(h^b) and no other bidegree components.
Source: Stacks Tags 0133 and 013S
(blueprint: lem-sfb-finite-exact-complex-derived-model).
Proof (node step 4): apply additivity to g₁-g₂=d_J h+h d_I. In dH+Hd the vertical
terms each have coefficient (-1)^a(-1)^a=1. Horizontal terms cancel, since their
coefficients are (-1)^a and (-1)^(a+1) and the model differential is natural.
All maps from a diagonal coproduct are determined by their components, proving the
homotopy equation including the zero degrees outside the quadrant. -/
theorem total_homotopy (F : A ⥤ CochainComplex B ℤ) [F.Additive] (r : ℕ)
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    {I J : CochainComplex A ℤ}
    (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b))
    (hJ : ∀ b : ℤ, b < 0 → IsZero (J.X b))
    (g₁ g₂ : I ⟶ J) (h : Homotopy g₁ g₂) :
    ∃ H : Homotopy (totalMap F r hF hI hJ g₁) (totalMap F r hF hI hJ g₂),
      ∀ a b n : ℤ, a + b = n →
        inclusion F r hF I hI a b n ≫ H.hom n (n - 1) =
          ((-1 : ℤˣ) ^ a) • (F.map (h.hom b (b - 1))).f a ≫
            inclusion F r hF J hJ a (b - 1) (n - 1) := by
  sorry

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The unit-normalized resolution isomorphism RG(QK) → QG(I).
Source: Stacks Tag 05TH (blueprint: lem-sfb-finite-exact-complex-derived-model).
Its two factors are RG(Qs) and the inverse of the specified unit at I. -/
def resolutionComparison (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    {K I : CochainComplex A ℤ} (s : K ⟶ I) [QuasiIso s] (hη : IsIso (η.app I)) :
    RG.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I) :=
  letI := hη
  asIso (RG.map (DerivedCategory.Q.map s)) ≪≫ (asIso (η.app I)).symm

/-- A finite exact cochain model computes RG naturally, independently of the resolution,
with the specified augmentation and derived-unit normalization.
Source: Stacks Tags 0133, 013P, 013S and 05TH; direct-image stability proof paragraph (3)
(blueprint: lem-sfb-finite-exact-complex-derived-model).

Proof (node steps 2--3 and 5--7):
1. Exactness of every F^a preserves each short exact cycle sequence in s. Consequently
F^a(X)[0] → F^a(I) is a quasi-isomorphism. Apply the first-quadrant axis-augmentation
lemma to the transpose. The transpose is the identity on the b=0 axis, giving c_s.
2. Naturality of e gives a chain map G(I) → B(I)^{0,*}. Its horizontal differential
vanishes because e is a chain map out of G(I^b)[0]. Each row augmentation is a
quasi-isomorphism since I^b is injective. The other axis-augmentation lemma gives b_s.
3. Both maps become invertible under Q. Set λ_s = Q(c_s) Q(b_s)⁻¹ ρ_s⁻¹, in diagrammatic
order. Naturality gives c_s e_X = G(s) b_s. Naturality of η and its invertibility at I
give η_X ρ_s = QG(s); hence Q(e_X) λ_s = η_X, with the single-complex transport.
4. For u:X→Y, lift u to a chain map between the nonnegative injective resolutions by
lem-weil-pbc-injective-resolution-lift-exists (Stacks 013P). Two lifts are homotopic
by lem-weil-pbc-lift-to-injective-unique-up-to-homotopy (Stacks 013S). The signed
homotopy above identifies their total maps after Q. The strict augmentation squares
and naturality of η give ρ_s QG(g) = RG(Qu[0]) ρ_t. Cancelling the isomorphisms proves
naturality. Taking u=1 compares any two resolutions in the same Hom set. -/
theorem finite_exact_complex_derived_model [EnoughInjectives A]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]
    (hη : ∀ (I : CochainComplex A ℤ),
      (∃ a : ℤ, ∀ b : ℤ, b < a → IsZero (I.X b)) →
      (∀ b : ℤ, Injective (I.X b)) → IsIso (η.app I))
    (r : ℕ) (F : A ⥤ CochainComplex B ℤ) [F.Additive]
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (hExact : ∀ a : ℤ,
      PreservesFiniteLimits (F ⋙ HomologicalComplex.eval B (.up ℤ) a) ∧
      PreservesFiniteColimits (F ⋙ HomologicalComplex.eval B (.up ℤ) a))
    (e : G ⋙ HomologicalComplex.single B (.up ℤ) 0 ⟶ F)
    (he : ∀ (X : A) [Injective X], QuasiIso (e.app X)) :
    ∃ comparison : F ⋙ DerivedCategory.Q ≅ DerivedCategory.singleFunctor A 0 ⋙ RG,
      (∀ X : A, DerivedCategory.Q.map (e.app X) ≫ comparison.hom.app X =
        DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app X) ≫
          η.app ((HomologicalComplex.single A (.up ℤ) 0).obj X)) ∧
      (∀ (X : A) (I : CochainComplex A ℤ)
        (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b))
        (hInj : ∀ b : ℤ, Injective (I.X b))
        (s : (HomologicalComplex.single A (.up ℤ) 0).obj X ⟶ I) [QuasiIso s],
        ∃ (c : F.obj X ⟶ total F r hF I hI)
          (b : (G.mapHomologicalComplex (.up ℤ)).obj I ⟶ total F r hF I hI),
          (∀ n : ℤ, c.f n =
            (F.map ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫ s.f 0)).f n ≫
              inclusion F r hF I hI n 0 n) ∧
          (∀ n : ℤ, b.f n =
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj (I.X n))).inv ≫
              (e.app (I.X n)).f 0 ≫ inclusion F r hF I hI 0 n n) ∧
          QuasiIso c ∧ QuasiIso b ∧
          comparison.hom.app X ≫ (resolutionComparison G RG η s (hη I ⟨0, hI⟩ hInj)).hom ≫
            DerivedCategory.Q.map b = DerivedCategory.Q.map c) := by
  sorry

/-- For the rank-zero identity model the comparison is the identity under the unique
unit-compatible identification of the derived identity functor with the identity.
Source: Stacks Tag 05TH, identity case
(blueprint: lem-sfb-finite-exact-complex-derived-model).
Proof (node step 8): when r=0, F(X)=X[0], G=id and e=1, the augmentation equation
says that the comparison is η at X[0]. The identity of the derived category with the
identity unit is itself the total right derived functor of the identity. The universal
property gives a unique isomorphism δ from the given RG to this identity functor,
compatible with the units on every complex. At X[0] this says comparison followed
by δ is the identity, for every resolution, without assuming X injective. -/
theorem identity_normalization
    (RG : DerivedCategory A ⥤ DerivedCategory A)
    (η : (𝟭 A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]
    (comparison : HomologicalComplex.single A (.up ℤ) 0 ⋙ DerivedCategory.Q ≅
      DerivedCategory.singleFunctor A 0 ⋙ RG)
    (hcomp : ∀ X : A, comparison.hom.app X =
      η.app ((HomologicalComplex.single A (.up ℤ) 0).obj X)) :
    ∃! δ : RG ≅ 𝟭 (DerivedCategory A),
      (∀ K : CochainComplex A ℤ, η.app K ≫ δ.hom.app (DerivedCategory.Q.obj K) =
        𝟙 (DerivedCategory.Q.obj K)) ∧
      (∀ X : A, comparison.hom.app X ≫
        δ.hom.app ((DerivedCategory.singleFunctor A 0).obj X) =
          𝟙 ((DerivedCategory.singleFunctor A 0).obj X)) := by
  sorry

end CategoryTheory.FiniteExactComplex
