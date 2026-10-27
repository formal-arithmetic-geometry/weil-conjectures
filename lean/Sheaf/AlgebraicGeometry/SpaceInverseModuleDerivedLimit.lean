module

public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQCohTriangulated
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.SpaceChartLimitEnlargedSections
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.AlgebraicGeometry.SpaceDerivedCoheratorAdjunction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Derived limits of infinitesimal module systems on algebraic spaces

Source: Stacks Project, spaces-flat.tex, Tag 0CX5, lemma-compute-what-it-should-be,
and spaces-perfect.tex, Tag 0CST, example-inverse-limit-quasi-coherent
(blueprint: lem-sfb-space-inverse-module-derived-limit).

The natural-number index n represents the paper's level n + 1. All fibre products,
tensor pullbacks, direct images, and transition maps are the existing canonical ones.
Products and the Roos triangles are formed in the full category D_QCoh.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Spec of a ring, with its unique map to Spec Z in the chosen scheme universe.
Source: Stacks, 0CX5, situation-existence
(blueprint: lem-sfb-space-inverse-module-derived-limit). -/
def inverseModuleSpec (R : CommRingCat.{u}) : Over (Spec (.of (ULift.{u} ℤ))) :=
  Over.mk (specULiftZIsTerminal.from (Spec R))

/-- The actual contravariant spectrum map over Spec Z.
Source: Stacks, 0CX5, situation-existence
(blueprint: lem-sfb-space-inverse-module-derived-limit). -/
def inverseModuleSpecMap {R R' : CommRingCat.{u}} (a : R ⟶ R') :
    inverseModuleSpec R' ⟶ inverseModuleSpec R :=
  Over.homMk (Spec.map a) (specULiftZIsTerminal.hom_ext _ _)

/-- The test scheme Spec A_n over Spec A from the specified ring limit cone.
Source: Stacks, 0CX5, situation-existence
(blueprint: lem-sfb-space-inverse-module-derived-limit). -/
def inverseModuleTest {A : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, A (n + 1) ⟶ A n}
    (c : Cone (Functor.ofOpSequence r)) (n : ℕ) :
    ProperQuotTest (schemeSpace (inverseModuleSpec c.pt)) :=
  CostructuredArrow.mk (yoneda.map (inverseModuleSpecMap (c.π.app (op n))))

/-- The cone equation, viewed as the commuting triangle of the actual test schemes.
Source: Stacks, 0CX5, situation-existence
(blueprint: lem-sfb-space-inverse-module-derived-limit).
Proof: the ring cone equation is pi_(n+1) followed by r_n = pi_n. Apply Spec,
which reverses composition, then the over-category Yoneda functor. The spectrum
maps are over Spec Z because this scheme is terminal. -/
theorem inverseModuleTestMap_w {A : ℕ → CommRingCat.{u}}
    {r : ∀ n : ℕ, A (n + 1) ⟶ A n} (c : Cone (Functor.ofOpSequence r)) (n : ℕ) :
    yoneda.map (inverseModuleSpecMap (r n)) ≫ (inverseModuleTest c (n + 1)).hom =
      (inverseModuleTest c n).hom := by
  sorry

/-- The transition Spec A_n to Spec A_(n+1) as a map of test schemes over Spec A.
Source: Stacks, 0CX5, situation-existence
(blueprint: lem-sfb-space-inverse-module-derived-limit). -/
def inverseModuleTestMap {A : ℕ → CommRingCat.{u}}
    {r : ∀ n : ℕ, A (n + 1) ⟶ A n} (c : Cone (Functor.ofOpSequence r)) (n : ℕ) :
    inverseModuleTest c n ⟶ inverseModuleTest c (n + 1) :=
  CostructuredArrow.homMk (inverseModuleSpecMap (r n)) (inverseModuleTestMap_w c n)

/-- The quotient transition on pushforwards, normalized by the tensor composition
comparison and the pullback/direct-image counit. This is the adjoint of pulling the
counit back to X_n and following it by the specified reduction isomorphism.
Source: Stacks, 0CX5, situation-existence; Modules on Sites, 03D7
(blueprint: lem-sfb-space-inverse-module-derived-limit). -/
def inverseModuleTransition {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (j : Y ⟶ X) (j' : Y' ⟶ X) (k : Y ⟶ Y') (h : k ≫ j' = j)
    (M : Y.Modules) (M' : Y'.Modules) (e : (moduleTensorPullback k).obj M' ≅ M) :
    (moduleDirectImage j').obj M' ⟶ (moduleDirectImage j).obj M :=
  (moduleTensorAdjunction j).homEquiv _ _
    ((eqToIso (congrArg (fun a ↦
        (moduleTensorPullback a).obj ((moduleDirectImage j').obj M')) h)).inv ≫
      (moduleTensorComposition k j').inv.app ((moduleDirectImage j').obj M') ≫
      (moduleTensorPullback k).map ((moduleTensorAdjunction j').counit.app M') ≫ e.hom)

/-- The direct image on X in degree zero, transported by the fixed small-site equivalence.
Source: Stacks, 0CX5 and 0CST
(blueprint: lem-sfb-space-inverse-module-derived-limit). -/
def inverseModuleDerivedTerm {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] {B : AlgebraicSpace S}
    (f : X ⟶ B) (T : ProperQuotTest B) (M : (properQuotFibre f T).Modules) :
    X.DerivedModules :=
  (DerivedCategory.singleFunctor X.SmallModules 0).obj
    (X.smallModuleRestriction.obj ((moduleDirectImage (properQuotFst f T)).obj M))

/-- A degree-zero term with its quasi-coherent-cohomology certificate, in the full category.
Source: Stacks, 0CST (blueprint: lem-sfb-space-inverse-module-derived-limit). -/
def inverseModuleQCohTerm {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] {B : AlgebraicSpace S}
    (f : X ⟶ B) (T : ProperQuotTest B) (M : (properQuotFibre f T).Modules)
    (h : X.derivedQCohProperty (inverseModuleDerivedTerm f T M)) : X.DerivedQCoh :=
  ⟨inverseModuleDerivedTerm f T M, h⟩

/-- The inverse-system arrow in D_QCoh is the image of the specified quotient map,
not an independently chosen morphism of derived objects.
Source: Stacks, 0CX5, situation-existence; 0CST
(blueprint: lem-sfb-space-inverse-module-derived-limit). -/
def inverseModuleDerivedTransition {S : Scheme.{u}} {X B : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] (f : X ⟶ B)
    {T T' : ProperQuotTest B} (a : T ⟶ T')
    (M : (properQuotFibre f T).Modules) (M' : (properQuotFibre f T').Modules)
    (e : (moduleTensorPullback (properQuotFibreMap f a)).obj M' ≅ M)
    (h : X.derivedQCohProperty (inverseModuleDerivedTerm f T M))
    (h' : X.derivedQCohProperty (inverseModuleDerivedTerm f T' M')) :
    inverseModuleQCohTerm f T' M' h' ⟶ inverseModuleQCohTerm f T M h :=
  ObjectProperty.homMk ((DerivedCategory.singleFunctor X.SmallModules 0).map
    (X.smallModuleRestriction.map (inverseModuleTransition
      (properQuotFst f T) (properQuotFst f T') (properQuotFibreMap f a)
      (properQuotFibreMap_fst f a) M M' e)))

/-- The homotopy inverse limit in D_QCoh exists, is bounded with no negative
cohomology, and the projections of every specified product triangle are compatible.
Source: Stacks, spaces-flat.tex, Tag 0CX5, lemma-compute-what-it-should-be,
and spaces-perfect.tex, Tag 0CST, example-inverse-limit-quasi-coherent
(blueprint: lem-sfb-space-inverse-module-derived-limit).

Proof:
1. Surjective ring transitions make every limit projection surjective by recursive
   lifting. Hence X_n to X is a closed immersion, thus quasi-compact and separated.
   The quasi-coherent pushforward theorem makes its module direct image quasi-coherent;
   the chart-limit comparison identifies this with the ringed-topos direct image.
   Finite presentation over the affine base makes X quasi-compact and quasi-separated.
2. On the equivalent small ringed model resolve by K-injectives. Sectionwise module
   limits and the K-injective product theorem give the ambient derived product B.
   The derived-limit existence theorem gives L to B to B to L[1], with middle map 1-s.
3. The derived coherator adjunction identifies Hom(P,DQ B) with the product of
   Hom(P,M_n), for every P in D_QCoh. Thus DQ B is its product. Naturality identifies
   DQ(1-s) with its transition endomorphism. The triangulated coherator takes the
   ambient triangle to a product triangle. Derived-limit uniqueness identifies any
   other specified homotopy limit K with DQ L.
4. On each affine etale chart U, localization and the derived-evaluation/slice
   comparison identify derived sections with slice cohomology. Scheme Zariski/etale
   quasi-coherent comparison and affine etale acyclicity identify RΓ(U,M_n) with
   Γ(U,M_n)[0]. Derived sections commute with derived limits.
5. The Milnor sequence gives H^i(U,L)=0 outside [0,1], uniformly in affine etale U:
   both adjacent stage cohomologies vanish there. No Mittag-Leffler condition is used.
6. The coherator bound applied to [0,1] gives a finite interval [0,1+N] for DQ L,
   hence for every K above. Its cohomology is quasi-coherent by its subcategory type.
7. Consecutive triangle arrows compose to zero: p(1-s)=0. Compose with projection n
   to get p pr_n = p pr_(n+1) t_n. These are the projections of the very same triangle.
-/
theorem inverseModuleDerivedLimit
    (A : ℕ → CommRingCat.{u}) (r : ∀ n : ℕ, A (n + 1) ⟶ A n)
    (hsurj : ∀ n : ℕ, Function.Surjective (r n))
    (hnil : ∀ (n : ℕ) (a : A (n + 1)), (r n) a = 0 → IsNilpotent a)
    (c : Cone (Functor.ofOpSequence r)) (hc : IsLimit c)
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    [HasDerivedCategory.{w} X.SmallModules]
    (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (hsep : MapIsSeparated f) (hfp : ProperQuotFinitePresentation f)
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (hqc : ∀ n : ℕ, (M n).IsQuasicoherent)
    (hfin : ∀ n : ℕ, (M n).IsFinitePresentation)
    (hflat : ∀ (n : ℕ) (U : (properQuotFibre f (inverseModuleTest c n)).EtaleSite),
      ((schemeRestriction _ U).obj (M n)).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ (properQuotSnd f (inverseModuleTest c n)).hom.hom)).left)
    (hsupp : ∀ n : ℕ, ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
      (i : Z ⟶ properQuotFibre f (inverseModuleTest c n)),
      IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left) i.hom.hom ∧
      MapIsProper (i ≫ properQuotSnd f (inverseModuleTest c n)) ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M n))
    (e : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj
        (M (n + 1)) ≅ M n) :
    ∃ hq : ∀ n : ℕ,
        X.derivedQCohProperty (inverseModuleDerivedTerm f (inverseModuleTest c n) (M n)),
      HasProduct (fun n : ℕ ↦ inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n)) ∧
      ∀ [HasProduct (fun n : ℕ ↦
          inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))],
        (∃ (K : X.DerivedQCoh)
          (p : K ⟶ ∏ᶜ (fun n : ℕ ↦
            inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n)))
          (δ : (∏ᶜ (fun n : ℕ ↦
            inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))) ⟶ K⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle (fun n : ℕ ↦ inverseModuleDerivedTransition f
            (inverseModuleTestMap c n) (M n) (M (n + 1)) (e n) (hq n) (hq (n + 1))) K p δ) ∧
        ∀ (K : X.DerivedQCoh)
          (p : K ⟶ ∏ᶜ (fun n : ℕ ↦
            inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n)))
          (δ : (∏ᶜ (fun n : ℕ ↦
            inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))) ⟶ K⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle (fun n : ℕ ↦ inverseModuleDerivedTransition f
            (inverseModuleTestMap c n) (M n) (M (n + 1)) (e n) (hq n) (hq (n + 1))) K p δ →
          (∃ b : ℤ, ∀ i : ℤ, b < i →
            IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj K.obj)) ∧
          (∀ i : ℤ, i < 0 →
            IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj K.obj)) ∧
          ∀ n : ℕ,
            p ≫ Pi.π (fun m : ℕ ↦
              inverseModuleQCohTerm f (inverseModuleTest c m) (M m) (hq m)) n =
            p ≫ Pi.π (fun m : ℕ ↦
              inverseModuleQCohTerm f (inverseModuleTest c m) (M m) (hq m)) (n + 1) ≫
              inverseModuleDerivedTransition f (inverseModuleTestMap c n)
                (M n) (M (n + 1)) (e n) (hq n) (hq (n + 1)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
