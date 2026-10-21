module

public import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
public import Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Sheaf.CategoryTheory.KInjectiveComputes
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import Mathlib.Algebra.Homology.ModelCategory.Injective
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

/-! # Equivariant resolution-to-bar normalization

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
formal normalization helper (blueprint: lem-sfb-equivariant-resolution-bar-normalization).
The exact independent internal-bar reference remains wanted, as recorded by the DAG.

The models retain the actual internal Hom and its action on every profinite slice.
The two comparison cochain maps are specified by their components, and the conclusion
is an equality in the ordinary derived category, with its canonical computation unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction (trivial HomogeneousFunctions homogeneousEvaluate)
namespace CategoryTheory.CondensedBar

variable {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Read the existing homogeneous internal-Hom model on generalized free generators.
Source: the homogeneous-function normalization, paragraph (3)
(blueprint: lem-sfb-equivariant-resolution-bar-normalization). -/
def homogeneousValue {N : Modules A} {n : ℕ}
    (H : HomogeneousFunctions A.toMon G ((trivial (P := G)).obj N) n)
    (S : Profinite.{u}) (x : sections A H.object.module S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 1) → C(T, G)) : sections A N T :=
  homogeneousEvaluate A.toMon G ((trivial (P := G)).obj N) n S
    ((H.internalHom.hom.val.app (op S)).hom x) T f g

/-- A nonnegative homogeneous bar model with the displayed deletion differential and
constant augmentation. The term models reuse the recorded internal Hom and diagonal
argument action; the coefficient action is trivial. All specifications hold on slices.
Source: paragraph (3), the definition of R_N
(blueprint: lem-sfb-equivariant-resolution-bar-normalization). -/
structure HomogeneousBar (N : Modules A) where
  complex : CochainComplex (Equivariant A G) ℕ
  functions : ∀ n : ℕ, HomogeneousFunctions A.toMon G ((trivial (P := G)).obj N) n
  term : ∀ n : ℕ, complex.X n ≅ (functions n).object
  differential : ∀ (n : ℕ) (S : Profinite.{u}) (x : sections A (complex.X n).module S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 2) → C(T, G)),
    homogeneousValue (functions (n + 1)) S
      (((complex.d n (n + 1) ≫ (term (n + 1)).hom).val.hom.hom.app (op S)) x) T f g =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      homogeneousValue (functions n) S (((term n).hom.val.hom.hom.app (op S)) x)
        T f (fun j ↦ g (i.succAbove j))
  augmentation : (CochainComplex.single₀ (Equivariant A G)).obj
    ((trivial (P := G)).obj N) ⟶ complex
  constants : ∀ (S : Profinite.{u}) (x : sections A N S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin 1 → C(T, G)),
    homogeneousValue (functions 0) S
      (((augmentation.f 0 ≫ (term 0).hom).val.hom.hom.app (op S)) x) T f g =
      N.X.obj.map f.op x

/-- The ordered prefix tuple (1,g_1,g_1 g_2,...), including its empty product.
Source: paragraph (3), homogeneous/inhomogeneous coordinates
(blueprint: lem-sfb-equivariant-resolution-bar-normalization). -/
def prefixTuple {n : ℕ} {S : Profinite.{u}} (g : Fin n → C(S, G)) :
    Fin (n + 1) → C(S, G) :=
  fun j ↦ ((List.ofFn g).take j.val).prod

variable [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- Specify rho by restricting e to invariant sections and evaluating at ordered prefixes.
The quantified slices ensure internal evaluation, rather than evaluation on points only.
Source: paragraph (3), the definition of rho
(blueprint: lem-sfb-equivariant-resolution-bar-normalization). -/
def ResolutionEvaluation (M : Model A G) {N : Modules A} (H : HomogeneousBar (G := G) N)
    {K : CochainComplex (Equivariant A G) ℕ} (e : K ⟶ H.complex)
    (rho : (M.invariants.functor.mapHomologicalComplex (.up ℕ)).obj K ⟶
      (cochains M.bar).obj ((trivial (P := G)).obj N)) : Prop :=
  ∀ (n : ℕ) (S : Profinite.{u}) (x : sections A (M.invariants.functor.obj (K.X n)) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, G)),
    (M.functions.evaluate (power G n) S N
      (((rho.f n ≫ (M.bar.term ((trivial (P := G)).obj N) n).hom).hom.hom.app
        (op S)) x)).val T f (tupleMap g) =
    homogeneousValue (H.functions n) S
      (((M.invariants.inclusion.app (K.X n) ≫
        (e.f n ≫ (H.term n).hom).val).hom.hom.app (op S)) x) T f (prefixTuple g)

/-- Specify the underived-to-derived bar map on each finite-total summand: apply the
resolution augmentation to values and include the (n,0) component. This determines the
map uniquely, and retains the canonical compatible-resolution construction.
Source: paragraph (3), the definition of j
(blueprint: lem-sfb-equivariant-resolution-bar-normalization). -/
def UnderivedBarComponents (M : Model A G) (N : Modules A)
    (I : InjectiveResolution ((trivial (P := G)).obj N))
    (j : (cochains M.bar).obj ((trivial (P := G)).obj N) ⟶
      (totalCochains M.bar).obj I.cocomplex) : Prop :=
  ∀ n : ℕ, j.f n = ((cochains M.bar).map (I.ι.f 0)).f n ≫
    (doubleComplex M.bar I.cocomplex).ιTotal (.up ℕ) n 0 n (by simp)

/-- The specified nonnegative augmentation as a map from the ordinary degree-zero
complex. Only the canonical extension-of-single identification is inserted.
Source: paragraph (3), Q(a)
(blueprint: lem-sfb-equivariant-resolution-bar-normalization). -/
def localizedAugmentation {N : Equivariant A G} {K : CochainComplex (Equivariant A G) ℕ}
    (a : (CochainComplex.single₀ (Equivariant A G)).obj N ⟶ K) [QuasiIso a] :
    (DerivedCategory.singleFunctor (Equivariant A G) 0).obj N ≅
      DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat) :=
  DerivedCategory.Q.mapIso
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N 0 0 (by simp)).symm ≪≫
      asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat))

/-- The canonical right-derived unit, transported through extension by zero. This is
u_K, with domain the localization of the actual nonnegative invariant complex.
Source: paragraph (3), the canonical right-derived unit of def-sfb-right-derived-functor
(blueprint: lem-sfb-equivariant-resolution-bar-normalization). -/
def invariantUnit (V : Invariants A G) (K : CochainComplex (Equivariant A G) ℕ) :
    DerivedCategory.Q.obj (extend ((V.functor.mapHomologicalComplex (.up ℕ)).obj K)) ⟶
      V.functor.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat)) :=
  DerivedCategory.Q.map
    (HomologicalComplex.mapExtendIso K ComplexShape.embeddingUpNat V.functor).inv ≫
      V.functor.rightDerivedFunctorUnitQ (K.extend ComplexShape.embeddingUpNat)

/-- Evaluation from an arbitrary nonnegative equivariant resolution has the normalized
ordinary derived bar arrow. Both rho and j are fixed by their component formulas;
epsilon is the existing normalized compatible-resolution isomorphism.
Source: main-20261015 six-functors direct-images proof, paragraph (3), formal helper
(blueprint: lem-sfb-equivariant-resolution-bar-normalization).

Proof:
1. By lem-sfb-condensed-derived-restriction-calculus and
   lem-sp-grothendieck-enough-injectives choose a nonnegative equivariant injective
   resolution s:N[0] -> I (def-sp-injective-resolutions). It is K-injective by
   lem-sp-kinjective-computes.
2. Free A[S] is extension by zero from the slice by its universal property and the
   internal/section-module equivalence. It is flat by lem-pc-sites-modules-j-shriek-flat.
   Induction A[G] tensor - is the exact left adjoint of forgetting, so forgetting
   preserves injectives by lem-sp-right-adjoint-preserves-injectives; Us is injective.
3. Form T^{p,q}=Hom(A[G^{p+1}],UI^q), with diagonal argument and coefficient actions.
   The terms are equivariantly injective by lem-sfb-internal-homogeneous-functions-injective.
   Its finite-diagonal total (def-sp-double-complex-total) has injective terms and
   differential d_h+(-1)^p d_v. Constants give an equivariant map delta:I -> Tot T.
4. The slice formulas f -> f(1,g1,g1g2,...) and
   c -> ((h0,...,hp) -> h0.c(h0^-1 h1,...,h(p-1)^-1 hp)) give inverse cochain maps
   chi:Gamma(Tot T) -> V. Deletion gives the inhomogeneous faces; invariants commute
   with the finite biproducts. Put v=chi Gamma(delta).
5. With Us as the compatible resolution in every internal Hom, the normalized bar
   theorem lem-sfb-condensed-derived-invariant-bar identifies QV with the derived bar
   and epsilon=Q(v)c_s, where c_s=u_I^-1 RF(Qs). The map j is the (p,0) inclusion
   after postcomposition with s^0 (def-sfb-condensed-equivariant-bar-data).
6. Postcomposition by s^0 gives t:R_N -> Tot T. Since d_I s^0=0 it is a cochain map.
   The prefix formula for rho and the components of j give chi Gamma(te)=j_chain rho.
7. Since K vanishes below zero, the quasi-isomorphism a is degreewise monic: in degree
   zero H^0(K)=ker d^0. Apply lem-weil-pbc-lift-along-injective-quasi-iso to lift s
   to an equivariant b:K -> I with ba=s.
8. Both te and delta b agree after a, by the constant augmentation. The injective
   target T and lem-weil-pbc-lift-to-injective-unique-up-to-homotopy give te~delta b.
   Additive invariants preserve that homotopy, so Q(chi) QGamma(te)=Q(v) QGamma(b).
9. Naturality of the canonical right-derived unit (def-sfb-right-derived-functor)
   gives QGamma(b)=u_I^-1 RF(Qb) u_K. Since ba=s, RF(Qb)=RF(Qs) RF(Qa)^-1.
   Substitute steps 5, 6 and 8 to obtain the displayed equality. No injectivity or
   invariant-acyclicity assumption was used for K^n or R_N^n.
-/
theorem equivariant_resolution_bar_normalization (M : Model A G) (N : Modules A)
    (H : HomogeneousBar (G := G) N) (K : CochainComplex (Equivariant A G) ℕ)
    (a : (CochainComplex.single₀ (Equivariant A G)).obj ((trivial (P := G)).obj N) ⟶ K)
    [QuasiIso a] (e : K ⟶ H.complex) (hea : a ≫ e = H.augmentation)
    (rho : (M.invariants.functor.mapHomologicalComplex (.up ℕ)).obj K ⟶
      (cochains M.bar).obj ((trivial (P := G)).obj N))
    (hrho : ResolutionEvaluation M H e rho)
    (I : InjectiveResolution ((trivial (P := G)).obj N))
    (j : (cochains M.bar).obj ((trivial (P := G)).obj N) ⟶
      (totalCochains M.bar).obj I.cocomplex) (hj : UnderivedBarComponents M N I j) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap rho ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap j ComplexShape.embeddingUpNat) =
    invariantUnit M.invariants K ≫
      (M.invariants.functor.rightDerivedFunctor.mapIso (localizedAugmentation a)).inv ≫
        (M.computation.iso I).hom := by
  sorry

end CategoryTheory.CondensedBar
