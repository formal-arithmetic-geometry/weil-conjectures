/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.PbcActualScalarPullback
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Paper.LocallyConstantTensor
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Finite reduction and constructibility

Source: main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-reduction,
first paragraph; Stacks Tags 08G1, 06YQ, 094H and 09AL
(blueprint: lem-pur-finite-reduction-constructibility).

## Main definitions

* `AlgebraicGeometry.FiniteReduction.System`: universal derived extensions with
  canonical representative normalizations.
* `AlgebraicGeometry.FiniteReduction.System.CoherentAt`: their associator square.

## Main statements

* `AlgebraicGeometry.FiniteReduction.finiteReduction_constructibility`: finite reduction,
  its bounded flat models, intrinsic finiteness and coherent etale origin.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteReduction

/-- Size lift of the actual quotient ring. Source: blueprint sk-lem-sp-reduction,
finite coefficients (blueprint: lem-pur-finite-reduction-constructibility). -/
abbrev Ring (l r : ℕ) := ULift.{u} (ZMod (l ^ r))

/-- Module-size lift of the same coefficient ring. Source: blueprint sk-lem-sp-reduction,
finite coefficients (blueprint: lem-pur-finite-reduction-constructibility). -/
abbrev Coeff (l r : ℕ) := ULift.{u + 1} (Ring.{u} l r)

/-- The actual quotient map, lifted to the module universe. Source: blueprint
sk-lem-sp-reduction (blueprint: lem-pur-finite-reduction-constructibility). -/
def quotient (l : ℕ) {r m : ℕ} (h : m ≤ r) : Coeff.{u} l r →+* Coeff.{u} l m :=
  ((ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m))).ulift).ulift

section Site
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B)

/-- Scalar extension is sheafification of sectionwise scalar extension; it does not
assume the quotient is flat. Source: Stacks 06YY
(blueprint: lem-pur-finite-reduction-constructibility). -/
def extend : Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J (ModuleCat.{u + 1} B) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f)

/-- The standard tensor/restriction adjunction, fixing all tensor units. Source: Stacks
06YY (blueprint: lem-pur-finite-reduction-constructibility). -/
def extendAdjunction : extend J f ⊣ Sheaf.restrictScalars J f :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1} f)

/-- Additivity comes from the tensor/restriction adjunction. Source: Stacks 06YY
(blueprint: lem-pur-finite-reduction-constructibility). -/
instance extend_additive : (extend J f).Additive :=
  (extendAdjunction J f).left_adjoint_additive

set_option genSizeOf false in
set_option genInjectivity false in
/-- A universal derived tensor extension, including its canonical K-flat computation.
This records the universal pair, rather than an unspecified functor or isomorphism.
Source: Stacks 06YT and 06YY
(blueprint: lem-pur-finite-reduction-constructibility). -/
structure DerivedExtension where
  functor : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))
  counit : DerivedCategory.Q ⋙ functor ⟶
    (extend J f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : functor.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ))
  computation : ∀ P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P → IsIso (counit.app P)

end Site

/-- Canonical ordinary comparison: both sides are left adjoint to the same restriction
functor. Its normalization is the identity on that right adjoint, hence on local pure
tensors. Source: Stacks 03EL
(blueprint: lem-pur-finite-reduction-constructibility). -/
def ordinaryComparison (T : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (f : A →+* B) :
    extend T.smallEtaleTopology f ⋙ ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ extend (Scheme.ProEt.topology T) f :=
  Adjunction.leftAdjointUniq
    ((extendAdjunction T.smallEtaleTopology f).comp (ProEtale.comparisonAdjunction _ T))
    ((ProEtale.comparisonAdjunction _ T).comp
      (extendAdjunction (Scheme.ProEt.topology T) f))

/-- The ordinary tensor associator, fixed by the identity on scalar restriction.
On local tensors it sends c tensor (b tensor q) to (bc) tensor q, equivalently
(q tensor b) tensor c to q tensor bc in the right-tensor convention of the source.
Source: blueprint sk-lem-sp-reduction, associativity
(blueprint: lem-pur-finite-reduction-constructibility). -/
def ordinaryAssociator {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    (l : ℕ) {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m) :
    extend J (quotient.{u} l hmr) ⋙ extend J (quotient l hnm) ≅
      extend J (quotient l (hnm.trans hmr)) :=
  Adjunction.leftAdjointUniq
    (((extendAdjunction J (quotient l hmr)).comp
      (extendAdjunction J (quotient l hnm))).ofNatIsoRight
        (Sheaf.restrictScalarsCompIso J (quotient l hmr) (quotient l hnm)
          (quotient l (hnm.trans hmr))
          (RingHom.ext (fun x ↦
            congrArg (fun y : ZMod (l ^ n) ↦ (⟨⟨y⟩⟩ : Coeff.{u} l n))
              (DFunLike.congr_fun
                (Subsingleton.elim
                  (ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n)))
                  ((ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))).comp
                    (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m))))) x.down.down)))))
    (extendAdjunction J (quotient l (hnm.trans hmr)))

/-- The actual termwise comparison on complexes. Source: Stacks 03EL
(blueprint: lem-pur-finite-reduction-constructibility). -/
abbrev ordinaryComparisonComplex (T : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (f : A →+* B) :=
  NatIso.mapHomologicalComplex (ordinaryComparison T f) (.up ℤ)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Canonical coefficient extension on the two sites, including representative
normalizations of its comparison and its associators. All functors are universal derived
functors of the concrete scalar extensions above. The normalizations remove arbitrary
choices of natural isomorphisms. Source: Stacks 06YT, 06YY and 03EL; blueprint
sk-lem-sp-reduction (blueprint: lem-pur-finite-reduction-constructibility). -/
structure System (T : Scheme.{u}) (l : ℕ) where
  etale : ∀ (r m : ℕ) (h : m ≤ r),
    DerivedExtension T.smallEtaleTopology (quotient.{u} l h)
  proetale : ∀ (r m : ℕ) (h : m ≤ r),
    DerivedExtension (Scheme.ProEt.topology T) (quotient.{u} l h)
  comparison : ∀ (r m : ℕ) (h : m ≤ r),
    (etale r m h).functor ⋙
      (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory ≅
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory ⋙
      (proetale r m h).functor
  comparison_model : ∀ (r m : ℕ) (h : m ≤ r)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (comparison r m h).hom.app (DerivedCategory.Q.obj P) ≫
      (proetale r m h).functor.map
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategoryFactors.hom.app P) ≫
      (proetale r m h).counit.app
        (((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapHomologicalComplex (.up ℤ)).obj P) =
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory.map
      ((etale r m h).counit.app P) ≫
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategoryFactors.hom.app
        (((extend T.smallEtaleTopology (quotient l h)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map ((ordinaryComparisonComplex T (quotient l h)).hom.app P)
  etaleAssociator : ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m),
    (etale r m hmr).functor ⋙ (etale m n hnm).functor ≅
      (etale r n (hnm.trans hmr)).functor
  proetaleAssociator : ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m),
    (proetale r m hmr).functor ⋙ (proetale m n hnm).functor ≅
      (proetale r n (hnm.trans hmr)).functor
  etaleAssociator_model : ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (etaleAssociator r m n hmr hnm).hom.app (DerivedCategory.Q.obj P) ≫
      (etale r n (hnm.trans hmr)).counit.app P =
    (etale m n hnm).functor.map ((etale r m hmr).counit.app P) ≫
      (etale m n hnm).counit.app
        (((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          (ordinaryAssociator T.smallEtaleTopology l hmr hnm) (.up ℤ)).hom.app P)
  proetaleAssociator_model : ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (P : CochainComplex
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (proetaleAssociator r m n hmr hnm).hom.app (DerivedCategory.Q.obj P) ≫
      (proetale r n (hnm.trans hmr)).counit.app P =
    (proetale m n hnm).functor.map ((proetale r m hmr).counit.app P) ≫
      (proetale m n hnm).counit.app
        (((extend (Scheme.ProEt.topology T) (quotient l hmr)).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          (ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm) (.up ℤ)).hom.app P)

/-- The associator square at a given etale object. Source: blueprint
sk-lem-sp-reduction, final sentence of the first paragraph
(blueprint: lem-pur-finite-reduction-constructibility). -/
def System.CoherentAt {T : Scheme.{u}} {l : ℕ} (S : System T l)
    (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r)))) : Prop :=
    (S.comparison m n hnm).hom.app ((S.etale r m hmr).functor.obj K) ≫
      (S.proetale m n hnm).functor.map ((S.comparison r m hmr).hom.app K) ≫
      (S.proetaleAssociator r m n hmr hnm).hom.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory.obj K) =
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l n)) T).mapDerivedCategory.map
      ((S.etaleAssociator r m n hmr hnm).hom.app K) ≫
      (S.comparison r n (hnm.trans hmr)).hom.app K

/-- Finiteness of the actual coefficients, derived from primality, not an extra
hypothesis. Source: blueprint sk-lem-sp-reduction
(blueprint: lem-pur-finite-reduction-constructibility). -/
instance ringFinite (l : ℕ) [h : Fact l.Prime] (r : ℕ) : Finite (Ring.{u} l r) := by
  let : NeZero l := ⟨h.out.ne_zero⟩
  infer_instance

/-- The canonical realization in the intrinsic constant-ring presentation, used solely
to apply the recorded intrinsic constructibility and Tor predicates. Source: Stacks 00YV
and 09AL (blueprint: lem-pur-finite-reduction-constructibility). -/
def realize (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r))) ⥤
      Scheme.proEtaleDerivedCategory T (Ring.{u} l r) :=
  (ProEtale.finiteCoefficientIntrinsicRealization.{u} T (Ring.{u} l r)).mapDerivedCategory

/-- The origin comparison for the specified isomorphism, with no new choice of map.
Source: blueprint sk-lem-sp-reduction, first paragraph
(blueprint: lem-pur-finite-reduction-constructibility). -/
def System.originComparison {T : Scheme.{u}} {l : ℕ} (S : System T l)
    {r m : ℕ} (h : m ≤ r)
    {K₀ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r)))}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r)))}
    (e : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory.obj K₀ ≅ K) :
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory.obj
      ((S.etale r m h).functor.obj K₀) ≅ (S.proetale r m h).functor.obj K :=
  (S.comparison r m h).app K₀ ≪≫ (S.proetale r m h).functor.mapIso e

/-- Finite quotient reduction preserves bounded intrinsic constructibility and the exact
Tor interval, with bounded flat etale representatives and the canonical coherent origin
comparison. The pro-etale objects use fixed-scalar sheaves; `realize` is the recorded
canonical exact equivalence to modules over the constant ring sheaf. Thus every intrinsic
predicate is exactly the recorded one, and tests all pro-etale module sheaves.

Source: main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-reduction,
first paragraph; Stacks 08G1, 06YQ, 094H and 09AL
(blueprint: lem-pur-finite-reduction-constructibility).

Proof (the node's ten steps):
1. Reflect Tor amplitude from K to its specified bounded etale origin by
lem-exc-comparison-tor-interval; the canonical realization changes only presentation.
2. Apply lem-sf-etale-flat-model to the ordered interval. The model Q is zero outside
[a,b], with flat terms; no constructibility of its terms or Noetherian base is needed.
Apply lem-pc-bounded-above-flat-kflat-site to obtain K-flatness.
3. Apply lem-pur-kflat-change-of-rings to the constant quotient ring map. The ordinary
extension Q_m has flat terms and is K-flat. By lem-pur-derived-change-of-rings its
image represents the derived extension of K_0. It remains zero outside [a,b].
4. Tensor Q_m with each arbitrary degree-zero A_m-module sheaf. The tensor is zero
outside [a,b], giving etale Tor amplitude and boundedness of the reduction.
5. Exact comparison commutes with the constant ring maps, sheaf tensor products and
coequalizers by lem-sf-comparison-pullback-exact and
lem-weil-pbc-left-exact-site-inverse-image-tensor. This is ordinaryComparison: its
adjunction conjugate fixes the local tensor generators. Apply it degreewise to Q.
Pullback preserves flat K-flat models by lem-weil-pbc-ringed-topoi-derived-tensor-pullback;
canonical derived computation yields comparison_model, independently of Q.
6. Apply the forward implication of lem-exc-comparison-tor-interval to Q_m's bounded
etale derived object. This gives Tor amplitude against all pro-etale test sheaves.
7. Refine the finitely many constructible stratifications of the cohomology of K_0
using lem-weil-pbc-constructible-stratification-intersection and
lemma-constructible-of-refines. Exact inverse image commutes with cohomology, so each
restriction is bounded with finite locally constant cohomology.
8. On each stratum use lem-weil-pbc-locally-constant-tensor (Stacks 094H). A_r is finite,
hence Noetherian, and A_m is finite over A_r. The resulting cohomology is finite locally
constant over A_r. Its A_m-action and the surjection A_r to A_m make the same local
trivializations A_m-linear; use lem-weil-pbc-finite-locally-constant-module-values.
9. The common stratification proves etale constructibility of every reduced cohomology
sheaf. The finite-ring constructible-derived-origin equivalence, for A_m, makes its
comparison bounded and intrinsically constructible; originComparison identifies it
with the reduction of K through the specified e.
10. Successive extension is represented by (Q tensor A_m) tensor A_n. The two ordinary
adjunctions identify its associator with (q tensor b) tensor c mapping to q tensor bc,
with inverse q tensor c mapping to (q tensor 1) tensor c. Balancing gives well-defined
inverse maps and differentials act on q alone. Both routes through comparison send a
pure tensor to the image of q tensored with bc; sheafification and localization preserve
that equality. This proves the two representative normalizations and coherence in System.
Existence of K-flat resolutions supplies the universal derived extensions in that system;
no flatness of A_m over A_r is used. -/
theorem finiteReduction_constructibility (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (_hinvert : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) :
    ∃ S : System T l,
    ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r) (a b : ℤ) (_hab : a ≤ b)
      (K : DerivedCategory
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r))))
      (_hconstructible : ∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T (Ring.{u} l r)
        ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T (Ring.{u} l r))) i).obj
            ((realize T l r).obj K)))
      (_hbounded : ∃ c d : ℤ, c ≤ d ∧ ∀ i : ℤ, (i < c ∨ d < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T (Ring.{u} l r))) i).obj
            ((realize T l r).obj K)))
      (_htor : Scheme.HasProEtaleTorAmplitude T (Ring.{u} l r)
        ((realize T l r).obj K) a b)
      (K₀ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))))
      (_hK₀ : Etale.DerivedCategory.isBoundedConstructible (Coeff.{u} l r) T K₀)
      (e : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory.obj K₀ ≅ K),
    Etale.DerivedCategory.hasTorAmplitudeIn (Coeff.{u} l r) T a b K₀ ∧
    ∃ Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ,
      Etale.IsBoundedFlatComplex (Coeff.{u} l r) a b Q ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q ∧
      Nonempty (K₀ ≅ DerivedCategory.Q.obj Q) ∧
      Etale.IsBoundedFlatComplex (Coeff.{u} l m) a b
        (((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj Q) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj Q) ∧
      Nonempty ((S.etale r m hmr).functor.obj K₀ ≅ DerivedCategory.Q.obj
        (((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
      Etale.DerivedCategory.isBoundedConstructible (Coeff.{u} l m) T
        ((S.etale r m hmr).functor.obj K₀) ∧
      (∃ origin :
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory.obj
          ((S.etale r m hmr).functor.obj K₀) ≅ (S.proetale r m hmr).functor.obj K,
        origin.hom = (S.comparison r m hmr).hom.app K₀ ≫
          (S.proetale r m hmr).functor.map e.hom) ∧
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T (Ring.{u} l m)
        ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T (Ring.{u} l m))) i).obj
            ((realize T l m).obj ((S.proetale r m hmr).functor.obj K)))) ∧
      (∃ c d : ℤ, c ≤ d ∧ ∀ i : ℤ, (i < c ∨ d < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T (Ring.{u} l m))) i).obj
            ((realize T l m).obj ((S.proetale r m hmr).functor.obj K)))) ∧
      Scheme.HasProEtaleTorAmplitude T (Ring.{u} l m)
        ((realize T l m).obj ((S.proetale r m hmr).functor.obj K)) a b ∧
      ∀ (n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m), S.CoherentAt r m n hmr hnm K₀ := by
  sorry

end AlgebraicGeometry.FiniteReduction
