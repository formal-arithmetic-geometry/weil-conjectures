/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.Paper.LatticeSheafBasic
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.ContinuousRingUniverseRealization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Analysis.Normed.Algebra.Ultra
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.SixFunctors.IntegralLisseReductionEquivalence
import Sheaf.Paper.NormalProEtaleMonodromy
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import Sheaf.Paper.ContinuousLocallyFreePullback
import Sheaf.Paper.ContinuousSetDescentComponents

/-!
# Integral tame reduction families

Source: Bhatt--Scholze, Lemmas 4.2.12, 6.8.2 and 7.4.10, Proposition 6.8.4(1),(6),
assembled in the tame-boundary expansion of blueprint direct-images paragraph (3).
(blueprint: lem-sfb-tame-integral-reduction-family).

The auxiliary constructions only specify the coefficient transports, scalar quotients,
and embedded-image normalization appearing in this assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.TameIntegralReduction

/-- The canonical continuous-function encoding, in the common scheme universe.
Source: Bhatt--Scholze 6.8.1; the existing internal/sectionwise equivalence and canonical
coefficient realization (blueprint: lem-sfb-tame-integral-reduction-family). -/
@[irreducible] def encoding (X : Scheme.{u}) (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj T) X) ≌
      SheafOfModules.{u + 1} (latticeModuleRing X T) := by
  let J := Scheme.ProEt.topology X
  let R := latticeModuleRing X T
  let B := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  letI : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj J R
    (fun V a b ↦ @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  let φ : condensedRingObj (Profinite.continuousCoefficientRingObj T) X ⟶ B :=
    ContinuousRingUniverse.comparison X T
  letI : IsIso φ := ContinuousRingUniverse.comparison_isIso X T
  exact (Mod.comapEquivalenceOfIsIso (inv φ)).trans
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J B).trans
      (CondensedRing.ringModuleEquivalenceOfIso X
        (CondensedRing.reconstructedRingIso X R).symm))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Internal integral coefficients with the induced norm topology.
Source: Bhatt--Scholze 6.8.1 (blueprint: lem-sfb-tame-integral-reduction-family). -/
abbrev integralRing :=
  Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)

/-- Internal rational coefficients with the specified extending norm.
Source: Bhatt--Scholze 6.8.1 (blueprint: lem-sfb-tame-integral-reduction-family). -/
abbrev rationalRing := Profinite.continuousCoefficientRingObj E

/-- The canonical integral module encoding; ultrametricity supplies total disconnectedness.
Source: Bhatt--Scholze 6.8.1 (blueprint: lem-sfb-tame-integral-reduction-family). -/
@[irreducible] def integralEncoding (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralRing l E) X) ≌
      SheafOfModules.{u + 1} (latticeModuleRing X (Padic.coefficientExtensionIntegers l E)) := by
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  exact encoding X (Padic.coefficientExtensionIntegers l E)

/-- The actual finite coefficient sheaf, initially with its quotient topology.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: lem-sfb-tame-integral-reduction-family). -/
abbrev finiteRing (X : Scheme.{u}) (n : ℕ) :=
  latticeCoefficientSheaf X (Padic.coefficientExtensionRing l E (n + 1))

/-- The actual quotient homomorphism, postcomposed with continuous coefficient functions.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: lem-sfb-tame-integral-reduction-family). -/
def finiteReduction (X : Scheme.{u}) (n : ℕ) :
    latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E) ⟶ finiteRing l E X n :=
  latticeCoefficientSheafMap X (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
    continuous_quot_mk

/-- Finite coefficients regarded as integral modules using the actual quotient map.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: lem-sfb-tame-integral-reduction-family). -/
def finiteRestriction (X : Scheme.{u}) (n : ℕ) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (finiteReduction l E X n))

/-- Multiplication by an integral constant on the sectionwise encoding.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-sfb-tame-integral-reduction-family). -/
@[irreducible] def sectionScalar (X : Scheme.{u})
    (M : SheafOfModules.{u + 1}
      (latticeModuleRing X (Padic.coefficientExtensionIntegers l E)))
    (a : Padic.coefficientExtensionIntegers l E) : M ⟶ M :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
       { toFun := fun x ↦ ULift.up (ContinuousMap.const U.unop.left a) • x
         map_add' := smul_add _
         map_smul' := fun r x ↦ by
           change _ • (r • x) = r • (_ • x)
           rw [smul_smul, smul_smul]
           exact congrArg (fun c : (latticeModuleRing X
             (Padic.coefficientExtensionIntegers l E)).obj.obj U ↦ c • x) (@mul_comm
               (ULift.{u + 1} C(U.unop.left, Padic.coefficientExtensionIntegers l E))
               inferInstance (ULift.up (ContinuousMap.const U.unop.left a)) r) }
     naturality := fun {U V} f ↦ by
       ext x
       exact (M.val.map_smul f (ULift.up (ContinuousMap.const U.unop.left a)) x).symm }⟩

/-- Multiplication by a constant in the internal integral category, transported canonically.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-sfb-tame-integral-reduction-family). -/
@[irreducible] def scalar (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralRing l E) X))
    (a : Padic.coefficientExtensionIntegers l E) : M ⟶ M :=
  (integralEncoding l E X).unitIso.hom.app M ≫
    (integralEncoding l E X).inverse.map
      (sectionScalar l E X ((integralEncoding l E X).functor.obj M) a) ≫
    (integralEncoding l E X).unitIso.inv.app M

/-- The quotient universal property pins down the actual scalar quotient and its map.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-sfb-tame-integral-reduction-family). -/
def IsQuotient {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralRing l E) X)}
    (a : Padic.coefficientExtensionIntegers l E) (q : M ⟶ N) : Prop :=
  ∃ h : scalar l E X M a ≫ q = 0,
    Nonempty (IsColimit (CokernelCofork.ofπ q h))


/-- The actual integral-to-rational condensed ring homomorphism.
Source: Bhatt--Scholze 6.8.1 (blueprint: lem-sfb-tame-integral-reduction-family). -/
def ringInclusion :
    Profinite.continuousCoefficientRingSheaf (Padic.coefficientExtensionIntegers l E) ⟶
      Profinite.continuousCoefficientRingSheaf E :=
  ⟨{ app := fun S ↦ RingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         (((Padic.coefficientExtensionIntegers l E).subtype.compLeftContinuous S.unop
           continuous_subtype_val).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The same coefficient inclusion as a map of internal ring objects.
Source: Bhatt--Scholze 6.8.1 (blueprint: lem-sfb-tame-integral-reduction-family). -/
def inclusion : Mon.mk (integralRing l E) ⟶ Mon.mk (rationalRing E) :=
  Mon.ofHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (ringInclusion l E))


/-- The actual rationalization embedding, as a morphism of underlying abelian sheaves.
Source: Bhatt--Scholze 6.8.4(6) (blueprint: lem-sfb-tame-integral-reduction-family). -/
@[irreducible] def embedding {W : Scheme.{u}}
    (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (integralRing l E) W))
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (rationalRing E) W))
    (e : (Mod.extendScalars (coefficientMap (inclusion l E).hom W)).obj N ≅ L) :
    N.X ⟶ L.X :=
  (Mod.extendUnit (coefficientMap (inclusion l E).hom W) N).hom ≫ e.hom.hom

/-- Pullback of an abelian-sheaf arrow using the canonical Cartesian identifications.
Source: Bhatt--Scholze 6.8.4(6), Cartesian coefficients
(blueprint: lem-sfb-tame-integral-reduction-family). -/
@[irreducible] def pullEmbedding
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    {W Z : Scheme.{u}} (q : Z ⟶ W)
    (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ' W))
    (j : N.X ⟶ L.X) :
    ((CondensedRing.upperStar Λ q).obj N).X ⟶
      ((CondensedRing.upperStar Λ' q).obj L).X :=
  ((Functor.isoWhiskerLeft
      ((upperStar Ab.{u + 1} q).mapMod (condensedRingObj Λ W))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ q))).app N).hom.hom ≫
    (upperStar Ab.{u + 1} q).map j ≫
      ((Functor.isoWhiskerLeft
        ((upperStar Ab.{u + 1} q).mapMod (condensedRingObj Λ' W))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ' q))).app L).inv.hom

/-- The matrix of an integral-to-rational map between based free modules. Its entries
are the images of integral basis vectors in the chosen rational basis; the canonical
continuous coefficient realizations evaluate them as continuous functions on Z.
Source: Bhatt--Scholze 6.8.4(6) (blueprint: lem-sfb-tame-integral-reduction-family). -/
@[irreducible] def embeddingMatrix {Z : Scheme.{u}} (d : ℕ)
    {N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralRing l E) Z)}
    {L : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (rationalRing E) Z)}
    (j : N.X ⟶ L.X)
    (b : N ≅ Mod.finiteFree (condensedRingObj (integralRing l E) Z) d)
    (t : L ≅ Mod.finiteFree (condensedRingObj (rationalRing E) Z) d) :
    Matrix (Fin d) (Fin d) C(Z, E) := by
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let a := ContinuousRingUniverse.comparison Z (Padic.coefficientExtensionIntegers l E)
  let c := ContinuousRingUniverse.comparison Z E
  letI : IsIso a := ContinuousRingUniverse.comparison_isIso Z _
  exact fun i k ↦
    ((inv a ≫
      (biproduct.ι (fun _ : Fin d ↦ Mod.regular
        (condensedRingObj (integralRing l E) Z)) k).hom ≫
      b.inv.hom ≫ j ≫ t.hom.hom ≫
      (biproduct.π (fun _ : Fin d ↦ Mod.regular
        (condensedRingObj (rationalRing E) Z)) i).hom ≫ c).hom.app
          (op (Scheme.ProEt.mk (𝟙 Z))) (ULift.up 1)).down

/-- The actual normalized reduction cone, including local finite freeness and completeness.
The exponent at index n is n+1. Each arrow out of N and each adjacent transition is
specified as the scalar cokernel, so its induced quotient comparison is invertible.
Source: Bhatt--Scholze 6.8.2 and 6.8.4(1)
(blueprint: lem-sfb-tame-integral-reduction-family). -/
structure ReductionFamily (W : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (integralRing l E) W)) where
  tower : ℕᵒᵖ ⥤ Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
    (condensedRingObj (integralRing l E) W)
  projection : (Functor.const ℕᵒᵖ).obj N ⟶ tower
  quotient : ∀ n : ℕ, IsQuotient l E
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) (projection.app (op n))
  transition : ∀ n : ℕ, IsQuotient l E
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
    (tower.map (homOfLE (Nat.le_succ n)).op)
  complete : IsLimit (Cone.mk N projection)
  finiteModule : ∀ n : ℕ, SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteRing l E W n))
  finiteFree : ∀ n : ℕ, (finiteModule n).IsFiniteLocallyFree
  finiteIdentification : ∀ n : ℕ,
    (finiteRestriction l E W n).obj (finiteModule n) ≅
      (integralEncoding l E W).functor.obj (tower.obj (op n))
  constantCoefficients : ∀ n : ℕ,
    Nonempty (finiteRing l E W n ≅
      (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))


/-- The source of the recorded strict-local root projection, with its existing scheme structure.
Source: tame-boundary expansion (blueprint: lem-sfb-tame-integral-reduction-family). -/
abbrev puncturedTower (p : ℕ) {Y W : Scheme.{u}} (w : W ⟶ Y)
    {κ : Type u} [Field κ] [IsAlgClosed κ] (s : Spec (.of κ) ⟶ Y)
    {r : ℕ} (t : Fin r → Scheme.strictHenselizationRing s) : Scheme.{u} :=
  (Over.mk (strictLocalTameRootProjection p w s t)).left


/-- The embedded pair and finite reductions on a fixed tower, in every rational basis.
The matrix records the actual rationalization unit, not merely an abstract integral module.
Source: Bhatt--Scholze 6.8.4(6) (blueprint: lem-sfb-tame-integral-reduction-family). -/
@[irreducible] def HasConstantModel {Z : Scheme.{u}}
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralRing l E) Z))
    (L : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (rationalRing E) Z))
    (j : N.X ⟶ L.X)
    (F : ℕ → Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralRing l E) Z)) : Prop :=
  ∀ (d : ℕ) (τ : L ≅ Mod.finiteFree (condensedRingObj (rationalRing E) Z) d),
    ∃ b : N ≅ Mod.finiteFree (condensedRingObj (integralRing l E) Z) d,
    (∃ h : Matrix.GeneralLinearGroup (Fin d) E, ∀ (i k : Fin d) (z : Z),
      embeddingMatrix l E d j b τ i k z = h.val i k) ∧
    ∀ n : ℕ, Nonempty
      ((integralEncoding l E Z).functor.obj (F n) ≅
        (finiteRestriction l E Z n).obj
          (SheafOfModules.free (R := (sheafCompose _
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteRing l E Z n))
              (ULift.{u + 1} (Fin d))))

/-- The same embedded-pair normalization on every recorded boundary parameter tower.
Source: tame-boundary expansion (blueprint: lem-sfb-tame-integral-reduction-family). -/
@[irreducible] def HasConstantKummerModels (p : ℕ) {Y W : Scheme.{u}}
    (D : Y.IdealSheafData) (w : W ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (integralRing l E) W))
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (rationalRing E) W))
    (j : N.X ⟶ L.X)
    (F : ReductionFamily l E W N) : Prop :=
  ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (s : Spec (.of κ) ⟶ Y)
    (r : ℕ) (t : Fin r → Scheme.strictHenselizationRing s),
    IsStrictLocalBoundaryParameters D s t →
      HasConstantModel l E
        ((CondensedRing.upperStar (integralRing l E)
          (strictLocalTameRootProjection p w s t)).obj N)
        ((CondensedRing.upperStar (rationalRing E)
          (strictLocalTameRootProjection p w s t)).obj L)
        (pullEmbedding (strictLocalTameRootProjection p w s t) N L j)
        (fun n ↦ (CondensedRing.upperStar (integralRing l E)
          (strictLocalTameRootProjection p w s t)).obj (F.tower.obj (op n)))

/-- A finite-rank lisse rational module tame on the stipulated nonempty connected qcqs
strict-local root towers has a lisse integral model with its actual complete reduction
family. In every rational tower basis the embedding has one constant invertible matrix
in a suitable integral basis, and the reductions have that same rank.

Source: Bhatt--Scholze, Lemmas 4.2.12, 6.8.2, 7.4.7, 7.4.10 and Proposition 6.8.4(1),(6);
Stanford Weil II L19, Proposition 1.1.9
(blueprint: lem-sfb-tame-integral-reduction-family).

Proof plan:
1. Finite type over a field makes Y Noetherian; its open W is Noetherian. Regularity
makes the stalks normal domains, and separation restricts to W. Decompose W into its
finitely many open-and-closed connected components, using
lem-weil-pbc-finite-type-over-noetherian,
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal,
lem-weil-pbc-regular-ring-normal and lem-sfb-noetherian-connected-components-open.
2. On each nonempty component, lem-sfb-embedded-lattice-coefficient-comparison and
lem-sfb-integral-lisse-reduction-equivalence identify the continuous coefficients.
Since l is a unit times a positive power of the uniformizer, either localization is
rationalization. Apply lem-a1-normal-proetale-monodromy to obtain continuous profinite
monodromy; the distinct-characteristic hypothesis makes l invertible.
3. Apply lem-pod-profinite-stable-lattice. The integral normalization of monodromy
constructs N from the actual finite quotients of the stable lattice. Coordinatewise
injection of continuous integral functions makes its rationalization unit injective.
Transport using lem-sfb-embedded-lattice-coefficient-comparison and glue over the
finite disjoint component cover, taking products of sections on each site object.
4. Apply lem-sfb-integral-lisse-reduction-equivalence. Its canonical scalar cokernels
and transition maps give the reduction cone and its limit universal property. The
coefficient equivalence preserves these universal properties, so the quotients and
completion map here are the actual ones.
5. Pullback preserves lisseness by lem-weil-pbc-continuous-locally-free-pullback and is
exact by sk-prop-sfb-cartesian-coefficients. On a qcqs tower and in a rational basis,
det-lem-stratified-lattice-scheme(1) classifies the embedded lattice by a section of
the constant discrete lattice-coset sheaf. By lem-sfb-continuous-set-descent-components
and connectedness this section is one coset. Choose its representative h; the
intertwining integral basis gives exactly the displayed constant embedding matrix.
6. Exact pullback identifies reductions with those of that integral basis. The
coefficient quotient calculation gives the constant rank-d quotient modules. All
steps allow rank zero and different ranks on different components. Empty W uses the
zero model and has no nonempty tower. Only the parameters vanishing at the chosen
point enter the boundary tuple, so fewer boundary components cause no extra factor. -/
theorem tame_integral_reduction_family
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hY : IsRegularScheme Y)
    (D : Y.IdealSheafData) (hD : IsStrictNormalCrossingsBoundary D)
    (L : Mod (Sheaf (Scheme.ProEt.topology (Scheme.Opens.toScheme D.support.compl)) Ab.{u + 1})
      (condensedRingObj (rationalRing E) (Scheme.Opens.toScheme D.support.compl)))
    (hL : IsLisseCoefficientModule (rationalRing E) L)
    (htame : IsStrictLocalKummerTameModule p (rationalRing E) D (Scheme.Opens.ι D.support.compl) L)
    (htowers : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (s : Spec (.of κ) ⟶ Y)
      (r : ℕ) (t : Fin r → Scheme.strictHenselizationRing s),
      IsStrictLocalBoundaryParameters D s t →
        ConnectedSpace (puncturedTower p (Scheme.Opens.ι D.support.compl) s t) ∧
        CompactSpace (puncturedTower p (Scheme.Opens.ι D.support.compl) s t) ∧
        QuasiSeparatedSpace (puncturedTower p (Scheme.Opens.ι D.support.compl) s t)) :
    ∃ (N : Mod (Sheaf (Scheme.ProEt.topology (Scheme.Opens.toScheme D.support.compl)) Ab.{u + 1})
        (condensedRingObj (integralRing l E) (Scheme.Opens.toScheme D.support.compl)))
      (e : (Mod.extendScalars (coefficientMap (inclusion l E).hom
        (Scheme.Opens.toScheme D.support.compl))).obj N ≅ L),
      IsLisseCoefficientModule (integralRing l E) N ∧
      ∃ F : ReductionFamily l E (Scheme.Opens.toScheme D.support.compl) N,
        HasConstantKummerModels l E p D (Scheme.Opens.ι D.support.compl)
          N L (embedding l E N L e) F := by
  sorry

end AlgebraicGeometry.ProEtale.TameIntegralReduction
