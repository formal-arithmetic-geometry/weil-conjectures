/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.KoszulReconstruction
public import Sheaf.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Endomorphism
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Mathlib.Data.List.TFAE

/-! # Roos and intrinsic completeness for completed local-field coefficients

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul,
and Tag 099B, lemma-derived-completion
(blueprint: lem-pur-roos-intrinsic-completeness-equivalence).

All five conditions concern the completed integral ring on the actual small pro-etale
site. A section on U is equivalently a global section on the slice over U. Membership
in the ideal sheaf tR is expressed by local divisibility on a covering sieve; thus the
second condition tests every section of the sheaf ideal, not only the constant t.
The representative is K-flat with flat terms. The three displayed units retain their
specified quotient, degree-zero Koszul, and explicit (u,0) normalizations.
The integral one-generator chain models and their normalized units are defined here;
the general intrinsic-completion and reconstruction interfaces remain imported intact.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

section IntegralKoszulModels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})

/-- The uniformizer section, through the actual constant-to-limit map.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralCompletionScalarValue (U : T.ProEtᵒᵖ) :
    (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U :=
  (integralConstantToCompletionOfUniverses l E T).hom.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
          (ULift.up (Padic.coefficientExtensionUniformizer l E)))

/-- Multiplication by the actual uniformizer determines a unique chain endomorphism.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence).
Proof: the constant-to-limit map is natural, so its uniformizer sections restrict
compatibly. Scalar multiplication is linear over the commutative coefficient ring,
commutes with restrictions, and commutes with the linear differential. These formulas
define a chain map; equality on every section in every degree proves uniqueness. -/
theorem integralKoszulScalar_existsUnique (P : IntegralOnSlice.Cx l E T none) :
    ∃! f : P ⟶ P, ∀ (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U),
      (f.f q).val.app U x = integralCompletionScalarValue l E T U • x := by
  have hs {U V : T.ProEtᵒᵖ} (g : U ⟶ V) :
      (completedIntegralCoefficientSheafUnrestricted l E T).obj.map g
          (integralCompletionScalarValue l E T U) =
        integralCompletionScalarValue l E T V := by
    let α := Functor.whiskerRight
      (toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))))
      (forget₂ CommRingCat RingCat) ≫
      (integralConstantToCompletionOfUniverses l E T).hom
    exact (CategoryTheory.congr_fun (α.naturality g)
      (ULift.up (Padic.coefficientExtensionUniformizer l E))).symm
  let f : P ⟶ P :=
    { f := fun q ↦
        { val :=
            { app := fun U ↦ ModuleCat.ofHom
                { toFun := fun x ↦ integralCompletionScalarValue l E T U • x
                  map_add' := fun x y ↦ smul_add _ x y
                  map_smul' := fun a x ↦ by
                    let : CommRing ((IntegralOnSlice.rings l E T none).obj.obj U) :=
                      inferInstanceAs (CommRing ((IntegralOnSlice.ring l E T none).obj.obj U))
                    change (integralCompletionScalarValue l E T U :
                      (IntegralOnSlice.rings l E T none).obj.obj U) • (a • x) =
                        a • ((integralCompletionScalarValue l E T U :
                          (IntegralOnSlice.rings l E T none).obj.obj U) • x)
                    let z : (IntegralOnSlice.rings l E T none).obj.obj U :=
                      integralCompletionScalarValue l E T U
                    change z • (a • x) = a • (z • x)
                    rw [← mul_smul, ← mul_smul, mul_comm z a] }
              naturality := by
                intro U V g
                ext x
                change integralCompletionScalarValue l E T V • (P.X q).val.map g x =
                  (P.X q).val.map g (integralCompletionScalarValue l E T U • x)
                rw [PresheafOfModules.map_smul]
                rw [show (IntegralOnSlice.rings l E T none).obj.map g
                    (integralCompletionScalarValue l E T U) =
                    integralCompletionScalarValue l E T V from hs g] } }
      comm' := by
        intro i j _hij
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        ext x
        exact ((P.d i j).val.app U).hom.map_smul
          (integralCompletionScalarValue l E T U) x }
  refine ⟨f, ?_, ?_⟩
  · intro q U x
    rfl
  · intro g hg
    apply HomologicalComplex.hom_ext
    intro q
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact hg q U x

/-- The uniquely section-normalized scalar chain map.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulScalar (P : IntegralOnSlice.Cx l E T none) : End P :=
  (integralKoszulScalar_existsUnique l E T P).exists.choose

/-- P tensor [R --t^(n+1)--> R], in the standard total-cone coordinates.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulLevel (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :=
  CochainComplex.mappingCone (integralKoszulScalar l E T P ^ (n + 1))

/-- The square defining the (t,1) transition commutes.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence).
Proof: compose the indicated powers of the same endomorphism. Both sides are its
(n+2)-nd power, by the power recursion and the identity composition law. -/
theorem integralKoszulStep_square (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :
    (integralKoszulScalar l E T P ^ (n + 1 + 1)) ≫ 𝟙 P =
      integralKoszulScalar l E T P ≫ (integralKoszulScalar l E T P ^ (n + 1)) := by
  simpa only [Category.comp_id, End.mul_def] using
    (pow_succ (integralKoszulScalar l E T P) (n + 1))

/-- The specified transition, multiplication by t in degree -1 and identity in degree 0.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulStep (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :
    integralKoszulLevel l E T P (n + 1) ⟶ integralKoszulLevel l E T P n :=
  CochainComplex.mappingCone.map _ _ (integralKoszulScalar l E T P) (𝟙 P)
    (integralKoszulStep_square l E T P n)

/-- The strict positive-power Koszul tensor tower on this single representative.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulTower (P : IntegralOnSlice.Cx l E T none) :
    ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E T none :=
  Functor.ofOpSequence (integralKoszulStep l E T P)

/-- Degree-zero inclusions give the compatible Koszul augmentation.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence).
Proof: the transition has identity on the target copy of P in its mapping cone.
Composing the cone inclusion with the transition is therefore the next inclusion. -/
theorem integralKoszulUnit_compatible (P : IntegralOnSlice.Cx l E T none) (n : ℕ) :
    CochainComplex.mappingCone.inr (integralKoszulScalar l E T P ^ (n + 1 + 1)) ≫
        integralKoszulStep l E T P n =
      CochainComplex.mappingCone.inr (integralKoszulScalar l E T P ^ (n + 1)) := by
  simp [integralKoszulStep, CochainComplex.mappingCone.map]

/-- The product of the degree-zero inclusions.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulProductUnit (P : IntegralOnSlice.Cx l E T none) :
    P ⟶ ∏ᶜ (fun n : ℕ ↦ (integralKoszulTower l E T P).obj (op n)) :=
  Pi.lift (fun n ↦ CochainComplex.mappingCone.inr
    (integralKoszulScalar l E T P ^ (n + 1)))

/-- The specified one-minus-transition map on the termwise product.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulOneSubShift (P : IntegralOnSlice.Cx l E T none) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ (integralKoszulTower l E T P).obj (op n))
    (integralKoszulStep l E T P)

private theorem integralKoszulProductUnit_comp (P : IntegralOnSlice.Cx l E T none) :
    integralKoszulProductUnit l E T P ≫ integralKoszulOneSubShift l E T P = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [integralKoszulOneSubShift, towerTransitionEndomorphism,
    Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
    towerProductShift, Category.assoc, Pi.lift_π, integralKoszulProductUnit,
    Pi.lift_π_assoc, integralKoszulUnit_compatible, sub_self, zero_comp]

/-- The explicit fiber has differential (dx,(1-s)x-dy), as in the owning node.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulIntrinsicFiber (P : IntegralOnSlice.Cx l E T none) :=
  CochainComplex.mappingCocone (-integralKoszulOneSubShift l E T P)

/-- Zero is the specified second cochain in the intrinsic augmentation.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence).
Proof: each component of u(1-s) is the difference of consecutive compatible cone
inclusions, so is zero. The differential of the zero cochain is zero. -/
theorem integralKoszulIntrinsicUnit_condition (P : IntegralOnSlice.Cx l E T none) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P
          (∏ᶜ fun n : ℕ ↦ (integralKoszulTower l E T P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (integralKoszulProductUnit l E T P ≫ (-integralKoszulOneSubShift l E T P)) = 0 := by
  simp [Preadditive.comp_neg, integralKoszulProductUnit_comp]

/-- The actual (u,0) chain map into the signed intrinsic fiber.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulIntrinsicUnitComplex (P : IntegralOnSlice.Cx l E T none) :
    P ⟶ integralKoszulIntrinsicFiber l E T P :=
  CochainComplex.mappingCocone.lift _ (integralKoszulProductUnit l E T P) 0
    (integralKoszulIntrinsicUnit_condition l E T P)

/-- The intrinsic unit on K, realized using the specified representative isomorphism.
Source: Stacks 0A0E (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulIntrinsicUnit (K : IntegralOnSlice.D l E T none)
    (P : IntegralOnSlice.Cx l E T none) (e : DerivedCategory.Q.obj P ≅ K) :
    K ⟶ DerivedCategory.Q.obj (integralKoszulIntrinsicFiber l E T P) :=
  e.inv ≫ DerivedCategory.Q.map (integralKoszulIntrinsicUnitComplex l E T P)

/-- The total derived inverse limit of the Koszul tensor tower, in the exact-products model.
Source: Stacks 0A0E and 0941 (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulLimit (P : IntegralOnSlice.Cx l E T none) :=
  CochainComplex.mappingCocone (integralKoszulOneSubShift l E T P)

/-- The zero cochain gives the strict Koszul augmentation into the Roos fiber.
Source: Stacks 0A0E and 0941 (blueprint: lem-pur-roos-intrinsic-completeness-equivalence).
Proof: evaluate u(1-s) at every product projection. It is the difference of the
two cone inclusions identified by integralKoszulUnit_compatible. Thus it vanishes;
the differential of the zero cochain also vanishes. -/
theorem integralKoszulLimitUnit_condition (P : IntegralOnSlice.Cx l E T none) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P
          (∏ᶜ fun n : ℕ ↦ (integralKoszulTower l E T P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (integralKoszulProductUnit l E T P ≫ integralKoszulOneSubShift l E T P) = 0 := by
  simp [integralKoszulProductUnit_comp]

/-- The degree-zero Koszul unit into its total strict derived inverse limit.
Source: Stacks 0A0E and 0941 (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulLimitUnitComplex (P : IntegralOnSlice.Cx l E T none) :
    P ⟶ integralKoszulLimit l E T P :=
  CochainComplex.mappingCocone.lift _ (integralKoszulProductUnit l E T P) 0
    (integralKoszulLimitUnit_condition l E T P)

/-- The specified Koszul unit on the object represented by P.
Source: Stacks 0A0E and 0941 (blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
def integralKoszulLimitUnit (K : IntegralOnSlice.D l E T none)
    (P : IntegralOnSlice.Cx l E T none) (e : DerivedCategory.Q.obj P ≅ K) :
    K ⟶ DerivedCategory.Q.obj (integralKoszulLimit l E T P) :=
  e.inv ≫ DerivedCategory.Q.map (integralKoszulLimitUnitComplex l E T P)

end IntegralKoszulModels

/-- The local test object is exactly RHom(R_U[1/s], K restricted to U).
The slice sheafification and standard localization are the existing canonical ones;
they impose no equality between the site object, morphism and coefficient universes.
Source: Stacks 0999 and 0A0E
(blueprint: lem-pur-roos-intrinsic-completeness-equivalence). -/
noncomputable def integralCompletionLocalTest
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : AlgebraicGeometry.Scheme.{t}) (K : IntegralOnSlice.D l E T none)
    (U : T.ProEt)
    (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections) :
    IntegralOnSlice.D l E T (some U) :=
  letI : HasSheafify (IntegralOnSlice.topology T (some U))
      CommRingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  letI := HasDerivedCategory.standard
    (SheafOfModules.{max u (t + 1)} ((IntegralOnSlice.rings l E T none).over U))
  (IntegralOnSlice.hom l E T (some U)).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalizationOfUniverses (IntegralOnSlice.ring l E T (some U)) s)),
      ringedSiteDerivedRestrictionOfUniverses (IntegralOnSlice.rings l E T none) U K)

/-- The five completeness conditions for the specified canonical units are equivalent.
There is no geometric finiteness or cohomological boundedness assumption.

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul,
and Tag 099B, lemma-derived-completion
(blueprint: lem-pur-roos-intrinsic-completeness-equivalence).

Proof:
1. Apply lem-weil-pbc-ringed-koszul-completion-reflector to the completed ring and t.
   Its ideal is tR, so its local vanishing condition, on every slice and every local
   section, is exactly the second condition. It identifies that condition with the
   invertibility of the specified Koszul unit, and makes its completion locally complete.
2. Use def-pur-completed-coefficient-presentation-transport: the projection-normalized
   coefficient isomorphism identifies the continuous-function and constant-quotient
   completed rings. Exact restriction along its inverse preserves t, tensor, strict
   quotient towers, products and their total derived limits. Transport
   prop-weil-pbc-koszul-reconstruction. The cone model here is the negative one-generator
   Koszul tensor model. Its unit-preserving comparison identifies (iii) with (v), and
   shows that the quotient completion is locally complete.
3. Apply lem-weil-pbc-completed-koszul-quotient-comparison to the single generator t.
   It identifies the explicit signed product fiber with the strict quotient completion,
   preserving its (u,0) unit. Relabel positive exponents by n+1 and use the unique
   unit-compatible comparison between total right derived limits. Thus (iv) and (v)
   are equivalent. The independent-universe integral interfaces retain these formulas.
4. The single representative gives a strict quotient augmentation. By
   def-weil-strict-roos-model and lem-weil-strict-roos-derivation its zero-homotopy
   lift is the derived-limit unit. The exact products of
   lem-weil-proetale-countable-products-exact and the triangle from
   lem-weil-pbc-ringed-strict-tower-homotopy-limit give L -> B -> B -> L[1], whose
   first map composed with comp_K has exactly the quotient components c_n.
5. If (v) holds, transport this distinguished triangle along comp_K. Its first map
   becomes c, giving the Roos convention (i) by def-weil-derived-complete.
6. Conversely rotate the triangle in (i) and that for L. Both begin with the same
   arrow 1-s. TR3 extends the two identity maps of B to a triangle morphism;
   lem-sf-triangle-morphism-iso makes its last component an isomorphism. Shift back
   to identify K with L. Local vanishing is invariant under isomorphism, so K
   satisfies (ii). Steps 1--3 conclude all five equivalences. This use of TR3 does
   not identify its arbitrary lift with the prescribed completion unit. -/
theorem roosIntrinsicCompletenessEquivalence
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (_hpl : p ≠ l)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : AlgebraicGeometry.Scheme.{t})
    (d : AlgebraicGeometry.Scheme.AdicCoefficientDatum
      (Padic.coefficientExtensionIntegers l E))
    (_hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (K : IntegralOnSlice.D l E T none)
    (P : (IntegralOnSlice.Good l E T none).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) :
    List.TFAE [
      IntegralOnSlice.IsComplete l E T none K,
      (∀ (U : T.ProEt)
        (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections),
        (∃ S : Sieve U, S ∈ AlgebraicGeometry.Scheme.ProEt.topology T U ∧
          ∀ (V : T.ProEt) (f : V ⟶ U), S f →
            ∃ c : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj (op V),
              s.val (op (Over.mk f)) = integralCompletionScalarValue l E T (op V) * c) →
        IsZero (integralCompletionLocalTest l E T K U s)),
      IsIso (integralKoszulLimitUnit l E T K P.obj e),
      IsIso (integralKoszulIntrinsicUnit l E T K P.obj e),
      IsIso ((IntegralOnSlice.completionUnit l E T none).app K)] := by
  sorry

end WeilConjectures
