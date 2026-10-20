/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Compactification.NagataCompactification
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.DualityPairingHelpers
import WeilConjectures.Algebra.Homology.RhomGlobalSections
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory

import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopy
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.SignedDoubleHomCone
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Compactification.Defs
import WeilConjectures.Compactification.Noetherian
import Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses

/-! # Evaluation and the ambient double-dual morphism

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2122; Stacks Project, Tags 08J9, 08JA and 08JC
(blueprint: lem-weil-duality-pairing).

## Main definitions and statement

* `CategoryTheory.dualityDoubleFunctor`: the covariant double internal Hom.
* `CategoryTheory.DualityPairingCompatibility`: the naturality, shift and triangle clauses.
* `AlgebraicGeometry.Etale.AmbientDualityPairing` and
  `AlgebraicGeometry.ProEtale.AmbientDualityPairing`: the canonical evaluation and transpose,
  specified by the existing adjunction and the descended Koszul symmetry.
* `AlgebraicGeometry.Etale.ambient_duality_pairing`: the two site assertions of the node.

The tensor-Hom adjunction has left tensor as its left adjoint. Evaluation in the order
DK tensor K therefore includes the Koszul symmetry. Its adjunct, with left tensor DK,
is the double-dual morphism. All derived categories here are unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe v u a c d w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- Double application of the contravariant internal Hom into W.
Source: Stacks Project, Tag 08J9 (blueprint: lem-weil-duality-pairing). -/
def dualityDoubleFunctor {C : Type u} [Category.{v} C]
    (H : Cᵒᵖ ⥤ C ⥤ C) (W : C) : C ⥤ C :=
  (H.flip.obj W).rightOp ⋙ H.flip.obj W

/-- The compatibility assertions for the specified evaluation and its specified transpose.
This packages the conclusion, including the connecting square of triangles. The shift
isomorphisms include coherence for zero and addition, through Functor.CommShift.
Source: Stacks Project, Tags 08J9 and 08JC (blueprint: lem-weil-duality-pairing). -/
def DualityPairingCompatibility {C : Type u} [Category.{v} C]
    [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (W : C)
    (e : ∀ K : C, (T.obj ((H.obj (op K)).obj W)).obj K ⟶ W)
    (δ : ∀ K : C, K ⟶ (dualityDoubleFunctor H W).obj K) : Prop :=
  (∀ (K L : C) (f : K ⟶ L),
    ((T.map ((H.map f.op).app W)).app K) ≫ e K =
      (T.obj ((H.obj (op L)).obj W)).map f ≫ e L) ∧
  (∀ (K L : C) (f : K ⟶ L),
    f ≫ δ L = δ K ≫ (dualityDoubleFunctor H W).map f) ∧
  ∃ s : (dualityDoubleFunctor H W).CommShift ℤ,
    (∀ (n : ℤ) (K : C),
      δ ((shiftFunctor C n).obj K) ≫ (s.commShiftIso n).hom.app K =
        (shiftFunctor C n).map (δ K)) ∧
    ∀ (U : Triangle C), U ∈ distTriang C →
      Triangle.mk ((dualityDoubleFunctor H W).map U.mor₁)
        ((dualityDoubleFunctor H W).map U.mor₂)
        ((dualityDoubleFunctor H W).map U.mor₃ ≫
          (s.commShiftIso (1 : ℤ)).hom.app U.obj₁) ∈ distTriang C ∧
      ∃ t : U ⟶ Triangle.mk ((dualityDoubleFunctor H W).map U.mor₁)
          ((dualityDoubleFunctor H W).map U.mor₂)
          ((dualityDoubleFunctor H W).map U.mor₃ ≫
            (s.commShiftIso (1 : ℤ)).hom.app U.obj₁),
        t.hom₁ = δ U.obj₁ ∧ t.hom₂ = δ U.obj₂ ∧ t.hom₃ = δ U.obj₃

end CategoryTheory

namespace AlgebraicGeometry

variable (A : Type a) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (X : Scheme.{u})

namespace Etale

/-- Evaluation and its adjoint double-dual arrow with their canonical normalizations.
The tensor symmetry is the descended Koszul symmetry. After interchanging its factors,
evaluation corresponds to the identity under tensor-Hom adjunction. The arrow δ is its
transpose, rather than an arbitrary natural map with the same endpoints.
Source: Stacks Project, Tags 08J9, 08JA and 08JC
(blueprint: lem-weil-duality-pairing). -/
def AmbientDualityPairing
    (W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  ∃ b : derivedTensor A X ≅ (derivedTensor A X).flip,
    (∀ K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
      HEq ((b.hom.app K).app L)
        (DerivedMonoidal.braiding'
          (_root_.DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology A))
          (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)) K L).hom) ∧
    ∃ e : ∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
        ((derivedTensor A X).obj (((derivedHom A X).obj (op K)).obj W)).obj K ⟶ W,
      (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
        (derivedTensorHomAdjunction A K).homEquiv
          (((derivedHom A X).obj (op K)).obj W) W
          (((b.hom.app K).app (((derivedHom A X).obj (op K)).obj W)) ≫ e K) =
            𝟙 (((derivedHom A X).obj (op K)).obj W)) ∧
      ∃ δ : ∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
          K ⟶ (dualityDoubleFunctor (derivedHom A X) W).obj K,
        (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
          δ K = (derivedTensorHomAdjunction A
            (((derivedHom A X).obj (op K)).obj W)).homEquiv K W (e K)) ∧
        DualityPairingCompatibility (derivedTensor A X) (derivedHom A X) W e δ

end Etale

namespace ProEtale

/-- Evaluation and its adjoint double-dual arrow with their canonical normalizations.
The tensor symmetry is the descended Koszul symmetry. After interchanging its factors,
evaluation corresponds to the identity under tensor-Hom adjunction. The arrow δ is its
transpose, rather than an arbitrary natural map with the same endpoints.
Source: Stacks Project, Tags 08J9, 08JA and 08JC
(blueprint: lem-weil-duality-pairing). -/
def AmbientDualityPairing
    (W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) : Prop :=
  let T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) := curriedTensor _
  let H : (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))ᵒᵖ ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
    MonoidalClosed.internalHom
  ∃ b : T ≅ (T).flip,
    (∀ K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
      HEq ((b.hom.app K).app L)
        (DerivedMonoidal.braiding'
          (_root_.DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology X) A))
          (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A)
            (ComplexShape.up ℤ)) K L).hom) ∧
    ∃ e : ∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
        ((T).obj (((H).obj (op K)).obj W)).obj K ⟶ W,
      (∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
        (MonoidalClosed.internalHomAdjunction₂.adj K).homEquiv
          (((H).obj (op K)).obj W) W
          (((b.hom.app K).app (((H).obj (op K)).obj W)) ≫ e K) =
            𝟙 (((H).obj (op K)).obj W)) ∧
      ∃ δ : ∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
          K ⟶ (dualityDoubleFunctor H W).obj K,
        (∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
          δ K = (MonoidalClosed.internalHomAdjunction₂.adj
            (((H).obj (op K)).obj W)).homEquiv K W (e K)) ∧
        DualityPairingCompatibility (T) H W e δ

end ProEtale

namespace Etale

/-- Evaluation and its transpose are natural and compatible with shifts and distinguished
triangles, on the entire ambient derived category. The dualizing object is the ordinary
ambient exceptional inverse image of A, not a constructible exceptional functor.

Source: Weil conjectures blueprint, order 2122; Stacks Project, Tags 08J9, 08JA and 08JC
(blueprint: lem-weil-duality-pairing).

Proof:
1. On a small ringed site, use lem-weil-pbc-ringed-internal-hom-exact-restriction and
   lem-pur-rhom-global-sections for tensor-Hom adjunction. The tensor symmetry is
   x_p tensor y_q ↦ (-1)^(pq) y_q tensor x_p; its chain-map identity follows by
   expanding the two differentials of def-pc-tensor-complex-sheaves. Descend it by
   lem-weil-pbc-site-derived-tensor-descent.
2. Evaluation is the adjunct of the identity, in the order K tensor DK. Precompose
   with symmetry and transpose to define δ. Adjunction naturality gives the
   dinaturality equation for evaluation, and transposition gives naturality of δ.
3. Choose a K-injective representative I of W by prop-pur-kinjective-resolutions-exist.
   Put T(C) = Hom-complex(C,I). The chain map b_C(x)(f) = (-1)^(pq) f(x), for
   x in degree p and f in degree q, commutes with the Hom differential because the
   two d_I f(x) terms cancel. Choose K-flat representatives P of C and Q of T(P)
   by lem-pc-kflat-resolution. By lem-pur-hom-kflat-into-kinjective, T(P) and T(Q)
   are K-injective. Ordinary currying identifies the transpose of evaluation with
   T(Q → T(P)) composed with b_P. By lem-pur-rhom-well-defined the first map is a
   quasi-isomorphism; hence b_C localizes to the specified δ.
4. The chain shift comparison s_(C,m):T(C[m]) → T(C)[-m] multiplies a degree-q
   map by (-1)^(mq). On double Hom use χ_C = -s_(T(C),-1) composed with
   T(s_(C,1)) inverse. For u:A → B and E=Cone(u), write T²(E) as pairs (α,β).
   The map (α,β) ↦ (α,γ), γ(y)=(-1)^(p+r)β(y), identifies its differential with
   that of Cone(T²u). It preserves the inclusion and carries T²(-π), followed by
   χ, to the negative projection. Thus χ gives an exact shift comparison.
   Substituting b in χ gives χ_C b_(C[1])=b_C[1]. Iteration and inversion give
   the coherent comparisons and compatibility for every integer shift.
5. Apply lem-weil-pbc-commshift-nattrans-triangle-morphism to id, D² and δ.
   Naturality and the shift identity supply all three squares, including the
   connecting square; the cone calculation makes the image triangle distinguished.
6. Specialize to the etale site and its ordinary ambient dualizing object, and to
   the pro-etale site with the supplied W. Nothing restricts K or DK to a
   constructible subcategory, and no equivalence between the sites is used.
-/
theorem ambient_duality_pairing
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    AmbientDualityPairing (ModuleCat.{u + 1} Λ) Y
      (dualizingComplex (ModuleCat.{u + 1} Λ) aY) ∧
    ∀ W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)),
      ProEtale.AmbientDualityPairing (ModuleCat.{u + 1} Λ) Y W := by
  sorry

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (A : Type a) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (X : Scheme.{u})

/-- The double-dual morphism specified by the etale evaluation-pairing theorem.
Its value is uniquely determined: the symmetry is fixed to the descended Koszul
symmetry, evaluation is the adjunct of the identity, and this arrow is its transpose.
Thus this extracts determined data, rather than choosing an arbitrary pairing.
Source: Stacks Project, Tags 08J9 and 08JA (blueprint: lem-weil-duality-pairing). -/
noncomputable def Etale.AmbientDualityPairing.bidualityMap
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (h : Etale.AmbientDualityPairing A X W)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ (dualityDoubleFunctor (Etale.derivedHom A X) W).obj K :=
  h.choose_spec.2.choose_spec.2.choose K

/-- The double-dual morphism specified by the pro-etale evaluation-pairing theorem.
The normalization fixes its value uniquely, just as in the etale presentation.
Source: Stacks Project, Tags 08J9 and 08JA (blueprint: lem-weil-duality-pairing). -/
noncomputable def ProEtale.AmbientDualityPairing.bidualityMap
    {W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (h : ProEtale.AmbientDualityPairing A X W)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ⟶ (dualityDoubleFunctor MonoidalClosed.internalHom W).obj K :=
  h.choose_spec.2.choose_spec.2.choose K

end AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private theorem koszulComponents
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{w} D]
    [MonoidalCategory C] [BraidedCategory C]
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.ContainsIdentities] [L.HasDerivedMonoidalCategory W]
    (T : D ⥤ D ⥤ D)
    (h : T = @curriedTensor _ _ (DerivedMonoidal.instMonoidalCategory L W)) :
    ∃ b : ∀ M N : D, (T.obj M).obj N ≅ (T.obj N).obj M,
      ∀ M N, HEq (b M N).hom (DerivedMonoidal.braiding' L W M N).hom := by
  subst T
  let b : @curriedTensor _ _ (DerivedMonoidal.instMonoidalCategory L W) ≅
      (@curriedTensor _ _ (DerivedMonoidal.instMonoidalCategory L W)).flip :=
    NatIso.ofComponents (fun M ↦ NatIso.ofComponents
      (fun N ↦ DerivedMonoidal.braiding' L W M N)
      (fun f ↦ DerivedMonoidal.braiding_naturality_right L W M f))
      (fun f ↦ NatTrans.ext (funext (fun N ↦
        DerivedMonoidal.braiding_naturality_left L W f N)))
  refine ⟨fun M N ↦ (b.app M).app N, ?_⟩
  exact fun _ _ ↦ HEq.rfl

/-- A componentwise characterization of the actual descended Koszul symmetry.
Naming this predicate keeps the large derived-monoidal instance out of the implicit
predicate argument to Classical.choose; it imposes exactly the original HEq clause.
Source: ambient_duality_pairing proof step 1; Stacks 08J9 and 08JA
(blueprint: lem-weil-duality-pairing). -/
def IsEtaleKoszulSymmetry (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (b : ∀ M N : DerivedCategoryModule A X,
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj N ≅
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj N).obj M) : Prop :=
  ∀ M N : DerivedCategoryModule A X,
    HEq (b M N).hom
      (DerivedMonoidal.braiding'
        (_root_.DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
          (ComplexShape.up ℤ)) M N).hom

/-- The standalone symmetry component of the ambient duality pairing, with the
normalization already required in AmbientDualityPairing. Its components are fixed by
HEq to the descended Koszul braiding, so extracting this witness cannot choose an
arbitrary symmetry. This interface avoids expanding the large derived monoidal
instance when specializing a raw braiding to fixed-coefficient sheaves.
Source: Stacks 08J9 and 08JA; ambient_duality_pairing proof step 1
(blueprint: lem-weil-duality-pairing).

Proof: On cochain complexes use x_p tensor y_q to (-1)^(pq) y_q tensor x_p.
Expanding the tensor differential shows it is a chain map. It respects homotopies
and sends K-flat resolutions to the same derived tensor representatives. Descend
along the derived localization in both variables. The inverse is the same signed
interchange in the opposite order, since the two signs multiply to one. The
localization characterization gives precisely the displayed component normalization.
This is the symmetry constructed in step 1 of the recorded pairing proof; no
constructibility, geometric boundedness, or choice of a dualizing object is used. -/
theorem etaleKoszulSymmetry (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    ∃ b : ∀ M N : DerivedCategoryModule A X,
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj N ≅
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj N).obj M,
      IsEtaleKoszulSymmetry A X b := by
  unfold IsEtaleKoszulSymmetry
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let target ← Lean.Meta.whnf target
    let some tensor := target.find? (fun e => e.isAppOf ``derivedTensor) |
      throwError "tensor absent"
    let some raw := target.find? (fun e =>
      e.isAppOf ``DerivedMonoidal.braiding') | throwError "raw absent"
    let ts := tensor.getAppArgs
    let args := raw.getAppArgs
    let ls := raw.getAppFn.constLevels!
    let L := args[6]!
    let W := args[7]!
    let h ← Lean.Meta.mkAppM
      ``AlgebraicGeometry.Etale.etaleTensorRaw #[ts[0]!, ts[7]!]
    let proof := Lean.mkAppN
      (Lean.mkConst ``AlgebraicGeometry.Etale.koszulComponents
        [ls[2]!, ls[0]!, ls[1]!, ls[3]!])
      (args[:11].toArray ++ #[tensor, h])
    (← Lean.Elab.Tactic.getMainGoal).assign proof

end AlgebraicGeometry.Etale
