/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.LisseAdicAutomorphismPullback
public import Sheaf.Paper.LisseAdicFiberFunctors
public import Sheaf.RepresentationTheory.LAdic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
import Sheaf.Paper.GaloisLisseRepresentations

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.Paper.LisseTensorScalarExtension
/-!
# The Weil fundamental representation on actual etale adic fibres

Source: Weil II (1.1.1), (1.1.6), (1.1.10); blueprint main-20261015,
def-wf-fundamental-representation (blueprint: def-wf-fundamental-representation).

Finite-cover germs specify path transport. Inverse limits and the two coefficient
extensions then specify its adic extension. No pro-etale sheaf is substituted for an
etale adic sheaf. The general degree-datum construction also applies away from curves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y z : Spec (.of Ω) ⟶ Y}

/-- Finite-cover germs determine the finite-coefficient path uniquely, even when the
coefficient ring itself is infinite; the underlying stalks are required to be finite.
Source: Stacks 0BND(2), Weil II (1.1.6)
(blueprint: def-wf-fundamental-representation).
Proof: represent the underlying finite locally constant set sheaf by a finite etale
cover. Evaluate the given path on that cover. Naturality for addition and scalar
multiplication makes the resulting bijection linear. Every germ is represented on
such a cover, so the displayed germ rule determines it uniquely. The inverse path
supplies its inverse. This is the finite step of the node's stalk transport. -/
theorem etaleFinitePathIso_exists (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F)
    (hfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F))
    (τ : fiber y ≅ fiber z) :
    ∃! e : (pointSmallEtale y).ulift.{u + 1}.sheafFiber.obj F ≅
        (pointSmallEtale z).ulift.{u + 1}.sheafFiber.obj F,
      ∀ (P : Y.FiniteEtale) (a : (fiber y).obj P) (s : F.obj.obj (op P.obj)),
        e.hom ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber P.obj ⟨a⟩ F.obj s) =
          (pointSmallEtale z).ulift.{u + 1}.toPresheafFiber P.obj
            ⟨τ.hom.app P a⟩ F.obj s := by
  sorry

/-- The uniquely normalized finite path, not an arbitrary stalk isomorphism.
Source: Stacks 0BND(2) (blueprint: def-wf-fundamental-representation). -/
def etaleFinitePathIso (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F)
    (hfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F))
    (τ : fiber y ≅ fiber z) :
    (pointSmallEtale y).ulift.{u + 1}.sheafFiber.obj F ≅
      (pointSmallEtale z).ulift.{u + 1}.sheafFiber.obj F :=
  (etaleFinitePathIso_exists R F hF hfin τ).exists.choose

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]

/-- Adic levels have finite underlying stalks, not merely finitely generated modules.
Source: Weil II (1.1.1) b) (blueprint: def-wf-fundamental-representation).
Proof: the level-n stalk is finitely generated over O_E and annihilated by the
prescribed positive power of its uniformizer. It is therefore a quotient of a finite
power of O_E modulo that power. The residue field of the integers of the finite
extension E of Q_l is finite, so each such quotient ring, and then the stalk, is finite.
The lifted stalk has the same underlying module, hence the same finiteness. -/
theorem etaleIntegralLevel_finite (F : LisseIntegralSheaf l E Y) (n : ℕ)
    (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y) :
    Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
        (F.obj.obj (op n))) := by
  sorry

/-- The inverse-limit extension of the normalized finite paths.
Source: Weil II (1.1.1) b), (1.1.6)
(blueprint: def-wf-fundamental-representation).
Proof: finite path maps commute with coefficient transitions by the germ rule.
Their composites with the limit projections form a cone. The limit universal
property gives a unique map; inverse paths give its inverse, projectionwise. -/
theorem etaleIntegralPathIso_exists (F : LisseIntegralSheaf l E Y)
    (τ : fiber y ≅ fiber z) :
    ∃! e : lisseIntegralFiber l E Y y F ≅ lisseIntegralFiber l E Y z F,
      ∀ n : ℕ, e.hom ≫ limit.π (F.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber)
          (op n) =
        limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) ≫
          (etaleFinitePathIso (Padic.coefficientExtensionIntegers l E)
            (F.obj.obj (op n)) (F.property.1 n) (etaleIntegralLevel_finite l E F n) τ).hom := by
  sorry

/-- The unique limit map with the specified finite-level projections.
Source: Weil II (1.1.1) b) (blueprint: def-wf-fundamental-representation). -/
def etaleIntegralPathIso (F : LisseIntegralSheaf l E Y) (τ : fiber y ≅ fiber z) :
    lisseIntegralFiber l E Y y F ≅ lisseIntegralFiber l E Y z F :=
  (etaleIntegralPathIso_exists l E F τ).exists.choose

/-- Rational transport is exactly scalar extension of integral transport.
Source: Weil II (1.1.1) c) (blueprint: def-wf-fundamental-representation). -/
def etaleRationalPathIso (F : LisseRationalSheaf l E Y) (τ : fiber y ≅ fiber z) :
    lisseRationalFiber l E Y y F ≅ lisseRationalFiber l E Y z F :=
  (ModuleCat.extendScalars (algebraMap (Padic.coefficientExtensionIntegers l E) E)).mapIso
    (etaleIntegralPathIso l E F.integral τ)

variable (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]

/-- Algebraic transport uses the finite coefficient field already in the object's pair.
Source: Weil II (1.1.1) d) (blueprint: def-wf-fundamental-representation). -/
def etaleAlgebraicPathIso (F : LisseAlgebraicSheaf l Y Q) (τ : fiber y ≅ fiber z) :
    lisseAlgebraicFiber l Y Q y F ≅ lisseAlgebraicFiber l Y Q z F :=
  (ModuleCat.extendScalars (algebraMap (lisseAlgebraicPair l Y Q F).base.val Q)).mapIso
    (etaleRationalPathIso l (lisseAlgebraicPair l Y Q F).base.val
      (lisseCoefficientPairModel l Y Q (lisseAlgebraicPair l Y Q F)) τ)

/-- Its linear equivalence retains the same actual etale adic fibres.
Source: Weil II (1.1.6) (blueprint: def-wf-fundamental-representation). -/
def etaleAlgebraicPath (F : LisseAlgebraicSheaf l Y Q) (τ : fiber y ≅ fiber z) :
    lisseAlgebraicFiber l Y Q y F ≃ₗ[Q] lisseAlgebraicFiber l Y Q z F :=
  (etaleAlgebraicPathIso l Q F τ).toLinearEquiv

/-- The normalized paths obey the representation laws.
Source: Weil II (1.1.6) (blueprint: def-wf-fundamental-representation).
Proof: identity and composition hold on finite-cover germs, then on all finite
stalks. Apply the limit projections and extend scalars twice. -/
theorem etaleAlgebraicPath_laws (F : LisseAlgebraicSheaf l Y Q)
    (t : Spec (.of Ω) ⟶ Y) :
    (etaleAlgebraicPath l Q F (Iso.refl (fiber t))).toLinearMap = LinearMap.id ∧
    ∀ g h : Aut (fiber t),
      (etaleAlgebraicPath l Q F (g * h)).toLinearMap =
        (etaleAlgebraicPath l Q F g).toLinearMap *
          (etaleAlgebraicPath l Q F h).toLinearMap := by
  sorry

/-- The geometric representation on the actual etale fibre.
Source: Weil II (1.1.6) (blueprint: def-wf-fundamental-representation). -/
def etaleGeometricRep (F : LisseAlgebraicSheaf l Y Q) (t : Spec (.of Ω) ⟶ Y) :
    Representation Q (Aut (fiber t)) (lisseAlgebraicFiber l Y Q t F) where
  toFun g := (etaleAlgebraicPath l Q F g).toLinearMap
  map_one' := (etaleAlgebraicPath_laws l Q F t).1
  map_mul' := (etaleAlgebraicPath_laws l Q F t).2

/-- An actual etale adic Weil sheaf, with no Frobenius-stable integral lattice required.
Source: Weil II (1.1.10)(i) (blueprint: def-wf-fundamental-representation). -/
abbrev EtaleLisseWeilSheaf (h : Y ≅ Y) :=
  Endofunctor.IsoAlgebra (lisseAlgebraicAutomorphismPullback h l Q)

/-- The stalk of an algebraic-coefficient morphism on the recorded object fibres.
Source: Weil II (1.1.1) d) (blueprint: def-wf-fundamental-representation). -/
def etaleAlgebraicFiberMap (t : Spec (.of Ω) ⟶ Y)
    {F G : LisseAlgebraicSheaf l Y Q} (f : F ⟶ G) :
    lisseAlgebraicFiber l Y Q t F ⟶ lisseAlgebraicFiber l Y Q t G :=
  eqToHom (lisseAlgebraicFiberFunctor_obj l Y t Q F).symm ≫
    (lisseAlgebraicFiberFunctor l Y t Q).map f ≫
      eqToHom (lisseAlgebraicFiberFunctor_obj l Y t Q G)

/-- The degree-one operator is path transport, inverse pullback-fibre identification,
then the actual etale Weil descent datum on the fibre.
Source: Weil II (1.1.10)(i) (blueprint: def-wf-fundamental-representation). -/
def etaleWeilFrobenius (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (β : fiber t ≅ fiber (t ≫ h.hom)) (F : EtaleLisseWeilSheaf l Q h) :
    lisseAlgebraicFiber l Y Q t F.carrier ≃ₗ[Q] lisseAlgebraicFiber l Y Q t F.carrier :=
  (etaleAlgebraicPathIso l Q F.carrier β ≪≫
    (lisseAlgebraicAutomorphismFiberIso h l Q t F.carrier).symm ≪≫
    (eqToIso (lisseAlgebraicFiberFunctor_obj l Y t Q _)).symm ≪≫
    (lisseAlgebraicFiberFunctor l Y t Q).mapIso F.str ≪≫
    eqToIso (lisseAlgebraicFiberFunctor_obj l Y t Q _)).toLinearEquiv

/-- General degree data and the canonical finite-fibre path for the chosen arithmetic
lift. This is the source's homotopy-exact-sequence interface, independent of dimension.
Source: blueprint def-wf-fundamental-representation, conjugation convention
(blueprint: def-wf-fundamental-representation). -/
structure EtaleWeilDegreeData (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (G : Type v) [Group G] (d : Monodromy.DegreeDatum G) where
  /-- The geometric group identification. -/
  geom : Aut (fiber t) ≃* d.deg.ker
  /-- Transport from t to its Frobenius image, inverse to lambda_s in the source. -/
  path : fiber t ≅ fiber (t ≫ h.hom)
  /-- The finite-fibre conjugation rule fixes the lift convention. -/
  conjugation (g : Aut (fiber t)) :
    (geom (path ≪≫ pullbackPathIso h.hom g ≪≫ path.symm) : G) =
      d.degreeOneElement⁻¹ * geom g * d.degreeOneElement

/-- A representation is uniquely determined by its geometric restriction and the
specified degree-one operator; this verifies the general extension construction.
Source: Weil II (1.1.10), blueprint def-wf-fundamental-representation
(blueprint: def-wf-fundamental-representation).
Proof: naturality of descent and finite-path conjugation give T rho(g) T^-1 =
rho(sgs^-1), first at finite level and then after both coefficient extensions.
Every w is uniquely a s^n with a geometric. Set rho(w)=rho(a)T^n. The relation
proves multiplicativity, the geometric and degree-one rules, and uniqueness. -/
theorem etaleFundamentalRep_exists (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    {G : Type v} [Group G] (d : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (F : EtaleLisseWeilSheaf l Q h) :
    ∃! ρ : Representation Q G (lisseAlgebraicFiber l Y Q t F.carrier),
      (∀ g : Aut (fiber t), ρ (D.geom g) = etaleGeometricRep l Q F.carrier t g) ∧
      ρ d.degreeOneElement = (etaleWeilFrobenius l Q h t D.path F).toLinearMap := by
  sorry

/-- The unique extension, on actual etale adic fibres, with the source's prescribed
geometric action and degree-one operator. This choice is uniquely determined by the
preceding theorem, not data chosen from a bare existence assertion.
Source: Weil II (1.1.10) (blueprint: def-wf-fundamental-representation). -/
def etaleFundamentalRep (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    {G : Type v} [Group G] (d : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (F : EtaleLisseWeilSheaf l Q h) :
    Representation Q G (lisseAlgebraicFiber l Y Q t F.carrier) :=
  (etaleFundamentalRep_exists l Q h t d D F).exists.choose

/-- The extension has the source's finite-dimensional l-adic geometric restriction;
with the discrete-degree Weil topology this is continuity of the whole representation.
Source: Weil II (1.1.6), (1.1.10)
(blueprint: def-wf-fundamental-representation).
Proof: the finite-cover germ normalization identifies the geometric restriction
with the evaluation action in cor-galois-lisse-representations. Its integral system
has a finite coefficient-field model, so inverse limits give a continuous integral
action and rationalization gives a continuous E-action. Extend to Q using precisely
the finite model in F's coefficient pair. This proves IsLAdic and finite dimension.
Each degree coset is a translate of the open geometric subgroup; multiplication by
a fixed power of the degree-one operator is a continuous linear automorphism. -/
theorem etaleFundamentalRep_isLAdic (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    {G : Type v} [Group G] (d : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (F : EtaleLisseWeilSheaf l Q h) :
    Representation.IsLAdic l Q (ProfiniteGrp.of (Aut (fiber t)))
      (lisseAlgebraicFiber l Y Q t F.carrier)
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv Q _).toMonoidHom.comp
        (Representation.asGroupHom
          ((etaleFundamentalRep l Q h t d D F).comp
            (d.deg.ker.subtype.comp D.geom.toMonoidHom)))) := by
  sorry

/-- Changing the degree-one lift with its prescribed finite-fibre path leaves the
extension unchanged. Source: Weil II (1.1.10), the node's lift-change formula
(blueprint: def-wf-fundamental-representation).
Proof: finite path naturality for the descent map gives T' = rho_geom(a) T.
The geometric actions coincide. The first extension therefore has the second
extension's geometric restriction and its value on s'=a s. Uniqueness of the
extension gives equality, without assuming a Frobenius-stable integral lattice. -/
theorem etaleFundamentalRep_liftChange (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    {G : Type v} [Group G] (d d' : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (D' : EtaleWeilDegreeData h t G d')
    (a : Aut (fiber t))
    (hgeom : ∀ g : Aut (fiber t), (D.geom g : G) = (D'.geom g : G))
    (hlift : d'.degreeOneElement = (D.geom a : G) * d.degreeOneElement)
    (hpath : D'.path = D.path ≪≫ pullbackPathIso h.hom a)
    (F : EtaleLisseWeilSheaf l Q h) :
    etaleFundamentalRep l Q h t d D F = etaleFundamentalRep l Q h t d' D' F := by
  sorry

/-- Change of geometric base point is the normalized etale adic path isomorphism.
Source: Weil II (1.1.6), (1.1.10)
(blueprint: def-wf-fundamental-representation).
Proof: the geometric intertwining equation is the finite-cover path conjugation
identity, then its inverse limit and scalar extensions. The finite-path square
with Frobenius, naturality of descent and the pullback-fibre identification give
the degree-one intertwining equation. Every Weil element is a geometric element
times a power of the degree-one element, so these two equations give the result. -/
theorem etaleFundamentalRep_changeBasePoint (h : Y ≅ Y)
    (t t' : Spec (.of Ω) ⟶ Y) {G : Type v} [Group G] (d : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (D' : EtaleWeilDegreeData h t' G d)
    (τ : fiber t ≅ fiber t')
    (hgeom : ∀ g : Aut (fiber t),
      D'.geom (τ.symm ≪≫ g ≪≫ τ) = D.geom g)
    (hpath : D.path ≪≫ pullbackPathIso h.hom τ = τ ≪≫ D'.path)
    (F : EtaleLisseWeilSheaf l Q h) :
    ∀ (g : G) (x : lisseAlgebraicFiber l Y Q t F.carrier),
      etaleAlgebraicPath l Q F.carrier τ (etaleFundamentalRep l Q h t d D F g x) =
        etaleFundamentalRep l Q h t' d D' F g (etaleAlgebraicPath l Q F.carrier τ x) := by
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.WeilGroup
open AlgebraicGeometry.Scheme Scheme.FiniteEtale
/-- The coefficient-free finite-path data already used upstream, now applied to etale
adic fibres. There is no new choice of arithmetic lift or geometric action.
Source: blueprint def-wf-fundamental-representation
(blueprint: def-wf-fundamental-representation). -/
def WeilMonodromyData.toEtale
    {K : Type u} [Field K] [Finite K] {C : Scheme.{u}}
    [C.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))]
    {W : WeilGroup (C ↘ Spec (.of K))} {B : BasePointData W}
    (D : WeilMonodromyData B) :
    EtaleWeilDegreeData (C ↘ Spec (.of K)).geometricGaloisFrobenius B.t
      W.carrier D.degreeDatum where
  geom := D.geomEquiv.toMulEquiv
  path := B.frobPath
  conjugation := D.geomEquiv_conj
end AlgebraicGeometry.WeilGroup
