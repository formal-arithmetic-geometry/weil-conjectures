module

public import Sheaf.Paper.VerdierPairingThreeTransposes
public import Sheaf.SixFunctors.VerdierExchangeData
public import Sheaf.SixFunctors.TensorHomTranspositionData

/-! # Composition mate and normalization of Verdier exchange

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-thm-frobenius/prop-weil-operations.proof.md, formal duality exchange;
sec-six-functors/sk-thm-sf-package/fix-cor-verdier-exchange.proof.md, Steps 1--2,
and fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-pod-verdier-composition-mate-normalization).

The formulas use the recorded fixed-pair domains and adjunctions. There is no
exceptional adjoint on an ambient category. The internal-adjunction isomorphism
is supplied only in the final, conditional normalization assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z vx vy vz vb
open CategoryTheory CategoryTheory.Endofunctor Opposite AlgebraicGeometry
open WeilConjectures.VerdierPairing

namespace WeilConjectures.VerdierCompositionMate

section Mate
variable {X : Type v} {Y : Type w} {S : Type z}
  [Category.{vx} X] [Category.{vy} Y] [Category.{vz} S]
  {ΦX : X ⥤ X} {ΦY : Y ⥤ Y} {ΦS : S ⥤ S}
  {F : X ⥤ Y} {G : Y ⥤ X} {H : Y ⥤ S} {J : S ⥤ Y}
  {U : X ⥤ S} {W : S ⥤ X}

/-- The right-adjoint composition isomorphism in the existing Weil-pair category.
Its underlying comparison is normalized in composition_mate below.
Source: fix-cor-verdier-exchange.proof.md, Step 1
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def weilComposition
    (e : LiftedAdjunction ΦX ΦY F G) (h : LiftedAdjunction ΦY ΦS H J)
    (j : LiftedAdjunction ΦX ΦS U W)
    (alpha : IsoAlgebra.mapOfNatIso e.leftComparison ⋙
      IsoAlgebra.mapOfNatIso h.leftComparison ≅ IsoAlgebra.mapOfNatIso j.leftComparison) :
    IsoAlgebra.mapOfNatIso h.rightComparison ⋙
      IsoAlgebra.mapOfNatIso e.rightComparison ≅ IsoAlgebra.mapOfNatIso j.rightComparison :=
  VerdierExchange.composition e.weilAdj h.weilAdj j.weilAdj alpha

/-- The specified dualizing mate has the pasted-counit formula and is a Weil arrow.
The same assertion at the coefficient unit is precisely c:G omega_Y ≅ omega_X.
Source: fix-cor-verdier-exchange.proof.md, Step 1
(blueprint: lem-pod-verdier-composition-mate-normalization).
Proof: paste the two adjunctions using def-weil-pbc-composite-adjunction.
Conjugate alpha inverse using def-weil-pbc-adjunction-conjugate, which preserves
isomorphisms. Its component is eta^U followed by W(alpha inverse followed by
the pasted counit). Repeat in the fixed-pair category; the supplied unit and
counit normalizations and alpha normalization give the same underlying formula.
The pair arrow condition then proves equivariance, including at Lambda_s. -/
theorem composition_mate
    (e : LiftedAdjunction ΦX ΦY F G) (h : LiftedAdjunction ΦY ΦS H J)
    (j : LiftedAdjunction ΦX ΦS U W) (alpha : F ⋙ H ≅ U)
    (alphaW : IsoAlgebra.mapOfNatIso e.leftComparison ⋙
      IsoAlgebra.mapOfNatIso h.leftComparison ≅ IsoAlgebra.mapOfNatIso j.leftComparison)
    (_alpha_eq : ∀ K : IsoAlgebra ΦX, (alphaW.hom.app K).hom.f = alpha.hom.app K.carrier)
    (Z : IsoAlgebra ΦS) :
    (e.adj.comp h.adj).counit.app Z.carrier =
      H.map (e.adj.counit.app (J.obj Z.carrier)) ≫ h.adj.counit.app Z.carrier ∧
    (VerdierExchange.composition e.adj h.adj j.adj alpha).hom.app Z.carrier =
      j.adj.unit.app (G.obj (J.obj Z.carrier)) ≫
        W.map (alpha.inv.app (G.obj (J.obj Z.carrier)) ≫
          H.map (e.adj.counit.app (J.obj Z.carrier)) ≫ h.adj.counit.app Z.carrier) ∧
    ((weilComposition e h j alphaW).hom.app Z).hom.f =
      (VerdierExchange.composition e.adj h.adj j.adj alpha).hom.app Z.carrier := by
  refine ⟨Adjunction.comp_counit_app _ _ _, ?_, ?_⟩
  · simp only [VerdierExchange.composition, conjugateIsoEquiv_apply_hom,
      Iso.symm_hom, conjugateEquiv_apply_app, Adjunction.comp_counit_app,
      ← Functor.map_comp, Functor.comp_obj]
  · have alpha_inv_eq (K : IsoAlgebra ΦX) :
        (alphaW.inv.app K).hom.f = alpha.inv.app K.carrier := by
      have hi := congrArg (fun f ↦ (IsoAlgebra.forget ΦS).map f)
        (alphaW.inv_hom_id_app K)
      change (alphaW.inv.app K).hom.f ≫ (alphaW.hom.app K).hom.f = 𝟙 _ at hi
      rw [_alpha_eq] at hi
      apply (cancel_mono (alpha.hom.app K.carrier)).1
      simpa only [IsoAlgebra.mapOfNatIso_obj_carrier, Iso.inv_hom_id_app] using hi
    simp only [weilComposition, VerdierExchange.composition, conjugateIsoEquiv_apply_hom,
      Iso.symm_hom, conjugateEquiv_apply_app, Adjunction.comp_counit_app]
    simp only [IsoAlgebra.comp_hom_f, IsoAlgebra.mapOfNatIso_map_hom_f,
      j.unit_eq, e.counit_eq, h.counit_eq, alpha_inv_eq,
      IsoAlgebra.mapOfNatIso_obj_carrier, Functor.comp_obj]
end Mate

section Transposition
variable {X : Type v} {Y : Type w} [Category.{vx} X] [Category.{vy} Y]
  {ΦX : X ⥤ X} {ΦY : Y ⥤ Y}
  {F : X ⥤ Y} {G : Y ⥤ X} {P : Y ⥤ X} {Q : X ⥤ Y}

/-- The exceptional transpose of inverse projection followed by counit evaluation.
Source: fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def exceptionalTranspose
    (e : LiftedAdjunction ΦX ΦY F G) (_o : LiftedAdjunction ΦY ΦX P Q)
    (x : TensorHomData ΦX) (y : TensorHomData ΦY) (omega : Y) (M : X)
    (ay : y.tensor.obj (F.obj M) ⊣ y.hom.obj (op (F.obj M)))
    (pi : (y.tensor.obj (F.obj M)).obj ((y.hom.obj (op (F.obj M))).obj omega) ≅
      F.obj ((x.tensor.obj M).obj
        (P.obj ((y.hom.obj (op (F.obj M))).obj omega)))) :
    (x.tensor.obj M).obj (P.obj ((y.hom.obj (op (F.obj M))).obj omega)) ⟶
      G.obj omega :=
  e.adj.homEquiv _ _ (pi.inv ≫ ay.counit.app omega)

/-- Apply the last two transposes in tensor--Hom then ordinary-adjunction order.
Source: fix-cor-verdier-exchange.proof.md, Step 2
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def lastTransposes (o : LiftedAdjunction ΦY ΦX P Q) (x : TensorHomData ΦX)
    (M : X) (ax : x.tensor.obj M ⊣ x.hom.obj (op M)) {A : Y} {N : X}
    (t : (x.tensor.obj M).obj (P.obj A) ⟶ N) :
    A ⟶ Q.obj ((x.hom.obj (op M)).obj N) :=
  o.adj.homEquiv _ _ (ax.homEquiv _ _ t)

/-- The prescribed five-bijection chain, in the forward internal-adjunction direction.
It is defined for every test object B in the supplied domain.
Source: fix-lem-tensor-adjunction.proof.md, Step 1, read backwards
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def internalHomChain
    (e : LiftedAdjunction ΦX ΦY F G) (o : LiftedAdjunction ΦY ΦX P Q)
    (x : TensorHomData ΦX) (y : TensorHomData ΦY) (M : X) (N B : Y)
    (ax : x.tensor.obj M ⊣ x.hom.obj (op M))
    (ay : y.tensor.obj (F.obj M) ⊣ y.hom.obj (op (F.obj M)))
    (pi : (y.tensor.obj (F.obj M)).obj B ⟶ F.obj ((x.tensor.obj M).obj (P.obj B)))
    (u' : B ⟶ Q.obj ((x.hom.obj (op M)).obj (G.obj N))) :
    B ⟶ (y.hom.obj (op (F.obj M))).obj N :=
  ay.homEquiv _ _
    (pi ≫ (e.adj.homEquiv _ _).symm
      (ax.homEquiv _ _ |>.symm ((o.adj.homEquiv _ _).symm u')))

/-- Substituting the canonical dualizing mate commutes with the last two transposes.
This needs no finite-Tor or exceptional-admissibility assertion.
Source: prop-weil-operations.proof.md, formal exchange sentence
(blueprint: lem-pod-verdier-composition-mate-normalization).
Proof: the tensor transpose of t followed by c is H_M(c) after the tensor
transpose of t, by homEquiv_naturality_right. Apply the same naturality to the
ordinary adjunction. Functoriality of Q gives exactly the substitution composite. -/
theorem substitution
    (o : LiftedAdjunction ΦY ΦX P Q) (x : TensorHomData ΦX)
    (M : X) (ax : x.tensor.obj M ⊣ x.hom.obj (op M)) {A : Y} {N N' : X}
    (c : N ⟶ N') (t : (x.tensor.obj M).obj (P.obj A) ⟶ N) :
    lastTransposes o x M ax (t ≫ c) =
      lastTransposes o x M ax t ≫ Q.map ((x.hom.obj (op M)).map c) := by
  unfold lastTransposes
  rw [ax.homEquiv_naturality_right, o.adj.homEquiv_naturality_right]

/-- The substitution map is a Weil morphism under the supplied canonical Hom and Q lifts.
Source: prop-weil-operations.proof.md, formal exchange sentence
(blueprint: lem-pod-verdier-composition-mate-normalization).
Proof: c is a morphism in the fixed-pair category by composition_mate. Apply the
recorded Hom lift in its second variable and the recorded ordinary direct-image
lift. Their underlying maps are H_M(c) and QH_M(c), respectively. -/
theorem substitution_weil
    (o : LiftedAdjunction ΦY ΦX P Q) (x : TensorHomData ΦX)
    (M N N' : IsoAlgebra ΦX) (c : N ⟶ N') :
    ((IsoAlgebra.mapOfNatIso o.rightComparison).obj
      ((x.weilHom.obj (op M)).obj N)).str.hom ≫
        Q.map ((x.hom.obj (op M.carrier)).map c.hom.f) =
      ΦY.map (Q.map ((x.hom.obj (op M.carrier)).map c.hom.f)) ≫
        ((IsoAlgebra.mapOfNatIso o.rightComparison).obj
          ((x.weilHom.obj (op M)).obj N')).str.hom := by
  have hm : ((x.weilHom.obj (op M)).map c).hom.f =
      (x.hom.obj (op M.carrier)).map c.hom.f := by
    simp [TensorHomData.weilHom, IsoAlgebra.mapOfNatIso₂, IsoAlgebra.prod,
      IsoAlgebra.opFunctor]
  simpa only [IsoAlgebra.str_hom, IsoAlgebra.mapOfNatIso_map_hom_f, hm] using
    ((IsoAlgebra.mapOfNatIso o.rightComparison).map
      ((x.weilHom.obj (op M)).map c)).hom.h.symm
end Transposition

end WeilConjectures.VerdierCompositionMate

namespace WeilConjectures.VerdierCompositionMate

section Components
variable {X : Type v} {Y : Type w} [Category.{vx} X] [Category.{vy} Y]
  {ΦX : X ⥤ X} {ΦY : Y ⥤ Y}
  {F : X ⥤ Y} {G : Y ⥤ X} {P : Y ⥤ X} {Q : X ⥤ Y}

/-- The unsubstituted triple transpose s_M, with its specified projection isomorphism.
Source: fix-cor-verdier-exchange.proof.md, Step 2
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def preExchange
    (e : LiftedAdjunction ΦX ΦY F G) (o : LiftedAdjunction ΦY ΦX P Q)
    (x : TensorHomData ΦX) (y : TensorHomData ΦY) (omega : Y) (M : X)
    (ax : x.tensor.obj M ⊣ x.hom.obj (op M))
    (ay : y.tensor.obj (F.obj M) ⊣ y.hom.obj (op (F.obj M)))
    (pi : (y.tensor.obj (F.obj M)).obj ((y.hom.obj (op (F.obj M))).obj omega) ≅
      F.obj ((x.tensor.obj M).obj
        (P.obj ((y.hom.obj (op (F.obj M))).obj omega)))) :
    (y.hom.obj (op (F.obj M))).obj omega ⟶ Q.obj ((x.hom.obj (op M)).obj (G.obj omega)) :=
  lastTransposes o x M ax (exceptionalTranspose e o x y omega M ay pi)

/-- The exchange component substitutes c before the final tensor--Hom and ordinary
transposes, exactly as StageData.epsilon does.
Source: def-sf-verdier-exchange-data, component recipe
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def exchangeComponent
    (e : LiftedAdjunction ΦX ΦY F G) (o : LiftedAdjunction ΦY ΦX P Q)
    (x : TensorHomData ΦX) (y : TensorHomData ΦY) (omega : Y) (M : X)
    (ax : x.tensor.obj M ⊣ x.hom.obj (op M))
    (ay : y.tensor.obj (F.obj M) ⊣ y.hom.obj (op (F.obj M)))
    (pi : (y.tensor.obj (F.obj M)).obj ((y.hom.obj (op (F.obj M))).obj omega) ≅
      F.obj ((x.tensor.obj M).obj
        (P.obj ((y.hom.obj (op (F.obj M))).obj omega))))
    {omegaX : X} (c : G.obj omega ⟶ omegaX) :
    (y.hom.obj (op (F.obj M))).obj omega ⟶ Q.obj ((x.hom.obj (op M)).obj omegaX) :=
  lastTransposes o x M ax (exceptionalTranspose e o x y omega M ay pi ≫ c)
end Components

/-- Composition-mate normalization on the actual rational/common-stage supplied domains.
All transposes and the projection map are prescribed. The final clause is conditional
on the normalized internal-adjunction isomorphism I, supplied under the additional
admissibility and finite-Tor hypotheses in fix-lem-tensor-adjunction and
fix-cor-verdier-exchange; it does not assert that such I exists on every supplied domain.
Source: prop-weil-operations.proof.md, formal exchange sentence;
fix-cor-verdier-exchange.proof.md, Steps 1--2;
fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-pod-verdier-composition-mate-normalization).
Proof:
1. Paste F left adjoint to G and H left adjoint to J. Conjugating alpha inverse
   gives c with the formula in composition_mate, including its fixed-pair lift.
2. Inverting an equivariant isomorphism and composing equivariant arrows preserve
   the fixed-pair arrow equation; thus c is Weil at the coefficient unit Z.
3. Tensor--Hom naturality makes the transpose of ct equal to H_M(c) times the
   transpose of t. Ordinary-adjunction naturality gives QH_M(c) times s_M.
4. The definition of exchangeComponent is the prescribed epsilon_M construction,
   with substitution before the last two transposes. substitution_weil gives
   equivariance of its substitution map. These steps require no admissibility.
5. Under the additional hypotheses, take I from fix-lem-tensor-adjunction with
   the stipulated Hom-chain normalization. Apply that chain to s_M. The three
   inverse transposes give t then b; precomposition with pi cancels pi inverse,
   leaving evaluation. Its tensor transpose is the identity of A. Thus s_M I=1,
   so s_M=I inverse and is invertible. Step 4 gives epsilon_M=I inverse then
   QH_M(c). At field stages A is in the finite-Tor domain by
   def-weil-finite-tor-amplitude. No integral representative is selected. -/
theorem verdier_composition_mate_normalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l))
    (_embedding : ∀ E' ∈ E, E'.carrier →ₐ[Padic l] Ω)
    (SX : Domain D l hl Ω X₀ E) (SY : Domain D l hl Ω Y₀ E)
    {B : Type v} [Category.{vb} B]
    (d : CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage
      (DX := SX.C) (DB := B) (DY := SY.C) (DX' := SX.C) (DB' := B) (DY' := SY.C))
    (_pullback : d.pull ⋙ SX.objects.ι ≅
      SY.objects.ι ⋙ geometricPullback D l hl Ω X₀ Y₀ f₀ E)
    (x : TensorHomData SX.phi) (y : TensorHomData SY.phi)
    (_x_realizes : Realizes D l hl Ω X₀ E SX x)
    (_y_realizes : Realizes D l hl Ω Y₀ E SY y)
    (_tensorX : d.tensorX = x.tensor) (_tensorY : d.tensorY = y.tensor)
    {G : SY.C ⥤ SX.C} {Q : SX.C ⥤ SY.C}
    (e : LiftedAdjunction SX.phi SY.phi d.compactSupport G)
    (o : LiftedAdjunction SY.phi SX.phi d.pull Q)
    {S : Type z} [Category.{vz} S] (ΦS : S ⥤ S)
    {H : SY.C ⥤ S} {J : S ⥤ SY.C} {U : SX.C ⥤ S} {W : S ⥤ SX.C}
    (h : LiftedAdjunction SY.phi ΦS H J) (j : LiftedAdjunction SX.phi ΦS U W)
    (alpha : d.compactSupport ⋙ H ≅ U)
    (alphaW : IsoAlgebra.mapOfNatIso e.leftComparison ⋙
      IsoAlgebra.mapOfNatIso h.leftComparison ≅ IsoAlgebra.mapOfNatIso j.leftComparison)
    (_alpha_eq : ∀ K : IsoAlgebra SX.phi,
      (alphaW.hom.app K).hom.f = alpha.hom.app K.carrier)
    (Z : IsoAlgebra ΦS) (M : IsoAlgebra SX.phi)
    (ax : x.tensor.obj M.carrier ⊣ x.hom.obj (op M.carrier))
    (ay : y.tensor.obj (d.compactSupport.obj M.carrier) ⊣
      y.hom.obj (op (d.compactSupport.obj M.carrier)))
    (pi : (y.tensor.obj (d.compactSupport.obj M.carrier)).obj
        ((y.hom.obj (op (d.compactSupport.obj M.carrier))).obj (J.obj Z.carrier)) ≅
      d.compactSupport.obj ((x.tensor.obj M.carrier).obj (d.pull.obj
        ((y.hom.obj (op (d.compactSupport.obj M.carrier))).obj (J.obj Z.carrier)))))
    (_pi_eq : HEq pi.hom ((d.projection.app M.carrier).app
      ((y.hom.obj (op (d.compactSupport.obj M.carrier))).obj (J.obj Z.carrier)))) :
    exchangeComponent e o x y (J.obj Z.carrier) M.carrier ax ay pi
        ((VerdierExchange.composition e.adj h.adj j.adj alpha).hom.app Z.carrier) =
      preExchange e o x y (J.obj Z.carrier) M.carrier ax ay pi ≫
      Q.map ((x.hom.obj (op M.carrier)).map
        ((VerdierExchange.composition e.adj h.adj j.adj alpha).hom.app Z.carrier)) ∧
    (∀ (piAll : ∀ A : SY.C, (y.tensor.obj (d.compactSupport.obj M.carrier)).obj A ⟶
          d.compactSupport.obj ((x.tensor.obj M.carrier).obj (d.pull.obj A)))
      (_piAll_eq : ∀ A : SY.C, HEq (piAll A) ((d.projection.app M.carrier).app A))
      (I : Q.obj ((x.hom.obj (op M.carrier)).obj (G.obj (J.obj Z.carrier))) ≅
        (y.hom.obj (op (d.compactSupport.obj M.carrier))).obj (J.obj Z.carrier)),
      (∀ (A : SY.C)
        (u' : A ⟶ Q.obj ((x.hom.obj (op M.carrier)).obj (G.obj (J.obj Z.carrier)))),
        u' ≫ I.hom = internalHomChain e o x y M.carrier (J.obj Z.carrier) A
          ax ay (piAll A) u') →
      IsIso (preExchange e o x y (J.obj Z.carrier) M.carrier ax ay pi) ∧
      preExchange e o x y (J.obj Z.carrier) M.carrier ax ay pi = I.inv ∧
      exchangeComponent e o x y (J.obj Z.carrier) M.carrier ax ay pi
          ((VerdierExchange.composition e.adj h.adj j.adj alpha).hom.app Z.carrier) =
        I.inv ≫ Q.map ((x.hom.obj (op M.carrier)).map
          ((VerdierExchange.composition e.adj h.adj j.adj alpha).hom.app Z.carrier))) := by
  have hs := substitution o x M.carrier ax
    ((VerdierExchange.composition e.adj h.adj j.adj alpha).hom.app Z.carrier)
    (exceptionalTranspose e o x y (J.obj Z.carrier) M.carrier ay pi)
  refine ⟨hs, ?_⟩
  intro piAll hpiAll I hI
  let A := (y.hom.obj (op (d.compactSupport.obj M.carrier))).obj (J.obj Z.carrier)
  have hpi : piAll A = pi.hom :=
    eq_of_heq ((hpiAll A).trans _pi_eq.symm)
  have hcancel : preExchange e o x y (J.obj Z.carrier) M.carrier ax ay pi ≫
      I.hom = 𝟙 _ := by
    rw [hI]
    unfold internalHomChain preExchange lastTransposes exceptionalTranspose
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hpi]
    simp only [Iso.hom_inv_id_assoc]
    rw [← ay.homEquiv_symm_id, Equiv.apply_symm_apply]
  have heq : preExchange e o x y (J.obj Z.carrier) M.carrier ax ay pi = I.inv := by
    apply (cancel_mono I.hom).1
    rw [hcancel, I.inv_hom_id]
  refine ⟨?_, heq, ?_⟩
  · rw [heq]
    infer_instance
  · exact hs.trans (congrArg (fun f ↦ f ≫ _) heq)

end WeilConjectures.VerdierCompositionMate


namespace WeilConjectures.VerdierCompositionMate
open ConstructibleExceptionalCoefficients

/-- Forget only the dualizing identification from the recorded stage datum.
This reuses the tensor-adjunction model, with the very same projection and adjunctions.
Source: def-sf-verdier-exchange-data, internal-adjunction ingredients
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def stageTensorModel
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation l Ω X Y s} {H : Operation l Ω Y S s} {U : Operation l Ω X S s}
    {unit : C l Ω S s} (d : VerdierExchange.StageData l Ω s F H U unit) :
    TensorAdjunctionExchange.Model l Ω s F where
  homX := d.homX
  homY := d.homY
  closedX := d.closedX
  closedY := d.closedY
  pull := d.pull
  star := d.star
  adjunction := d.adjunction
  projection := d.projection

/-- The right-hand substitution composite is exactly the existing canonical epsilon_M.
Thus a stage-conclusion isomorphism has this precise component, rather than an
independently selected duality isomorphism. The specified tensor order here is the
right-tensor convention of StageData, including its recorded projection normalization.
Source: fix-cor-verdier-exchange.proof.md, Step 2; def-sf-verdier-exchange-data
(blueprint: lem-pod-verdier-composition-mate-normalization).
Proof: unfold StageData.epsilon and Model.inverseComponent. Naturality of the tensor
Hom bijection moves dualizing.hom through the tensor transpose. Naturality of the
ordinary bijection moves its Hom image through the ordinary transpose. This gives
the displayed composite. If a StageConclusion is supplied, its components field
identifies its isomorphism component with the same epsilon_M. -/
theorem stage_epsilon
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation l Ω X Y s} {H : Operation l Ω Y S s} {U : Operation l Ω X S s}
    {unit : C l Ω S s} (d : VerdierExchange.StageData l Ω s F H U unit)
    (M : C l Ω X s) :
    d.epsilon l Ω M =
      (stageTensorModel l Ω d).inverseComponent l Ω M (H.G.obj unit) ≫
        d.star.map (d.homX.map (Prod.mkHom (𝟙 (op M)) d.dualizing.hom)) ∧
    (∀ conclusion : VerdierExchange.StageConclusion l Ω d,
      conclusion.epsilon.hom.app (op M) =
        (stageTensorModel l Ω d).inverseComponent l Ω M (H.G.obj unit) ≫
          d.star.map (d.homX.map (Prod.mkHom (𝟙 (op M)) d.dualizing.hom))) := by
  have heq : d.epsilon l Ω M =
      (stageTensorModel l Ω d).inverseComponent l Ω M (H.G.obj unit) ≫
        d.star.map (d.homX.map (Prod.mkHom (𝟙 (op M)) d.dualizing.hom)) := by
    let t := F.adjunction.homEquiv _ _
      ((d.projection (d.homY.obj (op (F.F.obj M), H.G.obj unit)) M).hom ≫
        d.closedY.evaluation (F.F.obj M) (H.G.obj unit))
    exact (congrArg (fun a ↦ d.adjunction.homEquiv _ _ a)
      ((d.closedX.adjunction M).homEquiv_naturality_right t d.dualizing.hom)).trans
      (d.adjunction.homEquiv_naturality_right
        ((d.closedX.adjunction M).homEquiv _ _ t)
        ((Prod.sectR (op M) _ ⋙ d.homX).map d.dualizing.hom))
  refine ⟨heq, ?_⟩
  intro conclusion
  exact (conclusion.components M).trans heq

end WeilConjectures.VerdierCompositionMate
