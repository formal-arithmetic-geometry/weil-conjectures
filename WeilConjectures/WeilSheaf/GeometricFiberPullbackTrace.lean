/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelGaloisTrace
public import WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv
public import WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.StalkComparison
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# The trace function of a Weil sheaf pulled back from the model

Let `p : X̄ ⟶ X₀` be the projection of the geometric fibre and `H` an `ℓ`-adic sheaf on `X₀`. If
`F` is a Weil sheaf with an isomorphism `F ≅ p^* H` carrying its Weil structure to the canonical
one `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H`, the trace function of `F` at an `𝔽_{qᵐ}`-point is the
trace of the Galois action of `σᵐ` on the global sections `Γ(Spec k̄, x̄^* H)` at the geometric
point `x̄` over the point
(`AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_galoisGlobalSections_of_iso`); in
particular for `F = p^* H` itself
(`AlgebraicGeometry.WeilSheaf.traceFunction_geometricFiberPullback_eq_trace_galoisGlobalSections`).

The proof goes through the transports of global sections
(`AlgebraicGeometry.ProEtale.globalSectionsTransport`): the iterated Weil structures of `F` are
the canonical morphisms `(Frᵐ)^* p^* H ⟶ p^* H`
(`AlgebraicGeometry.WeilSheaf.frobeniusPowStr_comp_eq_of_iso`), and the transports along `p` of
the stalk of `H` at `x̄` intertwine the Galois action with the stalk Frobenius of `F`
(`AlgebraicGeometry.ProEtale.globalSectionsTransport_comm_of_upperStar`).
-/

@[expose] public section

universe u u'

open CategoryTheory

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The canonical morphism `g^* p^* N ≅ (g ≫ p)^* N = p^* N` for an endomorphism `g` with
`g ≫ p = p`. -/
noncomputable def upperStarInvariantHom {Z Y : Scheme.{u}} (p : Z ⟶ Y) {g : Z ⟶ Z}
    (hg : g ≫ p = p) (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (g)^*[A].obj ((p)^*[A].obj N) ⟶ (p)^*[A].obj N :=
  (upperStarComp A g p).inv.app N ≫ (upperStarCongr A hg).hom.app N

/-- The canonical morphisms `g^* p^* N ⟶ p^* N` along equal endomorphisms agree. -/
lemma upperStarCongr_hom_app_comp_upperStarInvariantHom {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    {g g' : Z ⟶ Z} (e : g = g') (hg : g ≫ p = p) (hg' : g' ≫ p = p)
    (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A e).hom.app ((p)^*[A].obj N) ≫ upperStarInvariantHom A p hg' N =
      upperStarInvariantHom A p hg N := by
  subst e
  simp [upperStarCongr]

/-- Three congruence isomorphisms of pullbacks compose to one; the composite equality is an
independent hypothesis, so that the kernel never compares proofs of equalities of morphisms. -/
lemma upperStarCongr_hom_app_trans_trans {P Q : Scheme.{u}} {x y z w : P ⟶ Q} (h : x = y)
    (h' : y = z) (h'' : z = w) (e : x = w) (N : Sheaf (Scheme.ProEt.topology Q) A) :
    (upperStarCongr A h).hom.app N ≫ (upperStarCongr A h').hom.app N ≫
        (upperStarCongr A h'').hom.app N =
      (upperStarCongr A e).hom.app N := by
  subst h h' h''
  simp [upperStarCongr]

/-- **The cocycle condition** of the canonical morphisms `g^* p^* N ⟶ p^* N`: for `b ≫ c = a`,
the canonical morphism along `a` is `a^* p^* N ≅ b^* c^* p^* N ⟶ b^* p^* N ⟶ p^* N`. -/
lemma upperStarFactor_hom_app_comp_upperStarInvariantHom {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    {a b c : Z ⟶ Z} (e : b ≫ c = a) (ha : a ≫ p = p) (hb : b ≫ p = p) (hc : c ≫ p = p)
    (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarFactor A e).hom.app ((p)^*[A].obj N) ≫
        (b)^*[A].map (upperStarInvariantHom A p hc N) ≫ upperStarInvariantHom A p hb N =
      upperStarInvariantHom A p ha N := by
  subst e
  rw [upperStarFactor_rfl, ← cancel_epi ((upperStarComp A (b ≫ c) p).hom.app N),
    reassoc_of% upperStarComp_hom_app_comp_upperStarComp_hom_app, upperStarInvariantHom,
    upperStarInvariantHom, upperStarInvariantHom, Functor.map_comp_assoc,
    ← Functor.map_comp_assoc (b)^*[A] ((upperStarComp A c p).hom.app N), Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
    ← reassoc_of% upperStarCongr_hom_app_comp_upperStarComp_hom_app' A b hc N,
    Iso.hom_inv_id_app_assoc]
  exact upperStarCongr_hom_app_trans_trans A _ _ _ _ N

/-- Two congruence isomorphisms of pullbacks compose to one; the composite equality is an
independent hypothesis. -/
@[reassoc]
lemma upperStarCongr_hom_app_trans_eq {P Q : Scheme.{u}} {x y z : P ⟶ Q} (h : x = y)
    (h' : y = z) (e : x = z) (N : Sheaf (Scheme.ProEt.topology Q) A) :
    (upperStarCongr A h).hom.app N ≫ (upperStarCongr A h').hom.app N =
      (upperStarCongr A e).hom.app N := by
  subst h h'
  simp [upperStarCongr]

/-- The composition isomorphism with the identity, followed by `𝟙^* ≅ 𝟭`, is the transport along
`t ≫ 𝟙 = t`. -/
@[reassoc]
lemma upperStarComp_id_right_hom_app_comp_map_upperStarId_hom_app {S Y : Scheme.{u}}
    (t : S ⟶ Y) (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarComp A t (𝟙 Y)).hom.app N ≫ (t)^*[A].map ((upperStarId A Y).hom.app N) =
      (upperStarCongr A (Category.comp_id t)).hom.app N := by
  rw [upperStarComp_id_right, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Iso.symm_hom, Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The transport of global sections along a square `τ ≫ x = x ≫ 𝟙` and `𝟙^* ≅ 𝟭` is the Galois
action `Γ(x^* N) ⟶ Γ(τ^* x^* N) ≅ Γ((τ ≫ x)^* N) = Γ(x^* N)`. -/
lemma globalSectionsTransport_upperStarId_hom_app {S Y : Scheme.{u}} {τ : S ⟶ S} {x : S ⟶ Y}
    (hY : τ ≫ x = x ≫ 𝟙 Y) (h : τ ≫ x = x) (N : Sheaf (Scheme.ProEt.topology Y) A) :
    globalSectionsTransport A hY ((upperStarId A Y).hom.app N) =
      (globalSectionsToUpperStar A τ).app ((x)^*[A].obj N) ≫
        (Sheaf.Γ _ A).map ((upperStarComp A τ x).inv.app N ≫ (upperStarCongr A h).hom.app N) := by
  rw [globalSectionsTransport, upperStarCompIso_hom_app, Category.assoc, Category.assoc,
    upperStarComp_id_right_hom_app_comp_map_upperStarId_hom_app,
    upperStarCongr_hom_app_trans_eq A hY (Category.comp_id x) h]

/-- The Galois action on global sections, written with the pullback of the underlying sheaf. -/
lemma galoisGlobalSections_eq {l : ℕ} [Fact l.Prime] {S X : Scheme.{u}} (σ : S ⟶ S) (x : S ⟶ X)
    (h : σ ≫ x = x) (H : AdicSheaf l X) :
    galoisGlobalSections σ x h H =
      (globalSectionsToUpperStar (WeilCoefficients.{u} l) σ).app
          ((x)^*[WeilCoefficients.{u} l].obj H.X) ≫
        (Sheaf.Γ _ (WeilCoefficients.{u} l)).map
          ((upperStarComp (WeilCoefficients.{u} l) σ x).inv.app H.X ≫
            (upperStarCongr (WeilCoefficients.{u} l) h).hom.app H.X) := by
  rw [galoisGlobalSections, Mod.comp_hom', adicUpperStarComp_inv_app_hom,
    adicUpperStarCongr_hom_app_hom]
  rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open ProEtale

/-- Endomorphisms of `ℚ̄_ℓ`-modules intertwined by an isomorphism have the same trace. -/
lemma WeilCoefficients.trace_toModuleCat_map_eq_of_comp_eq {l : ℕ} [Fact l.Prime]
    {V W : WeilCoefficients.{u} l} (E : V ≅ W) {T : V ⟶ V} {T' : W ⟶ W}
    (h : T ≫ E.hom = E.hom ≫ T') :
    LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map T).hom =
      LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map T').hom := by
  have hT' : T' = E.inv ≫ T ≫ E.hom := by rw [h, Iso.inv_hom_id_assoc]
  rw [hT', ← LinearMap.trace_conj' ((WeilCoefficients.toModuleCat l).map T).hom
    (WeilCoefficients.linearEquivOfIso E)]
  congr 1

/-- The `m`-th powers of the two forms `specGeometricFrobenius` and `geometricFrobeniusField` of the
geometric Frobenius `σ` of `Spec k̄` agree. -/
lemma specGeometricFrobenius_pow_hom_eq_geometricFrobeniusField_pow_hom (k : Type u) [Field k]
    [Finite k] (m : ℕ) :
    (specGeometricFrobenius k ^ m).hom = ((geometricFrobeniusField k).pow m).hom := by
  let := Fintype.ofFinite k
  have e : FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) =
      FiniteField.geometricFrobenius k (AlgebraicClosure k) := by
    ext x
    refine ((FiniteField.geometricFrobenius_eq_iff k (AlgebraicClosure k)).2 ?_).symm
    rw [Nat.card_eq_fintype_card, FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv,
      ← FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← AlgEquiv.mul_apply, mul_inv_cancel,
      AlgEquiv.one_apply]
  rw [specGeometricFrobenius_pow_hom, Iso.pow_hom_eq_pow,
    ProEtale.CondensedRing.geometricFrobeniusField_hom_pow, e]

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- **The iterated Weil structures of a sheaf pulled back from the model.** If an isomorphism
`e : F ≅ p^* H` of the underlying sheaves carries the Weil structure of `F` to the canonical
one `Fr^* p^* H ⟶ p^* H`, then it carries the iterated Weil structure `φ_m`, `m ≥ 1`, to the
canonical morphism `(Frᵐ)^* p^* H ⟶ p^* H`. -/
lemma frobeniusPowStr_comp_eq_of_iso (F : WeilSheaf k₀ l X) {H : AdicSheaf l X}
    (e : F.obj.carrier.X ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*[WeilCoefficients.{u} l].obj H.X)
    (hF : F.frobeniusStr ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
          e.hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H.X)
    (m : ℕ) (hm : 1 ≤ m) :
    F.frobeniusPowStr m ≫ e.hom =
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom)^*[
        WeilCoefficients.{u} l].map
          e.hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj _ m) H.X := by
  induction m, hm using Nat.le_induction with
  | base =>
    have p := congrArg Iso.hom (pow_one (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius)
    have n := (ProEtale.upperStarCongr (WeilCoefficients.{u} l) p).hom.naturality e.hom
    rw [frobeniusPowStr_one F p, Category.assoc, hF, ← reassoc_of% n,
      upperStarCongr_hom_app_comp_upperStarInvariantHom]
  | succ m hm ih =>
    have e' : (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).hom := by
      rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom]
    have n := (upperStarFactor (WeilCoefficients.{u} l) e').hom.naturality e.hom
    rw [Functor.comp_map] at n
    rw [← upperStarFactor_hom_app_comp_frobeniusPowStr_succ F m e', Category.assoc,
      Category.assoc, hF, ← Functor.map_comp_assoc, ih, Functor.map_comp_assoc,
      ← reassoc_of% n, upperStarFactor_hom_app_comp_upperStarInvariantHom]

/-- The compatibility of `e⁻¹ : p^* H ⟶ F` with the iterated Weil structure `φ_m` of `F` and the
identity structure `𝟙^* H ≅ H` of `H`, for `Frᵐ ≫ p = p ≫ 𝟙`. -/
lemma upperStarComp_hom_app_comp_map_inv_comp_frobeniusPowStr (F : WeilSheaf k₀ l X)
    {H : AdicSheaf l X}
    (e : F.obj.carrier.X ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*[WeilCoefficients.{u} l].obj H.X)
    (hF : F.frobeniusStr ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
          e.hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H.X)
    (m : ℕ) (hm : 1 ≤ m)
    (hc : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ 𝟙 X) :
    (ProEtale.upperStarComp (WeilCoefficients.{u} l)
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).hom.app H.X ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom)^*[
        WeilCoefficients.{u} l].map
          e.inv ≫ F.frobeniusPowStr m =
      (ProEtale.upperStarCongr (WeilCoefficients.{u} l) hc).hom.app H.X ≫
        (ProEtale.upperStarComp (WeilCoefficients.{u} l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj (𝟙 X)).hom.app H.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*[WeilCoefficients.{u} l].map
          ((ProEtale.upperStarId (WeilCoefficients.{u} l) X).hom.app H.X) ≫ e.inv := by
  have k := frobeniusPowStr_comp_eq_of_iso F e hF m hm
  have k' : (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom)^*[
      WeilCoefficients.{u} l].map e.inv ≫ F.frobeniusPowStr m =
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj _ m) H.X ≫
          e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, k, ← Functor.map_comp_assoc, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, e.inv_hom_id,
      Category.comp_id]
  rw [k', upperStarInvariantHom, Category.assoc, Iso.hom_inv_id_app_assoc,
    upperStarComp_id_right_hom_app_comp_map_upperStarId_hom_app_assoc,
    upperStarCongr_hom_app_trans_eq_assoc]

/-- **The trace function of a Weil sheaf pulled back from the model.** Let `e : F ≅ p^* H` be an
isomorphism of the underlying sheaves carrying the Weil structure of `F` to the canonical one
`Fr^* p^* H ⟶ p^* H`. At an `𝔽_{q^{n+1}}`-point `y` with geometric point `x̄`, the trace function
of `F` is the trace of the Galois action of `σ^{n+1}` on `Γ(Spec k̄, x̄^* H)`. -/
theorem traceFunction_eq_trace_galoisGlobalSections_of_iso (F : WeilSheaf k₀ l X)
    {H : AdicSheaf l X}
    (e : F.obj.carrier.X ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*[WeilCoefficients.{u} l].obj H.X)
    (hF : F.frobeniusStr ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
          e.hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H.X)
    (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)))
    {x : Spec (.of (AlgebraicClosure k₀)) ⟶ X}
    (hx : Spec.map (CommRingCat.ofHom
      (FiniteField.galoisExtension.liftAlgebraicClosure k₀ (n + 1)).toRingHom) ≫ y.1 = x)
    (h : ((geometricFrobeniusField k₀).pow (n + 1)).hom ≫ x = x) :
    F.traceFunction (n + 1) y =
      LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map
        (galoisGlobalSections ((geometricFrobeniusField k₀).pow (n + 1)).hom x h H)).hom := by
  have : Finite (FiniteField.galoisExtension k₀ (n + 1)) := Module.finite_of_finite k₀
  have hs := Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) (n + 1) IsAlgClosed.lift y
  have hστ := specGeometricFrobenius_pow_hom_eq_geometricFrobeniusField_pow_hom k₀ (n + 1)
  have hx' := (Scheme.Hom.geometricFiberPoint_comp_geometricFiberProj _ IsAlgClosed.lift y.1
    y.2).trans hx
  subst hx'
  have hY := h.trans (Category.comp_id _).symm
  have hc : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (n + 1)).hom ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ 𝟙 X :=
    (Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj _ (n + 1)).trans
      (Category.comp_id _).symm
  have comm := globalSectionsTransport_comm_of_upperStar (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (n + 1)).hom (𝟙 X) hc
    ((ProEtale.upperStarId (WeilCoefficients.{u} l) X).hom.app H.X) (F.frobeniusPowStr (n + 1))
    e.inv
    (upperStarComp_hom_app_comp_map_inv_comp_frobeniusPowStr F e hF (n + 1)
      (Nat.le_add_left 1 n) hc) (hστ ▸ hs.symm) hY
  have hiso : IsIso (globalSectionsTransport (WeilCoefficients.{u} l) (τ := (Iso.refl _).hom)
      (Category.id_comp ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint IsAlgClosed.lift
        y.1 y.2 ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)) e.inv) :=
    isIso_globalSectionsTransport _ (Iso.refl _) _ _
  rw [traceFunction, frobeniusEnd_stalkAt, globalSectionsTransport_congr_left _ _ hστ]
  refine Eq.trans (WeilCoefficients.trace_toModuleCat_map_eq_of_comp_eq
    (asIso (globalSectionsTransport (WeilCoefficients.{u} l) (τ := (Iso.refl _).hom)
      (Category.id_comp _) e.inv)) comm).symm ?_
  rw [globalSectionsTransport_upperStarId_hom_app _ hY h, galoisGlobalSections_eq]
  rfl

/-- The compatibility of an isomorphism `e : F ≅ p^* H` of `ℓ`-adic sheaves with the Weil
structures, read on the underlying sheaves. -/
lemma frobeniusStr_comp_forget_map_eq (F : WeilSheaf k₀ l X) {H : AdicSheaf l X}
    (e : F.obj.carrier ≅ ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H)
    (hF : (adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).hom.app F.obj.carrier ≫
          F.obj.str.hom ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*ᵃ[l].map e.hom ≫
        (adicUpperStarComp l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (CommRingCat.of k₀)))).hom.app H) :
    F.frobeniusStr ≫ ((AdicSheaf.forget _).mapIso e).hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
          ((AdicSheaf.forget _).mapIso e).hom ≫
        upperStarInvariantHom (WeilCoefficients.{u} l) _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H.X := by
  have k := congrArg Mod.Hom.hom hF
  rw [Mod.comp_hom', Mod.comp_hom', adicUpperStarIsoLowerStarInv_hom_app_hom, Mod.comp_hom',
    Mod.comp_hom', adicUpperStar_map_hom, adicUpperStarComp_inv_app_hom,
    adicUpperStarCongr_hom_app_hom] at k
  exact k

/-- `AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_galoisGlobalSections_of_iso` for an
isomorphism `e : F ≅ p^* H` of `ℓ`-adic sheaves compatible with the Weil structures. -/
theorem traceFunction_eq_trace_galoisGlobalSections_of_adicIso (F : WeilSheaf k₀ l X)
    {H : AdicSheaf l X}
    (e : F.obj.carrier ≅ ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H)
    (hF : (adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).hom.app F.obj.carrier ≫
          F.obj.str.hom ≫ e.hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*ᵃ[l].map e.hom ≫
        (adicUpperStarComp l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (CommRingCat.of k₀)))).hom.app H)
    (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)))
    {x : Spec (.of (AlgebraicClosure k₀)) ⟶ X}
    (hx : Spec.map (CommRingCat.ofHom
      (FiniteField.galoisExtension.liftAlgebraicClosure k₀ (n + 1)).toRingHom) ≫ y.1 = x)
    (h : ((geometricFrobeniusField k₀).pow (n + 1)).hom ≫ x = x) :
    F.traceFunction (n + 1) y =
      LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map
        (galoisGlobalSections ((geometricFrobeniusField k₀).pow (n + 1)).hom x h H)).hom :=
  traceFunction_eq_trace_galoisGlobalSections_of_iso F ((AdicSheaf.forget _).mapIso e)
    (frobeniusStr_comp_forget_map_eq F e hF) n y hx h

/-- The underlying `ℓ`-adic sheaf of the Weil sheaf `p^* H` pulled back from the model is
`p^* H`. -/
noncomputable def geometricFiberPullbackObjCarrierIso {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    (geometricFiberPullback (k₀ := k₀) hH).obj.carrier ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H :=
  Iso.refl _

/-- The Weil structure of `p^* H` is the canonical one, `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H`. -/
lemma geometricFiberPullback_str_hom_comp_carrierIso_hom {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    (adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).hom.app
          (geometricFiberPullback (k₀ := k₀) hH).obj.carrier ≫
        (geometricFiberPullback (k₀ := k₀) hH).obj.str.hom ≫
          (geometricFiberPullbackObjCarrierIso hH).hom =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*ᵃ[l].map
          (geometricFiberPullbackObjCarrierIso hH).hom ≫
        (adicUpperStarComp l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (CommRingCat.of k₀)))).hom.app H := by
  have hstr : (geometricFiberPullback (k₀ := k₀) hH).obj.str.hom =
      ((ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso k₀ l X).app H).hom := by
    rw [Endofunctor.IsoAlgebra.str_hom]
    rfl
  -- stated for a variable isomorphism `α`, so that the kernel does not unfold the concrete one
  have h {P Q : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (α : P ≅ Q) :
      α.hom.app (geometricFiberPullback (k₀ := k₀) hH).obj.carrier =
        α.hom.app (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H) := rfl
  rw [geometricFiberPullbackObjCarrierIso, Iso.refl_hom, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.id_comp, hstr, h]
  simp only [ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Iso.hom_inv_id_app_assoc]

/-- **The trace function of the Weil sheaf `p^* H` pulled back from the model**: at an
`𝔽_{q^{n+1}}`-point `y` with geometric point `x̄`, it is the trace of the Galois action of
`σ^{n+1}` on `Γ(Spec k̄, x̄^* H)`. -/
theorem traceFunction_geometricFiberPullback_eq_trace_galoisGlobalSections {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)))
    {x : Spec (.of (AlgebraicClosure k₀)) ⟶ X}
    (hx : Spec.map (CommRingCat.ofHom
      (FiniteField.galoisExtension.liftAlgebraicClosure k₀ (n + 1)).toRingHom) ≫ y.1 = x)
    (h : ((geometricFrobeniusField k₀).pow (n + 1)).hom ≫ x = x) :
    (geometricFiberPullback (k₀ := k₀) hH).traceFunction (n + 1) y =
      LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map
        (galoisGlobalSections ((geometricFrobeniusField k₀).pow (n + 1)).hom x h H)).hom :=
  traceFunction_eq_trace_galoisGlobalSections_of_adicIso _ (geometricFiberPullbackObjCarrierIso hH)
    (geometricFiberPullback_str_hom_comp_carrierIso_hom hH) n y hx h

end AlgebraicGeometry.WeilSheaf
