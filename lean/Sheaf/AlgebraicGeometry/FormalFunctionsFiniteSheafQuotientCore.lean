module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.IdealDataRecursivePowerComparison

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry

/-! The two residual finite-level identifications used by the main theorem. -/

/-- The canonical finite-level map is the base change of a quotient immersion.
Source: Stacks Project, Tag 02OD, finite fibre factorisation.
The finite fibre is obtained by pulling back the quotient
`Spec (A / m^(n+1)) → Spec A` along `X → Y`. The quotient map is
surjective, hence its affine morphism is a closed immersion. Stability of
closed immersions under pullback, together with the defining pullback
comparison for `formalFunctionsFiniteι`, gives the result.
(blueprint: lem-weil-pbc-formal-functions-finite-sheaf-quotient-closed) -/
theorem formalFunctionsFiniteι_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (n : ℕ) : IsClosedImmersion (formalFunctionsFiniteι f y n) := by
  have hp : IsPullback (pullback.fst (formalFibreBaseMap Y y n) f)
      (formalFunctionsFiniteι f y n)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formalFibreIdeal Y y n))))
      (pullback.fst (Y.fromSpecStalk y) f) := by
    apply ((IsPullback.of_hasPullback (Y.fromSpecStalk y) f).paste_vert_iff
      (by simp [formalFunctionsFiniteι])).mp
    simpa [formalFunctionsFiniteι, formalFibreBaseMap, formalFibreι] using
      (IsPullback.of_hasPullback (formalFibreBaseMap Y y n) f)
  apply MorphismProperty.of_isPullback hp
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_unit_factor {A B C : Scheme.{u}} (i : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (w : k = i ≫ g)
    (adjI : Scheme.Modules.tensorPullback i ⊣ Scheme.Modules.pushforward i)
    (F : C.Modules) :
    ∃ e : (Scheme.Modules.tensorPullback i).obj
        ((Scheme.Modules.tensorPullback g).obj F) ≅
          (Scheme.Modules.tensorPullback k).obj F,
      adjI.unit.app ((Scheme.Modules.tensorPullback g).obj F) ≫
          (Scheme.Modules.pushforward i).map e.hom =
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).homEquiv F
          _).symm
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app F ≫
            (Scheme.Modules.pushforwardCongr w).hom.app _ ≫
            (Scheme.Modules.pushforwardComp i g).inv.app _) := by
  let adjG := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let adjK := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  let r := Scheme.Modules.pushforwardCongr w ≪≫ (Scheme.Modules.pushforwardComp i g).symm
  let e := ((conjugateIsoEquiv adjK (adjG.comp adjI)).symm r).app F
  refine ⟨e, ?_⟩
  apply (adjG.homEquiv F _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_conjugateEquiv_symm adjK (adjG.comp adjI) r.hom F
  change adjG.unit.app F ≫ (Scheme.Modules.pushforward g).map
      (adjI.unit.app ((Scheme.Modules.tensorPullback g).obj F)) ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward i).map
          (((conjugateEquiv adjK (adjG.comp adjI)).symm r.hom).app F)) = _
  simpa only [r, Iso.trans_hom, NatTrans.comp_app, Functor.comp_map,
    Iso.symm_hom, Adjunction.comp_unit_app, Category.assoc] using hu.symm


set_option backward.isDefEq.respectTransparency false in
private theorem power_quotient_iso {B : Scheme.{u}} (J : B.IdealSheafData)
    (n : ℕ) (F : B.Modules) :
    ∃ e : formalModuleQuotient J n F ≅
        cokernel (Scheme.idealModuleProductι (J ^ n).toModulesι F),
      formalModuleQuotientπ J n F ≫ e.hom =
        cokernel.π (Scheme.idealModuleProductι (J ^ n).toModulesι F) := by
  obtain ⟨d, hd⟩ := (Scheme.Modules.idealData_recursive_power_comparison J n).2
  let e := d.symm
  have he : e.hom ≫ (J ^ n).toModulesι = (Scheme.idealSheafPower J.toModulesι n).2 := by
    rw [← hd]
    simp [e]
  let : MonoidalCategory B.Modules := SheafOfModules.monoidalCategory B.sheaf
  open MonoidalCategory in
  have hμ : (Scheme.idealSheafPower J.toModulesι n).2 ▷ F ≫ (λ_ F).hom =
      e.hom ▷ F ≫ ((J ^ n).toModulesι ▷ F ≫ (λ_ F).hom) := by
    rw [← Category.assoc, ← comp_whiskerRight, he]
  open MonoidalCategory in
  have hs : imageSubobject ((Scheme.idealSheafPower J.toModulesι n).2 ▷ F ≫ (λ_ F).hom) =
      imageSubobject ((J ^ n).toModulesι ▷ F ≫ (λ_ F).hom) := by
    calc
      _ = imageSubobject (e.hom ▷ F ≫ ((J ^ n).toModulesι ▷ F ≫ (λ_ F).hom)) :=
        congrArg (fun f ↦ imageSubobject f) hμ
      _ = _ := imageSubobject_iso_comp _ _
  let q := Subobject.isoOfMkEqMk _ _ hs
  have hq : q.hom ≫ Scheme.idealModuleProductι (J ^ n).toModulesι F =
      Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F := by
    simp [q, Scheme.idealModuleProductι]
  refine ⟨cokernel.mapIso _ _ q (Iso.refl F) (by simpa using hq.symm), ?_⟩
  simp [formalModuleQuotientπ, cokernel.mapIso]

private theorem ideal_quotient_congr {B : Scheme.{u}} (J K : B.IdealSheafData)
    (h : J = K) (F : B.Modules) :
    ∃ e : cokernel (Scheme.idealModuleProductι J.toModulesι F) ≅
        cokernel (Scheme.idealModuleProductι K.toModulesι F),
      cokernel.π (Scheme.idealModuleProductι J.toModulesι F) ≫ e.hom =
        cokernel.π (Scheme.idealModuleProductι K.toModulesι F) := by
  subst K
  exact ⟨Iso.refl _, by simp⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport the closed-immersion unit quotient to the canonical finite-level map.
Source: Stacks Project, Tags 02OD and 04CJ (1).
Apply `closedImmersion_unit_quotient` to the finite-level closed immersion.
The quotient-base-change ideal calculation identifies its kernel with the
extension of the `(n+1)`-st power of the maximal ideal; the product formula
identifies this with the ideal used by `formalModuleQuotient`. Finally, the
canonical tensor-pullback comparison identifies the resulting unit with
`formalFunctionsFiniteFMap`, yielding the displayed isomorphism and equation.
(blueprint: lem-weil-pbc-formal-functions-finite-sheaf-quotient-iso) -/
theorem formalFunctionsFinite_sheaf_quotient_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (y : Y) (n : ℕ) :
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap
          (pullback.fst (Y.fromSpecStalk y) f)
    ∃ e : formalModuleQuotient J (n + 1) F' ≅
        (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F),
      formalModuleQuotientπ J (n + 1) F' ≫ e.hom =
        formalFunctionsFiniteFMap f y F n := by
  classical
  dsimp only
  let p := pullback.fst (Y.fromSpecStalk y) f
  let g := pullback.snd (Y.fromSpecStalk y) f
  let i := formalFunctionsFiniteι f y n
  let F' := (Scheme.Modules.tensorPullback g).obj F
  let J := (Scheme.IdealSheafData.ofIdealTop
    ((maximalIdeal (Y.presheaf.stalk y)).map
      (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap p
  have hp : IsPullback (pullback.fst (formalFibreBaseMap Y y n) f) i
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formalFibreIdeal Y y n)))) p := by
    apply ((IsPullback.of_hasPullback (Y.fromSpecStalk y) f).paste_vert_iff
      (by simp [i, formalFunctionsFiniteι])).mp
    simpa [i, p, formalFunctionsFiniteι, formalFibreBaseMap, formalFibreι] using
      (IsPullback.of_hasPullback (formalFibreBaseMap Y y n) f)
  have hk : i.ker = J ^ (n + 1) := by
    rw [← hp.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
    rw [(quotientBaseChange_closedImmersion_ideal p (formalFibreIdeal Y y n)).2.1]
    exact ((quotientBaseChange_extendedIdeal_mul_pow p).2
      (maximalIdeal (Y.presheaf.stalk y)) (n + 1) (by omega)).symm
  have : IsClosedImmersion i := formalFunctionsFiniteι_isClosedImmersion f y n
  obtain ⟨a, ha⟩ := power_quotient_iso J (n + 1) F'
  obtain ⟨d, hd⟩ := ideal_quotient_congr (J ^ (n + 1)) i.ker hk.symm F'
  obtain ⟨η, hη, _⟩ := Scheme.Modules.closedImmersion_unit_quotient i
  have hη' := hη F'
  have : IsIso (η F') := hη'.2.2.2
  let b := asIso (η F')
  have hb : cokernel.π (Scheme.idealModuleProductι i.ker.toModulesι F') ≫ b.hom =
      (Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)).unit.app F' :=
    hη'.2.2.1
  obtain ⟨c, hc⟩ := tensor_unit_factor i g (formalFibreι f y n)
    (formalFunctionsFiniteι_snd f y n).symm
    (Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)) F
  refine ⟨a ≪≫ d ≪≫ b ≪≫ (Scheme.Modules.pushforward i).mapIso c, ?_⟩
  change formalModuleQuotientπ J (n + 1) F' ≫
    a.hom ≫ d.hom ≫ b.hom ≫ (Scheme.Modules.pushforward i).map c.hom = _
  rw [← Category.assoc, ha]
  rw [← Category.assoc, hd]
  rw [← Category.assoc, hb]
  exact hc

end AlgebraicGeometry
