module

public import Sheaf.Paper.LisseCompletedSystemComparison
public import Sheaf.Paper.EtaleLocalMonodromyRealization
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.Paper.IntegralRepresentationRationalization
import Sheaf.Paper.FiniteFibreLinearLifting
import Sheaf.Paper.LatticeNormalizationRationalExact
import Sheaf.Paper.CompletedNormalizationRecovery
import Sheaf.Paper.FibreFunctorLinearTransport
import WeilConjectures.AlgebraicGeometry.GaloisPointGeometricComparison

/-! # Integral fibre monodromy reconstruction

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Corollary 6.8.5, pp. 59--60,
and Lemma 7.4.7, p. 70 (blueprint: lem-a1-integral-fibre-monodromy-reconstruction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
open ProEtale.CompletedLisse
variable (l : ℕ) [Fact l.Prime] (P : Base.{u} l) (p : SfMonodromyPoint P.X)

/-- The actual stalk diagram of the specified normalized tower.
Source: BS 6.8.4(1) (blueprint: lem-a1-integral-fibre-monodromy-reconstruction). -/
abbrev a1IntegralFibreDiagram (C : Comparison l P) (M : Integral l P) :=
  (C.equivalence.functor.obj M).obj.obj ⋙
    (pointSmallEtale p.point).sheafFiber (A := ModuleCat.{u + 1} (Integers l P))

/-- Compatible tuples in the stalk tower, the concrete module inverse limit.
Source: BS 6.8.4(1) (blueprint: lem-a1-integral-fibre-monodromy-reconstruction). -/
abbrev a1IntegralFibre (C : Comparison l P) (M : Integral l P) :=
  ModuleCat.sectionsSubmodule (a1IntegralFibreDiagram l P p C M)

/-- The canonical coordinate projection of the concrete inverse limit.
Source: BS 6.8.4(1) (blueprint: lem-a1-integral-fibre-monodromy-reconstruction). -/
def a1IntegralFibreProjection (C : Comparison l P) (M : Integral l P) (n : ℕ) :=
  (LinearMap.proj (op n)).comp (a1IntegralFibre l P p C M).subtype

/-- The n-th normalized etale reduction, as a module over the valuation ring.
Source: BS 6.8.4(1) (blueprint: lem-a1-integral-fibre-monodromy-reconstruction). -/
abbrev a1IntegralEtaleTower (C : Comparison l P) (M : Integral l P) :=
  (C.equivalence.functor.obj M).obj.obj

/-- The inverse-limit topology: compatible tuples in the product of discrete stalks.
Source: BS 6.8.4(1) (blueprint: lem-a1-integral-fibre-monodromy-reconstruction). -/
abbrev a1IntegralFibreTopology (C : Comparison l P) (M : Integral l P) :
    TopologicalSpace (a1IntegralFibre l P p C M) :=
  TopologicalSpace.induced (fun x : a1IntegralFibre l P p C M ↦ x.val)
    (@Pi.topologicalSpace _ (fun j ↦ (a1IntegralFibreDiagram l P p C M).obj j)
      (fun _ ↦ ⊥))

/-- The rational fibre is the actual balanced tensor extension E tensor_A Lambda.
Source: BS 6.8.4(4) (blueprint: lem-a1-integral-fibre-monodromy-reconstruction). -/
abbrev a1RationalFibre (C : Comparison l P) (M : Integral l P) :=
  (ModuleCat.extendScalars (Integers l P).subtype).obj
    (ModuleCat.of (Integers l P) (a1IntegralFibre l P p C M))

/-- The canonical inclusion into the rational fibre, x maps to 1 tensor x.
Source: BS 6.8.4(4) (blueprint: lem-a1-integral-fibre-monodromy-reconstruction). -/
abbrev a1RationalFibreUnit (C : Comparison l P) (M : Integral l P) :=
  (ModuleCat.ExtendRestrictScalarsAdj.unit.{u + 1, u + 1, u + 1}
      (Integers l P).subtype).app
    (ModuleCat.of (Integers l P) (a1IntegralFibre l P p C M))

private theorem system_stalk_finite (F : Systems l P) (n : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ P.X) :
    Finite (((pointSmallEtale y).sheafFiber
      (A := ModuleCat.{u + 1} (Integers l P))).obj (F.obj.obj.obj (op n))) := by
  obtain ⟨r, ⟨e⟩⟩ := F.property n Ω y
  let : Finite (Padic.coefficientExtensionRing l P.E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l P.E (n + 1) (by omega)
  let eu := ((pointSmallEtale y).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} (Integers l P))).app (F.obj.obj.obj (op n))
  exact Finite.of_equiv _ (eu.symm.toLinearEquiv.trans e).toEquiv.symm

private theorem system_level_lisse (F : Systems l P) (n : ℕ) :
    IsLisseModuleSheaf (F.obj.obj.obj (op n)) := by
  apply isLisseModuleSheaf_of_locallyConstant_of_finite_stalk
    (Integers l P) _ ((F.obj.property.1 n).toIsLocallyConstantSheaf)
  intro Ω _ _ y
  have := system_stalk_finite l P F n y
  exact Finite.of_equiv _ (((pointSmallEtale y).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} (Integers l P))).app (F.obj.obj.obj (op n))).toLinearEquiv.toEquiv.symm

private theorem fibre_killed (C : Comparison l P) (M : Integral l P) (n : ℕ) :
    Padic.coefficientExtensionIdeal l P.E (n + 1) •
      (⊤ : Submodule (Integers l P) ((a1IntegralFibreDiagram l P p C M).obj (op n))) = ⊥ := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} (Integers l P))) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x _
  obtain ⟨U, ξ, s, rfl⟩ := (pointSmallEtale p.point).toPresheafFiber_jointly_surjective
    (P := ((a1IntegralEtaleTower l P C M).obj (op n)).obj) x
  have hkill : a • s = 0 := by
    have hm := Submodule.smul_mem_smul ha
      (show s ∈ (⊤ : Submodule (Integers l P) _) from Submodule.mem_top)
    have hk := (C.equivalence.functor.obj M).obj.property.2.1 n U
    change Padic.coefficientExtensionIdeal l P.E (n + 1) •
      (⊤ : Submodule (Integers l P) _) = ⊥ at hk
    change a • s ∈ _ at hm
    rw [hk, Submodule.mem_bot] at hm
    exact hm
  change a • ((pointSmallEtale p.point).toPresheafFiber U ξ
    ((a1IntegralEtaleTower l P C M).obj (op n)).obj).hom s = 0
  rw [← map_smul, hkill, map_zero]

private theorem fibre_transition (C : Comparison l P) (M : Integral l P) (n : ℕ) :
    Function.Surjective
      ((a1IntegralFibreDiagram l P p C M).map (homOfLE (Nat.le_succ n)).op) ∧
    LinearMap.ker
      ((a1IntegralFibreDiagram l P p C M).map (homOfLE (Nat.le_succ n)).op).hom =
      Padic.coefficientExtensionIdeal l P.E (n + 1) •
        (⊤ : Submodule (Integers l P)
          ((a1IntegralFibreDiagram l P p C M).obj (op (n + 1)))) := by
  let F := (C.equivalence.functor.obj M).obj
  let e := (pointSmallEtale p.point).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} (Integers l P))
  obtain ⟨hs, hk⟩ := F.property.2.2 p.Ω p.point n
  have hn := e.hom.naturality (F.obj.map (homOfLE (Nat.le_succ n)).op)
  constructor
  · intro x
    obtain ⟨y, hy⟩ := hs ((e.app (F.obj.obj (op n))).inv x)
    refine ⟨(e.app (F.obj.obj (op (n + 1)))).hom y, ?_⟩
    have h := ConcreteCategory.congr_hom hn y
    simp only [ModuleCat.comp_apply] at h
    rw [hy] at h
    exact h.symm.trans ((e.app (F.obj.obj (op n))).toLinearEquiv.apply_symm_apply x)
  · apply Submodule.comap_injective_of_surjective
      (e.app (F.obj.obj (op (n + 1)))).toLinearEquiv.surjective
    rw [← LinearMap.ker_comp]
    have heq := congrArg ModuleCat.Hom.hom hn
    change _ = ((a1IntegralFibreDiagram l P p C M).map
      (homOfLE (Nat.le_succ n)).op).hom.comp
        (e.app (F.obj.obj (op (n + 1)))).hom.hom at heq
    change (ModuleCat.Hom.hom ((a1IntegralFibreDiagram l P p C M).map
      (homOfLE (Nat.le_succ n)).op) |>.comp
        (e.app (F.obj.obj (op (n + 1)))).hom.hom).ker = _
    rw [← heq]
    change LinearMap.ker ((e.app (F.obj.obj (op n))).hom.hom.comp
      ((pointSmallEtale p.point).ulift.{u + 1}.sheafFiber.map
        (F.obj.map (homOfLE (Nat.le_succ n)).op)).hom) = _
    have hek : LinearMap.ker (e.app (F.obj.obj (op n))).hom.hom = ⊥ :=
      LinearMap.ker_eq_bot.mpr (e.app (F.obj.obj (op n))).toLinearEquiv.injective
    rw [LinearMap.ker_comp_of_ker_eq_bot _ hek]
    rw [Submodule.comap_smul_top_of_surjective _ _
      (e.app (F.obj.obj (op (n + 1)))).toLinearEquiv.surjective]
    change _ = _ ⊔ (LinearMap.ker (e.app (F.obj.obj (op (n + 1)))).hom.hom)
    rw [show LinearMap.ker (e.app (F.obj.obj (op (n + 1)))).hom.hom = ⊥ from
      LinearMap.ker_eq_bot.mpr (e.app (F.obj.obj (op (n + 1)))).toLinearEquiv.injective,
      sup_bot_eq]
    exact hk

private def level_loop (J : SfMonodromyRealization l P.E p)
    (F : LisseModuleSheafCategory P.X (Integers l P)) (g : p.group) :
    Aut (((pointSmallEtale p.point).sheafFiber
      (A := ModuleCat.{u + 1} (Integers l P))).obj F.obj) :=
  let e := ((pointSmallEtale p.point).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} (Integers l P))).app F.obj
  e.symm ≪≫ ((lisseLinearFibrePathFamily P.X (Integers l P)).map
    p.point p.point (J.finiteCorrespondence.γ g)).app F ≪≫ e

private def level_rep (J : SfMonodromyRealization l P.E p)
    (F : LisseModuleSheafCategory P.X (Integers l P)) :
    Representation (Integers l P) p.group
      (((pointSmallEtale p.point).sheafFiber
        (A := ModuleCat.{u + 1} (Integers l P))).obj F.obj) where
  toFun g := (level_loop l P p J F g).hom.hom
  map_one' := by
    simp only [level_loop, map_one]
    have hi := (lisseLinearFibrePathFamily P.X (Integers l P)).identity p.point
    change (lisseLinearFibrePathFamily P.X (Integers l P)).map p.point p.point
      (1 : Aut (flcFiber p.point)) = _ at hi
    rw [hi]
    ext x
    simp
  map_mul' g h := by
    have hm := (lisseLinearFibrePathFamily P.X (Integers l P)).composition
      p.point p.point p.point (J.finiteCorrespondence.γ h) (J.finiteCorrespondence.γ g)
    have hg : J.finiteCorrespondence.γ (g * h) =
        J.finiteCorrespondence.γ h ≪≫ J.finiteCorrespondence.γ g := map_mul _ _ _
    ext x
    simp only [level_loop, hg]
    rw [hm]
    simp

private theorem fibre_to_set_comparison
    (F : Sheaf P.X.smallEtaleTopology (ModuleCat.{u + 1} (Integers l P)))
    (x : ((pointSmallEtale p.point).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Integers l P))).obj F) :
    sfModuleFiberToSet l P.E p F
      ((((pointSmallEtale p.point).uliftSheafFiberIso.{u + 1}
        (ModuleCat.{u + 1} (Integers l P))).app F).hom x) =
      pathUnderlyingStalk p.point (Integers l P) F x := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} (Integers l P))) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  obtain ⟨U, ⟨ξ⟩, s, rfl⟩ :=
    ((pointSmallEtale p.point).ulift.{u + 1}).toPresheafFiber_jointly_surjective
      (P := F.obj) x
  rw [pathUnderlyingStalk_germ]
  have hu := ConcreteCategory.congr_hom
    ((pointSmallEtale p.point).toPresheafFiber_uliftSheafFiberIso_hom_app
      (ModuleCat.{u + 1} (Integers l P)) F U ξ) s
  change _ = ((pointSmallEtale p.point).toPresheafFiber U ξ F.obj).hom s at hu
  simp only [ModuleCat.comp_apply] at hu
  erw [hu]
  let e := ((pointSmallEtale p.point).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} (Integers l P)))).app F
  apply e.toEquiv.injective
  change e.hom (e.inv _) = _
  erw [Iso.inv_hom_id_apply]
  exact (ConcreteCategory.congr_hom
    ((pointSmallEtale p.point).toPresheafFiber_presheafFiberCompIso_hom_app
      (CategoryTheory.forget (ModuleCat.{u + 1} (Integers l P))) U ξ F.obj) s).symm

private theorem level_rep_evaluation (J : SfMonodromyRealization l P.E p)
    (F : LisseModuleSheafCategory P.X (Integers l P)) :
    ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf (Integers l P) F.obj),
      ∀ (g : p.group) (x : ((pointSmallEtale p.point).sheafFiber
          (A := ModuleCat.{u + 1} (Integers l P))).obj F.obj),
        sfModuleFiberToSet l P.E p F.obj (level_rep l P p J F g x) =
          (J.finiteCorrespondence.γ g).hom.app
            (galoisUnderlyingFLC (Integers l P) F.obj h)
              (sfModuleFiberToSet l P.E p F.obj x) := by
  obtain ⟨h, _⟩ := lisseLinearFibrePathFamily_evaluation (Integers l P)
    p.point p.point (J.finiteCorrespondence.γ 1) F
  refine ⟨h, fun g x ↦ ?_⟩
  let e := ((pointSmallEtale p.point).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} (Integers l P))).app F.obj
  obtain ⟨_, he⟩ := lisseLinearFibrePathFamily_evaluation (Integers l P)
    p.point p.point (J.finiteCorrespondence.γ g) F
  have hx : x = e.hom (e.inv x) := (e.toLinearEquiv.apply_symm_apply x).symm
  conv_rhs => rw [hx, fibre_to_set_comparison]
  change sfModuleFiberToSet l P.E p F.obj
    (e.hom (((lisseLinearFibrePathFamily P.X (Integers l P)).map
      p.point p.point (J.finiteCorrespondence.γ g)).hom.app F (e.inv x))) = _
  rw [fibre_to_set_comparison]
  exact he (e.inv x)

private theorem level_rep_continuous (J : SfMonodromyRealization l P.E p)
    (F : LisseModuleSheafCategory P.X (Integers l P)) :
    @Continuous _ _ (@instTopologicalSpaceProd _ _ inferInstance ⊥) ⊥
      (fun z : p.group × ((pointSmallEtale p.point).sheafFiber
        (A := ModuleCat.{u + 1} (Integers l P))).obj F.obj ↦
          level_rep l P p J F z.1 z.2) := by
  let T := ((pointSmallEtale p.point).sheafFiber
    (A := ModuleCat.{u + 1} (Integers l P))).obj F.obj
  let : TopologicalSpace T := ⊥
  let : DiscreteTopology T := ⟨rfl⟩
  obtain ⟨h, he⟩ := level_rep_evaluation l P p J F
  let X := galoisUnderlyingFLC (Integers l P) F.obj h
  let S := (flcFiber p.point).obj X
  let : TopologicalSpace S := ⊥
  let : DiscreteTopology S := ⟨rfl⟩
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} (Integers l P))) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  let k := ((pointSmallEtale p.point).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} (Integers l P)))).symm.app F.obj
  apply continuous_prod_of_discrete_right.mpr
  intro x
  let : TopologicalSpace (Aut S) := SetFunctorAut.fiberTopology S
  have hce : Continuous (fun g : p.group ↦
      (show Aut S from (J.finiteCorrespondence.γ g).app X)) :=
    (continuous_apply X).comp
      (continuous_induced_dom.comp J.finiteCorrespondence.γ.continuous)
  have hcf : Continuous (fun σ : Aut S ↦ (σ.hom : S → S)) := continuous_induced_dom
  have hc : Continuous (fun g : p.group ↦
      (J.finiteCorrespondence.γ g).hom.app X (k.hom x)) :=
    (continuous_apply (k.hom x)).comp (hcf.comp hce)
  have heq : (fun g : p.group ↦ level_rep l P p J F g x) =
      fun g ↦ k.inv ((J.finiteCorrespondence.γ g).hom.app X (k.hom x)) := by
    funext g
    apply k.toEquiv.injective
    exact (he g x).trans (k.toEquiv.apply_symm_apply _).symm
  rw [heq]
  exact continuous_of_discreteTopology.comp hc

private theorem level_rep_natural (J : SfMonodromyRealization l P.E p)
    (F H : LisseModuleSheafCategory P.X (Integers l P)) (f : F ⟶ H)
    (g : p.group) (x : ((pointSmallEtale p.point).sheafFiber
      (A := ModuleCat.{u + 1} (Integers l P))).obj F.obj) :
    ((pointSmallEtale p.point).sheafFiber.map f.hom) (level_rep l P p J F g x) =
      level_rep l P p J H g (((pointSmallEtale p.point).sheafFiber.map f.hom) x) := by
  let e := Functor.isoWhiskerLeft (ObjectProperty.ι
    (IsLisseModuleSheaf (Y := P.X) (Λ := Integers l P)))
      ((pointSmallEtale p.point).uliftSheafFiberIso.{u + 1}
        (ModuleCat.{u + 1} (Integers l P)))
  let t := e.symm ≪≫ (lisseLinearFibrePathFamily P.X (Integers l P)).map
    p.point p.point (J.finiteCorrespondence.γ g) ≪≫ e
  exact (ConcreteCategory.congr_hom (t.hom.naturality f) x).symm

private def limit_rep (C : Comparison l P) (M : Integral l P)
    (r : ∀ n : ℕ, Representation (Integers l P) p.group
      ((a1IntegralFibreDiagram l P p C M).obj (op n)))
    (ht : ∀ (n m : ℕ) (h : m ≤ n) (g : p.group)
      (x : (a1IntegralFibreDiagram l P p C M).obj (op n)),
      (a1IntegralFibreDiagram l P p C M).map (homOfLE h).op (r n g x) =
        r m g ((a1IntegralFibreDiagram l P p C M).map (homOfLE h).op x)) :
    Representation (Integers l P) p.group (a1IntegralFibre l P p C M) where
  toFun g :=
    { toFun x := ⟨fun j ↦ r j.unop g (x.val j), by
        intro i j f
        have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        change (a1IntegralFibreDiagram l P p C M).map f (r i.unop g (x.val i)) = _
        rw [hf, ht]
        exact congrArg (r j.unop g) (x.property (homOfLE (leOfHom f.unop)).op)⟩
      map_add' x y := by ext j; exact map_add (r j.unop g) _ _
      map_smul' a x := by ext j; exact (r j.unop g).map_smul a _ }
  map_one' := by
    ext x j
    exact LinearMap.congr_fun (r j.unop).map_one (x.val j)
  map_mul' g h := by
    ext x j
    exact LinearMap.congr_fun ((r j.unop).map_mul g h) (x.val j)

private theorem limit_rep_continuous (C : Comparison l P) (M : Integral l P)
    (r : ∀ n : ℕ, Representation (Integers l P) p.group
      ((a1IntegralFibreDiagram l P p C M).obj (op n)))
    (ht : ∀ (n m : ℕ) (h : m ≤ n) (g : p.group)
      (x : (a1IntegralFibreDiagram l P p C M).obj (op n)),
      (a1IntegralFibreDiagram l P p C M).map (homOfLE h).op (r n g x) =
        r m g ((a1IntegralFibreDiagram l P p C M).map (homOfLE h).op x))
    (hc : ∀ n : ℕ, @Continuous _ _ (@instTopologicalSpaceProd _ _ inferInstance ⊥) ⊥
      (fun z : p.group × (a1IntegralFibreDiagram l P p C M).obj (op n) ↦ r n z.1 z.2)) :
    @Continuous _ _
      (@instTopologicalSpaceProd _ _ inferInstance (a1IntegralFibreTopology l P p C M))
      (a1IntegralFibreTopology l P p C M)
      (fun z : p.group × a1IntegralFibre l P p C M ↦
        limit_rep l P p C M r ht z.1 z.2) := by
  let : ∀ j : ℕᵒᵖ, TopologicalSpace ((a1IntegralFibreDiagram l P p C M).obj j) := fun _ ↦ ⊥
  let : TopologicalSpace (a1IntegralFibre l P p C M) := a1IntegralFibreTopology l P p C M
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro j
  have hv : Continuous (fun x : a1IntegralFibre l P p C M ↦ x.val) :=
    continuous_induced_dom
  exact (hc j.unop).comp (continuous_fst.prodMk
    (((continuous_apply j).comp hv).comp continuous_snd))

private theorem quotient_cancel_uniformizer
    {R : Type*} [CommRing R] [IsDomain R] (π : R) (hπ : π ≠ 0)
    (n : ℕ) (a : R ⧸ (Ideal.span ({π} : Set R) ^ (n + 2)))
    (ha : π • a = 0) :
    a ∈ (Ideal.span ({π} : Set R) ^ (n + 1)) •
      (⊤ : Submodule R (R ⧸ (Ideal.span ({π} : Set R) ^ (n + 2)))) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hmem : π * a ∈ Ideal.span ({π} : Set R) ^ (n + 2) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact ha
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨b, hb⟩ := hmem
  have hab : a = π ^ (n + 1) * b := by
    apply mul_left_cancel₀ hπ
    calc
      π * a = π ^ (n + 2) * b := hb
      _ = π * (π ^ (n + 1) * b) := by rw [pow_succ']; ring
  rw [hab]
  exact Submodule.smul_mem_smul
    (by rw [Ideal.span_singleton_pow]; exact Ideal.subset_span (Set.mem_singleton _))
      (show Ideal.Quotient.mk _ b ∈ (⊤ : Submodule R _) from Submodule.mem_top)

private theorem fibre_free (C : Comparison l P) (M : Integral l P)
    [Module.Finite (Integers l P) (a1IntegralFibre l P p C M)] :
    Module.Free (Integers l P) (a1IntegralFibre l P p C M) := by
  let R := Integers l P
  let π := Padic.coefficientExtensionUniformizer l P.E
  have h := (Padic.extension_integers_dvr l P.E
    (Padic.coefficientExtensionAbsoluteValue l P.E)
    (spectralNorm_extends (K := ℚ_[l]) (L := P.E))).choose_spec.choose_spec
  let : IsDiscreteValuationRing R := h.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({π} : Set R) = Padic.coefficientExtensionMaximalIdeal l P.E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmax : Padic.coefficientExtensionMaximalIdeal l P.E = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr (hgen.trans hmax).symm
  have hinj (x : a1IntegralFibre l P p C M) (hx : π • x = 0) : x = 0 := by
    apply Subtype.ext
    funext j
    let n := j.unop
    obtain ⟨d, ⟨e⟩⟩ := (C.equivalence.functor.obj M).property (n + 1) p.Ω p.point
    let eu := ((pointSmallEtale p.point).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} R)).app ((a1IntegralEtaleTower l P C M).obj (op (n + 1)))
    let e' := eu.symm.toLinearEquiv.trans e
    have hz : π • e' (x.val (op (n + 1))) = 0 := by
      rw [← e'.map_smul]
      have hh := congrArg (fun z : a1IntegralFibre l P p C M ↦ z.val (op (n + 1))) hx
      exact congrArg e' hh |>.trans e'.map_zero
    have hcoords (i : Fin d) : e' (x.val (op (n + 1))) i ∈
        (Ideal.span ({π} : Set R) ^ (n + 1)) •
          (⊤ : Submodule R (Padic.coefficientExtensionRing l P.E (n + 2))) :=
      quotient_cancel_uniformizer π hirr.ne_zero n _ (congrFun hz i)
    have hwhole : e' (x.val (op (n + 1))) ∈
        (Ideal.span ({π} : Set R) ^ (n + 1)) • (⊤ : Submodule R _) := by
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
      apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      choose y hy using fun i ↦ (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
        (by simpa only [Ideal.span_singleton_pow,
          Submodule.ideal_span_singleton_smul] using hcoords i)
      exact ⟨y, Submodule.mem_top, funext fun i ↦ (hy i).2⟩
    have hm : x.val (op (n + 1)) ∈ Padic.coefficientExtensionIdeal l P.E (n + 1) •
        (⊤ : Submodule R _) := by
      have he := Submodule.mem_map_of_mem (f := e'.symm.toLinearMap) hwhole
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr e'.symm.surjective] at he
      change e'.symm (e' (x.val (op (n + 1)))) ∈
        (Ideal.span ({π} : Set R) ^ (n + 1)) • (⊤ : Submodule R _) at he
      rw [e'.symm_apply_apply] at he
      exact he
    have hk := (fibre_transition l P p C M n).2
    have hz' := LinearMap.mem_ker.mp (hk.symm ▸ hm)
    exact (x.property (homOfLE (Nat.le_succ n)).op).symm.trans hz'
  have hp (n : ℕ) (x : a1IntegralFibre l P p C M) : π ^ n • x = 0 → x = 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro hx
      rw [pow_succ', mul_smul] at hx
      exact ih (hinj _ hx)
  have : Module.IsTorsionFree R (a1IntegralFibre l P p C M) :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr (by
      intro a x hx
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hirr
        apply hp n x
        rw [mul_smul] at hx
        exact (smul_eq_zero_iff_eq u).mp hx)
  exact Module.free_of_finite_type_torsion_free'

private theorem quotient_stalk_equiv (C : Comparison l P) (M : Integral l P)
    (V : SfContinuousRepresentations l P.E p) (B : SfInvariantLattice l P.E V)
    (i : a1IntegralFibre l P p C M ≃ₗ[Integers l P] B.submodule)
    (hp : ∀ n : ℕ, Function.Surjective (a1IntegralFibreProjection l P p C M n) ∧
      LinearMap.ker (a1IntegralFibreProjection l P p C M n) =
        Padic.coefficientExtensionIdeal l P.E (n + 1) •
          (⊤ : Submodule (Integers l P) (a1IntegralFibre l P p C M))) :
    ∃ q : ∀ n : ℕ, (a1IntegralFibreDiagram l P p C M).obj (op n) ≃ₗ[Integers l P]
        sfLatticeQuotient l P.E B n,
      ∀ n x, q n (a1IntegralFibreProjection l P p C M n x) =
        sfLatticeQuotientMk l P.E B n (i x) := by
  let q := fun n ↦ ((a1IntegralFibreProjection l P p C M n).quotKerEquivOfSurjective
    (hp n).1).symm |>.trans
      ((Submodule.quotEquivOfEq _ _ (hp n).2).trans
        (Submodule.Quotient.equiv _ _ i (by
          rw [Submodule.map_smul'', Submodule.map_top,
            LinearMap.range_eq_top.mpr i.surjective])))
  refine ⟨q, ?_⟩
  intro n x
  simp [q, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk, sfLatticeQuotientMk]

/-- Integral fibre reconstruction with recovery under the specified normalized realization.
Source: BS 6.8.4(1),(4), Corollary 6.8.5, pp. 59--60, and Lemma 7.4.7, p. 70
(blueprint: lem-a1-integral-fibre-monodromy-reconstruction).

Proof: (1) Evaluate the normalized finite-free etale tower at the geometric point.
The finite correspondence cor-galois-lisse-representations supplies the evaluation
monodromy and equivariant quotient transitions. (2) Apply
lem-pod-adic-limit-finite-modules to obtain finite generation, the canonical quotient
maps and equality of limit and adic topologies. Define the action on compatible tuples
coordinatewise. (3) If varpi x = 0, the (n+1)-st free quotient coordinate is divisible by
varpi^n and hence its n-th image vanishes. Thus the limit is torsion-free; DVR
factorization from lem-weil-l-adic-extension-integers-dvr and
lem-sc-dvr-fg-torsionfree-free give freeness, also at rank zero. (4) Each coordinate
of the joint action is continuous, so the joint limit action is continuous.
(5) In a finite basis the map to E tensor_A Lambda is A^d into E^d and is injective.
The open sets varpi^(-r) Lambda cover the rational fibre; continuity on each follows
by scalar conjugation from integral joint continuity. (6) Full faithfulness of the
finite correspondence lifts the quotient fibre identifications to sheaf isomorphisms;
faithfulness makes every transition square commute. (7) Apply the stipulated
simultaneous normalization of this same J to the resulting actual stable lattice.
The diagram isomorphism identifies its integral limit with M by
lem-per-lisse-completed-system-comparison. The coefficient identifications of
lem-sfb-integral-lisse-reduction-equivalence and l = unit times varpi^e identify the
localizations, giving the asserted lisse rational-module isomorphism. -/
theorem integral_fibre_monodromy_reconstruction
    (C : Comparison l P) (J : SfMonodromyRealization l P.E p) (M : Integral l P) :
    ∃ (hflc : ∀ n : ℕ, IsLisseEtaleSheafOfSets
        (galoisUnderlyingSetSheaf (Integers l P) ((a1IntegralEtaleTower l P C M).obj (op n))))
      (r : ∀ n : ℕ, Representation (Integers l P) p.group
        ((a1IntegralFibreDiagram l P p C M).obj (op n)))
      (rho : Representation (Integers l P) p.group (a1IntegralFibre l P p C M)),
      (∀ (n : ℕ) (g : p.group) (x : (a1IntegralFibreDiagram l P p C M).obj (op n)),
        sfModuleFiberToSet l P.E p ((a1IntegralEtaleTower l P C M).obj (op n)) (r n g x) =
          (J.finiteCorrespondence.γ g).hom.app
            (galoisUnderlyingFLC (Integers l P)
              ((a1IntegralEtaleTower l P C M).obj (op n)) (hflc n))
            (sfModuleFiberToSet l P.E p ((a1IntegralEtaleTower l P C M).obj (op n)) x)) ∧
      (∀ n : ℕ, Finite ((a1IntegralFibreDiagram l P p C M).obj (op n)) ∧
        @Continuous _ _ (@instTopologicalSpaceProd _ _ inferInstance ⊥) ⊥
          (fun z : p.group × (a1IntegralFibreDiagram l P p C M).obj (op n) ↦ r n z.1 z.2)) ∧
      (∀ (n m : ℕ) (h : m ≤ n) (g : p.group)
          (x : (a1IntegralFibreDiagram l P p C M).obj (op n)),
        (a1IntegralFibreDiagram l P p C M).map (homOfLE h).op (r n g x) =
          r m g ((a1IntegralFibreDiagram l P p C M).map (homOfLE h).op x)) ∧
      (∀ n : ℕ, Function.Surjective
          ((a1IntegralFibreDiagram l P p C M).map (homOfLE (Nat.le_succ n)).op) ∧
        LinearMap.ker
          ((a1IntegralFibreDiagram l P p C M).map (homOfLE (Nat.le_succ n)).op).hom =
            Padic.coefficientExtensionIdeal l P.E (n + 1) •
              (⊤ : Submodule (Integers l P)
                ((a1IntegralFibreDiagram l P p C M).obj (op (n + 1))))) ∧
      Module.Finite (Integers l P) (a1IntegralFibre l P p C M) ∧
      Module.Free (Integers l P) (a1IntegralFibre l P p C M) ∧
      (∀ n : ℕ, Function.Surjective (a1IntegralFibreProjection l P p C M n) ∧
        LinearMap.ker (a1IntegralFibreProjection l P p C M n) =
          Padic.coefficientExtensionIdeal l P.E (n + 1) •
            (⊤ : Submodule (Integers l P) (a1IntegralFibre l P p C M))) ∧
      (∀ (n : ℕ) (g : p.group) (x : a1IntegralFibre l P p C M),
        a1IntegralFibreProjection l P p C M n (rho g x) =
          r n g (a1IntegralFibreProjection l P p C M n x)) ∧
      a1IntegralFibreTopology l P p C M =
        (Padic.coefficientExtensionMaximalIdeal l P.E).adicModuleTopology
          (a1IntegralFibre l P p C M) ∧
      @Continuous _ _
        (@instTopologicalSpaceProd _ _ inferInstance (a1IntegralFibreTopology l P p C M))
        (a1IntegralFibreTopology l P p C M)
        (fun z : p.group × a1IntegralFibre l P p C M ↦ rho z.1 z.2) ∧
      ∃ (V : SfContinuousRepresentations l P.E p)
        (e : a1RationalFibre l P p C M ≅ ModuleCat.of P.E V.obj.V)
        (B : SfInvariantLattice l P.E V)
        (i : a1IntegralFibre l P p C M ≃ₗ[Integers l P] B.submodule),
        Function.Injective (a1RationalFibreUnit l P p C M) ∧
        (∀ x : a1IntegralFibre l P p C M,
          (i x).val = e.hom (a1RationalFibreUnit l P p C M x)) ∧
        (∀ (g : p.group) (x : a1IntegralFibre l P p C M),
          e.hom (a1RationalFibreUnit l P p C M (rho g x)) =
            V.obj.ρ g (e.hom (a1RationalFibreUnit l P p C M x))) ∧
        ∃ d : a1IntegralEtaleTower l P C M ≅ (J.normalization V B).etale,
          (∀ (n : ℕ) (x : a1IntegralFibre l P p C M),
            ((J.normalization V B).fiber n).hom
              (((pointSmallEtale p.point).sheafFiber
                (A := ModuleCat.{u + 1} (Integers l P))).map (d.hom.app (op n))
                  (a1IntegralFibreProjection l P p C M n x)) =
              sfLatticeQuotientMk l P.E B n (i x)) ∧
          Nonempty (J.functor.obj V ≅
            (completedAdicChange P.X
              (C.coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X)).obj M.obj) := by
  classical
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} (Integers l P))) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  let F := C.equivalence.functor.obj M
  let LF (n : ℕ) : LisseModuleSheafCategory P.X (Integers l P) :=
    ⟨(a1IntegralEtaleTower l P C M).obj (op n), system_level_lisse l P F n⟩
  let r := fun n ↦ level_rep l P p J (LF n)
  have ht (n m : ℕ) (h : m ≤ n) (g : p.group)
      (x : (a1IntegralFibreDiagram l P p C M).obj (op n)) :
      (a1IntegralFibreDiagram l P p C M).map (homOfLE h).op (r n g x) =
        r m g ((a1IntegralFibreDiagram l P p C M).map (homOfLE h).op x) :=
    level_rep_natural l P p J (LF n) (LF m)
      (ObjectProperty.homMk ((a1IntegralEtaleTower l P C M).map (homOfLE h).op)) g x
  let rho := limit_rep l P p C M r ht
  have hflc := fun n ↦ (level_rep_evaluation l P p J (LF n)).choose
  have hfin (n : ℕ) : Module.Finite (Integers l P)
      ((a1IntegralFibreDiagram l P p C M).obj (op n)) := by
    let : Finite ((a1IntegralFibreDiagram l P p C M).obj (op n)) :=
      system_stalk_finite l P F n p.point
    exact Module.Finite.of_finite
  obtain ⟨hf, hp, htop⟩ := Padic.adicLimit_finite_modules l P.E
    (a1IntegralFibreDiagram l P p C M) hfin
    (fibre_killed l P p C M) (fibre_transition l P p C M)
  have := hf
  have hfree := fibre_free l P p C M
  refine ⟨hflc, r, rho, ?_, ?_, ht, fibre_transition l P p C M, hf, hfree,
    hp, ?_, htop, ?_, ?_⟩
  · intro n
    exact (level_rep_evaluation l P p J (LF n)).choose_spec
  · intro n
    exact ⟨system_stalk_finite l P F n p.point, level_rep_continuous l P p J (LF n)⟩
  · intro n g x
    rfl
  · exact limit_rep_continuous l P p C M r ht
      (fun n ↦ level_rep_continuous l P p J (LF n))
  · have hca := limit_rep_continuous l P p C M r ht
      (fun n ↦ level_rep_continuous l P p J (LF n))
    change a1IntegralFibreTopology l P p C M = _ at htop
    rw [htop] at hca
    let := hfree
    obtain ⟨V, e, B, i, hinj, hi, heq⟩ := integral_representation_rationalization l P p
      (ModuleCat.of _ (a1IntegralFibre l P p C M)) rho hca
    refine ⟨V, e, B, i, hinj, hi, heq, ?_⟩
    obtain ⟨q, hq⟩ := quotient_stalk_equiv l P p C M V B i hp
    let N := J.normalization V B
    have hact (g : p.group) (x : a1IntegralFibre l P p C M) :
        i (rho g x) = ⟨V.obj.ρ g (i x).val, B.stable g (i x)⟩ := by
      apply Subtype.ext
      rw [hi, heq, ← hi]
    have hlevel (n : ℕ) : ∃! d : (a1IntegralEtaleTower l P C M).obj (op n) ≅
        N.etale.obj (op n),
        ((pointSmallEtale p.point).sheafFiber
          (A := ModuleCat.{u + 1} (Integers l P))).mapIso d =
            ((q n).trans (N.fiber n).toLinearEquiv.symm).toModuleIso := by
      apply finite_fibre_linear_lifting l P.E p J.finiteCorrespondence _ _ (hflc n) (N.flc n)
      intro g x y hxy
      have hκ : Function.Injective (sfModuleFiberToSet l P.E p
          ((a1IntegralEtaleTower l P C M).obj (op n))) :=
        (((pointSmallEtale p.point).sheafFiberCompIso
          (CategoryTheory.forget (ModuleCat.{u + 1} (Integers l P)))).app _).toEquiv.symm.injective
      have hyr : y = r n g x := hκ
        (hxy.trans ((level_rep_evaluation l P p J (LF n)).choose_spec g x).symm)
      subst y
      obtain ⟨z, rfl⟩ := (hp n).1 x
      have hpr : r n g (a1IntegralFibreProjection l P p C M n z) =
          a1IntegralFibreProjection l P p C M n (rho g z) := rfl
      change sfModuleFiberToSet l P.E p (N.etale.obj (op n))
        ((N.fiber n).inv (q n (r n g (a1IntegralFibreProjection l P p C M n z)))) = _
      rw [hpr, hq]
      change sfModuleFiberToSet l P.E p (N.etale.obj (op n))
        ((N.fiber n).inv (sfLatticeQuotientMk l P.E B n (i (rho g z)))) =
          (J.finiteCorrespondence.γ g).hom.app
            (galoisUnderlyingFLC _ (N.etale.obj (op n)) (N.flc n))
              (sfModuleFiberToSet l P.E p (N.etale.obj (op n))
                ((N.fiber n).inv
                  (q n (a1IntegralFibreProjection l P p C M n z))))
      rw [hq, hact]
      exact (N.monodromy n g (i z)).symm
    let d := fun n ↦ (hlevel n).exists.choose
    have hd (n : ℕ) := (hlevel n).exists.choose_spec
    have hnat {a b : ℕᵒᵖ} (f : a ⟶ b) :
        (a1IntegralEtaleTower l P C M).map f ≫ (d b.unop).hom =
          (d a.unop).hom ≫ N.etale.map f := by
      apply eq_of_finite_fiber p J.finiteCorrespondence
        (hflc a.unop) (N.flc b.unop)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨z, rfl⟩ := (hp a.unop).1 x
      simp only [Functor.map_comp, ModuleCat.comp_apply]
      have htrans : (a1IntegralFibreDiagram l P p C M).map f
          (a1IntegralFibreProjection l P p C M a.unop z) =
          a1IntegralFibreProjection l P p C M b.unop z := z.property f
      have hda (n : ℕ) (x : (a1IntegralFibreDiagram l P p C M).obj (op n)) :
          ((pointSmallEtale p.point).sheafFiber.map (d n).hom) x =
            (N.fiber n).inv (q n x) := by
        exact ConcreteCategory.congr_hom (congrArg (fun e ↦ e.hom) (hd n)) x
      change ((pointSmallEtale p.point).sheafFiber.map (d b.unop).hom)
        ((a1IntegralFibreDiagram l P p C M).map f
          (a1IntegralFibreProjection l P p C M a.unop z)) = _
      rw [htrans, hda, hda, hq]
      change (N.fiber b.unop).inv (sfLatticeQuotientMk l P.E B b.unop (i z)) =
        ((pointSmallEtale p.point).sheafFiber.map (N.etale.map f))
          ((N.fiber a.unop).inv
            (q a.unop (a1IntegralFibreProjection l P p C M a.unop z)))
      rw [hq]
      apply (N.fiber b.unop).toLinearEquiv.injective
      change (N.fiber b.unop).hom ((N.fiber b.unop).inv _) = _
      rw [Iso.inv_hom_id_apply]
      have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
      rw [hf]
      exact (N.transition a.unop b.unop (leOfHom f.unop) (i z)).symm
    let D : a1IntegralEtaleTower l P C M ≅ N.etale :=
      NatIso.ofComponents (fun n ↦ d n.unop) (fun f ↦ hnat f)
    refine ⟨D, ?_, completed_normalization_recovery l P p C J M V B D⟩
    intro n x
    have hh := congrArg (fun e ↦ e.hom) (hd n)
    have hhx := ConcreteCategory.congr_hom hh
      (a1IntegralFibreProjection l P p C M n x)
    change (N.fiber n).hom
      (((pointSmallEtale p.point).sheafFiber.map (d n).hom)
        (a1IntegralFibreProjection l P p C M n x)) = _
    change ((pointSmallEtale p.point).sheafFiber.map (d n).hom)
        (a1IntegralFibreProjection l P p C M n x) =
      (N.fiber n).inv (q n (a1IntegralFibreProjection l P p C M n x)) at hhx
    rw [hhx]
    rw [Iso.inv_hom_id_apply, hq]


end AlgebraicGeometry.Scheme
