/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.PointDerivedHomModels
import Sheaf.Paper.PointExtensionKFlat
import Sheaf.Paper.PointHomComplexAdjunction
import Sheaf.Paper.PointTensorHomEvaluation
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Derived Hom and evaluation at a pro-etale point

Source: Stacks Project, Tags 0A8X, 08J7, 08BJ and 0G7E.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.PointDerivedHom

private theorem derivedModelMap_isIso
    (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
    (α : constantRing.{t, u} k R ⟶ B)
    (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
    (adj : L ⊣ sections.{t, u} k B α)
    [PreservesFiniteLimits (sections.{t, u} k B α)]
    [PreservesFiniteColimits (sections.{t, u} k B α)]
    (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)
    (I : CochainComplex (Modules.{t, u} k B) ℤ) [I.IsKInjective]
    (iota : (CochainComplex.singleFunctor (Modules.{t, u} k B) 0).obj
      (SheafOfModules.unit (ring.{t, u} k B)) ⟶ I) [QuasiIso iota] :
    IsIso (derivedModelMap.{t, u} k B α L adj c I iota) := by
  let A := Modules.{t, u} k B
  let : IsGrothendieckAbelian.{max u (t + 1)} A :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      (Scheme.ProEt.topology (Spec (.of k))) B).1
  let η : I ⟶ (CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} A).obj I :=
    (CochainComplex.toKInjectiveResolution.{max u (t + 1)} A).app I
  have : QuasiIso η :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A I).2
  have : ((CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} A).obj I).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj A I
  have hh := quasiIso_homComplex_mapOfUniverses.{t + 1, t, u}
    (R := B) η (𝟙 ((extensionComplex k B α L adj).obj c))
  rw [op_id, (homComplexFunctor (R := B)).map_id, NatTrans.id_app,
    Category.id_comp] at hh
  have : IsIso (DerivedCategory.Q.map
      (((homComplexFunctor (R := B)).obj (op ((extensionComplex k B α L adj).obj c))).map η)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hh
  have hmodel : IsIso (IntegralHom.homModelMap.{t, u} (Spec (.of k)) B
      ((extensionComplex k B α L adj).obj c) I) := by
    unfold IntegralHom.homModelMap
    change IsIso (DerivedCategory.Q.map
      (((homComplexFunctor (R := B)).obj
        (op ((extensionComplex k B α L adj).obj c))).map η) ≫ _)
    infer_instance
  have hprod : IsIso (CategoryTheory.Prod.mkHom
      (𝟙 (op (DerivedCategory.Q.obj ((extensionComplex k B α L adj).obj c))))
      (inv (DerivedCategory.Q.map iota))) := by
    exact (CategoryTheory.isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have hderived : IsIso
      ((derivedInternalHomOfUniverses.{t + 1, t, u}
        (Scheme.ProEt.topology (Spec (.of k))) B).map
          (CategoryTheory.Prod.mkHom
            (𝟙 (op (DerivedCategory.Q.obj ((extensionComplex k B α L adj).obj c))))
            (inv (DerivedCategory.Q.map iota)))) := by infer_instance
  unfold derivedModelMap
  infer_instance

private theorem generator_one_natural
    (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
    (α : constantRing.{t, u} k R ⟶ B)
    (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
    (hobj : ∀ M : ModuleCat.{max u (t + 1)} R, L.obj M = extensionObject k B α M)
    (adj : L ⊣ sections.{t, u} k B α)
    (hex : ExplicitAdjunction k B α L hobj adj)
    {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N) (x : M) :
    (L.map f).val.app (op (finalObject k))
      (generator k B α L hobj M (op (finalObject k)) 1 x) =
        generator k B α L hobj N (op (finalObject k)) 1 (f.hom x) := by
  have hu (T : ModuleCat.{max u (t + 1)} R) (y : T) :
      (adj.unit.app T).hom y = generator k B α L hobj T (op (finalObject k)) 1 y := by
    have h := hex.1 T (L.obj T) (𝟙 _) y
    rw [adj.homEquiv_id] at h
    exact h
  have h := congrArg (fun a ↦ a.hom x) (adj.unit.naturality f)
  change (adj.unit.app N).hom (f.hom x) =
    (L.map f).val.app (op (finalObject k)) ((adj.unit.app M).hom x) at h
  rw [hu, hu] at h
  exact h.symm

private theorem homValue_natural
    (k : Type t) [Field k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
    {P P' I I' : CochainComplex (Modules.{t, u} k B) ℤ}
    (f : P' ⟶ P) (g : I ⟶ I') (j p : ℤ)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (h : ((sheafHom k B P I).X j).val.obj U) (x : (P'.X p).val.obj U) :
    homValue k B P' I' j p U
      (((((homComplexFunctor (R := B)).map f.op).app I ≫
        ((homComplexFunctor (R := B)).obj (op P')).map g).f j).val.app U h) x =
      (g.f (p + j)).val.app U
        (homValue k B P I j p U h ((f.f p).val.app U x)) := by
  have he := homComplexFunctor_map_f_π f g j p (p + j) rfl
  have hx := congrArg (fun a ↦ (((a.val.app U h).app
    (op (Over.mk (𝟙 U.unop)))).hom x)) he
  exact hx

private theorem comparison_natural
    (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
    (α : constantRing.{t, u} k R ⟶ B)
    (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
    (hobj : ∀ M : ModuleCat.{max u (t + 1)} R, L.obj M = extensionObject k B α M)
    (adj : L ⊣ sections.{t, u} k B α)
    (hex : ExplicitAdjunction k B α L hobj adj)
    (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)
    (I : CochainComplex (Modules.{t, u} k B) ℤ)
    (q : (sectionComplex k B α).obj
      (sheafHom k B ((extensionComplex k B α L adj).obj c) I) ≅
        CochainComplex.moduleHomComplex c ((sectionComplex k B α).obj I))
    (hq : IsComparison k B α L hobj adj c I q) :
    ComparisonNatural k B α L hobj adj c I q := by
  intro c' I' f g q' hq' j p h x
  rw [hq', hq]
  refine (homValue_natural k B ((extensionComplex k B α L adj).map f) g j p
    (op (finalObject k)) h
    (generator k B α L hobj (c'.X p) (op (finalObject k)) 1 x)).trans ?_
  exact congrArg (fun y ↦ (g.f (p + j)).val.app (op (finalObject k))
    (homValue k B ((extensionComplex k B α L adj).obj c) I j p
      (op (finalObject k)) h y))
    (generator_one_natural k B α L hobj adj hex (f.f p) x)

/-- Derived sections-Hom comparison for both coefficient models at the geometric point.
Source: blueprint main-20261015, lem-pod-point-dualizing-complex.proof.md, second sentence;
Stacks sites-cohomology Tags 0G7E, 0A8X, 08J7, 0A95 and 0FPT, derived Tag 08BJ,
and sites Tag 00WJ (blueprint: lem-pod-point-derived-hom-evaluation).

Proof: constant sheafification is the finite-limit-preserving inverse image of the
geometric morphism to sets. Tensor extension is its module pullback, so a flat-term
K-flat complex remains K-flat by the separate point_extension_kflat specialization.
In each Hom degree apply the assumed explicit adjunction to every product factor.
Evaluation at 1 tensor x gives q; its inverse sends t to b tensor x mapped to b t(x).
The differential d_I h - (-1)^j h d_c commutes with this formula, and pre- and
post-composition prove naturality. The exact-left-adjoint lemma
lem-weil-pbc-right-adjoint-preserves-kinjective makes sections of I K-injective.
Exact sections preserve the resolution quasi-isomorphism; the bijective constant-value
map identifies its degree-zero source with R. Thus this is a K-injective resolution
of R. The derived-internal-Hom representative comparison and exact sections descend q
to the specified derived isomorphism. The independent-universe Hom invariance lemma
gives independence of representatives. Evaluation with the argument first is the ordinary Hom counit
preceded by symmetry, so on bidegree (p,j) it is (-1)^(p*j) h(y). Its differential
identity follows by cancellation of the two h(dy) terms. Define beta on each total
summand by x tensor h mapped to (1 tensor x) tensor h. Balancing, restriction and
the tensor differential give a chain map without commuting sections with coproducts.
Both composites evaluate to (-1)^(p*j) h(1 tensor x). Pure tensors generate each
module summand, proving the chain-map equality and hence the derived evaluation square.
All tensors are ordinary; this makes no completed-tensor assertion. -/
theorem point_derived_hom_evaluation (D : FiniteFieldDatum.{t})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (_hn : 1 ≤ n) (integral : Bool) :
    Statement.{t, u} D.k
      (coefficientSheaf.{t, u} D.k l E n integral)
      (coefficientMap.{t, u} D.k l E n integral) := by
  intro L hobj hmap adj hex hLlim hLcol hSlim hScol hscalar c hc hflat I hI iota hiota
  let k := D.k
  let B := coefficientSheaf.{t, u} k l E n integral
  let α := coefficientMap.{t, u} k l E n integral
  have : L.Additive := adj.left_adjoint_additive
  have := adj.preservesKInjectiveComplexes
  have hKI : CochainComplex.IsKInjective ((sectionComplex k B α).obj I) :=
    inferInstance
  have hcoef : IsIso (coefficientSections k B α) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact hscalar
  have hres : QuasiIso (sectionResolution k B α I iota) := by
    unfold sectionResolution
    infer_instance
  refine ⟨hKI, hres, ?_, ?_⟩
  · exact point_extension_kflat k B α L hobj hmap adj c hc hflat
  · obtain ⟨q, hq⟩ := point_hom_complex_adjunction k B α L hobj adj c I hex
    refine ⟨q, hq, comparison_natural k B α L hobj adj hex c I q hq,
      point_tensor_hom_evaluation k B α L hobj adj c hex I q hq, ?_⟩
    have : IsIso (derivedModelMap k B α L adj c I iota) :=
      derivedModelMap_isIso k B α L adj c I iota
    let d := (asIso (derivedModelMap k B α L adj c I iota)).symm ≪≫
      DerivedCategory.Q.mapIso q
    refine ⟨d, ?_⟩
    exact IsIso.hom_inv_id_assoc _ _

end WeilConjectures.PointDerivedHom
