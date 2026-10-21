/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Normalized quotient tensor products on the étale site

Source: Stacks Project, Tags 03PT and 03PU, and the support-quotient refinement of
blueprint main-20261015, `lem-pur-kunneth-supported`, final paragraph
(blueprint: lem-pur-etale-quotient-tensor-stalk-criterion).

Module-valued sheaves encode modules over the constant ring sheaf via the published
constant-scalar equivalence. The tensor is the existing sheafified tensor; its unit is
that constant ring module. The section product below is the unit multiplication, so
sections may be locally constant rather than globally constant. The stalk unit map
is the canonical identification of the constant ring stalk with the coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

variable (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})

/-- The tensor of the two quotient generators, with one sent to one tensor one.
Source: support-quotient refinement of `lem-pur-kunneth-supported`, final paragraph
(blueprint: lem-pur-etale-quotient-tensor-stalk-criterion). -/
def etaleQuotientTensorGenerator
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (q : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ F)
    (s : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ G) :
    𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ F ⊗ G :=
  (λ_ (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))).inv ≫ (q ⊗ₘ s)

/-- The specified normalized stalk identifications: on the subset there is an
A-linear identification with A carrying the quotient map to the canonical unit-stalk
identification; off the subset the stalk is zero. An identification with a zero module
and its zero map is unique, so the latter clause retains exactly the off-support data.
Source: support-quotient refinement of `lem-pur-kunneth-supported`, final paragraph
(blueprint: lem-pur-etale-quotient-tensor-stalk-criterion). -/
def EtaleQuotientStalkNormalized
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)} (S : Set T)
    (q : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ F) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
    (t (IsLocalRing.closedPoint Ω) ∈ S →
      ∃ i : ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj F ≅ ModuleCat.of A A,
        ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map q ≫ i.hom =
          Functor.OplaxMonoidal.η
            ((pointSmallEtale t).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} A))) ∧
    (t (IsLocalRing.closedPoint Ω) ∉ S →
      IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj F))

private theorem normalized_tensor_map
    {C : Type*} [Category C] [MonoidalCategory C]
    {B : Type*} [Category B] [MonoidalCategory B]
    (P : C ⥤ B) [P.Monoidal] {F G : C}
    (q : 𝟙_ C ⟶ F) (s : 𝟙_ C ⟶ G)
    (iF : P.obj F ≅ 𝟙_ B) (iG : P.obj G ≅ 𝟙_ B)
    (hq : P.map q ≫ iF.hom = Functor.OplaxMonoidal.η P)
    (hs : P.map s ≫ iG.hom = Functor.OplaxMonoidal.η P) :
    P.map ((λ_ (𝟙_ C)).inv ≫ (q ⊗ₘ s)) ≫
        Functor.OplaxMonoidal.δ P F G ≫ (iF.hom ⊗ₘ iG.hom) ≫
          (λ_ (𝟙_ B)).hom = Functor.OplaxMonoidal.η P := by
  rw [P.map_comp]
  simp only [Category.assoc, ← Functor.OplaxMonoidal.δ_natural_assoc,
    tensorHom_comp_tensorHom_assoc, hq, hs]
  rw [Functor.OplaxMonoidal.δ_comp_η_tensorHom_assoc]
  simp

private theorem normalized_tensor_isIso
    {C : Type*} [Category C] [MonoidalCategory C]
    {B : Type*} [Category B] [MonoidalCategory B]
    (P : C ⥤ B) [P.Monoidal] {F G : C}
    (q : 𝟙_ C ⟶ F) (s : 𝟙_ C ⟶ G)
    (iF : P.obj F ≅ 𝟙_ B) (iG : P.obj G ≅ 𝟙_ B)
    (hq : P.map q ≫ iF.hom = Functor.OplaxMonoidal.η P)
    (hs : P.map s ≫ iG.hom = Functor.OplaxMonoidal.η P) :
    IsIso (P.map ((λ_ (𝟙_ C)).inv ≫ (q ⊗ₘ s))) := by
  let k := (Functor.Monoidal.μIso P F G).symm ≪≫ tensorIso iF iG ≪≫ λ_ (𝟙_ B)
  have h : P.map ((λ_ (𝟙_ C)).inv ≫ (q ⊗ₘ s)) ≫ k.hom =
      Functor.OplaxMonoidal.η P := normalized_tensor_map P q s iF iG hq hs
  exact IsIso.of_isIso_fac_right h

private theorem stalk_ext
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)} {f g : F ⟶ G}
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map f =
        ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map g) : f = g := by
  apply ((isConservativeFamilyOfPoints_ulift_pointSmallEtale T).jointlyFaithful
    (ModuleCat.{u + 1} A)).map_injective
  rintro ⟨_, ⟨x⟩⟩
  exact h _ (T.algClosurePoint x)

private theorem tensor_stalk_zero
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (h : IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj F) ∨
      IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj G)) :
    IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj (F ⊗ G)) := by
  let P := (pointSmallEtale t).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} A)
  apply IsZero.of_iso (Y := P.obj F ⊗ P.obj G) _
    (Functor.Monoidal.μIso P F G).symm
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← id_tensorHom_id]
  rcases h with h | h
  · rw [h.eq_of_src (𝟙 _) 0, MonoidalPreadditive.zero_tensor]
  · rw [h.eq_of_src (𝟙 _) 0, MonoidalPreadditive.tensor_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Normalized quotient multiplication, with its section and stalk formulas.
Source: Stacks 03PT (exact stalks), 03PU (conservativity), and blueprint
`lem-pur-kunneth-supported`, final paragraph
(blueprint: lem-pur-etale-quotient-tensor-stalk-criterion).

Proof:
1. The constant-ring module equivalence and the sheafification-tensor comparison
identify the tensor over A_T with the sheafification of the presheaf tensor over A.
2. The geometric stalk tensor comparison sends the generator to q_t(c) tensor s_t(1).
On E intersect D this is c tensor one, inverse to multiplication. Elsewhere at least
one factor vanishes, so the tensor stalk vanishes. Its kernel is the kernel of r_t.
3. Module sheaves are abelian. Their faithful exact forgetful functor, exact stalks
and geometric-stalk conservativity imply the cokernel of the generator is zero.
The preadditive epi/cokernel criterion therefore makes the generator epic.
4. The kernel inclusion followed by r is zero on every geometric stalk, hence zero
by exactness and conservativity. This uses the normalization, not just stalk ranks.
5. The exact-epi cokernel universal property gives the unique e with m followed by e
 equal to r. Epimorphic cancellation gives uniqueness among all morphisms.
6. Its stalk is multiplication on the intersection, with inverse c tensor one;
off the intersection it is the unique zero-to-zero map. Conservativity gives the
isomorphism. The inverse is module-linear because e is module-linear and invertible.
7. Bilinearity gives q(a) tensor s(b) = m(ab) on local sections before sheafification
and hence after it. Applying e gives r(ab). Flatness is retained, though unused.
The cited proof dependencies are respectively the constant-ring equivalence,
module-sheafification tensor, stalk-tensor comparison, module-sheaf forgetful theorem,
exact geometric stalks, conservativity, and the exact-epi cokernel lemma. -/
theorem etale_quotient_tensor_stalk_criterion
    (E D : Set T) (F G H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (q : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ F)
    (s : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ G)
    (r : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ H)
    [Epi q] [Epi s] [Epi r]
    (hflat : exactFunctor _ _ (tensorRight F))
    (hq : EtaleQuotientStalkNormalized A T E q)
    (hs : EtaleQuotientStalkNormalized A T D s)
    (hr : EtaleQuotientStalkNormalized A T (E ∩ D) r) :
    Epi (etaleQuotientTensorGenerator A T q s) ∧
    ∃ e : F ⊗ G ≅ H,
      etaleQuotientTensorGenerator A T q s ≫ e.hom = r ∧
      (∀ f : F ⊗ G ⟶ H, etaleQuotientTensorGenerator A T q s ≫ f = r → f = e.hom) ∧
      (∀ (U : T.Etaleᵒᵖ)
        (a b : (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj.obj U),
        (e.hom.hom.app U)
          ((Functor.LaxMonoidal.μ
            (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) F G).app U
              ((q.hom.app U a) ⊗ₜ[A] (s.hom.app U b))) =
        r.hom.app U
          (((λ_ (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))).hom.hom.app U)
            ((Functor.LaxMonoidal.μ
              (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
                (𝟙_ _) (𝟙_ _)).app U (a ⊗ₜ[A] b)))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        (t (IsLocalRing.closedPoint Ω) ∈ E ∩ D →
          ∀ (iF : ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj F ≅ ModuleCat.of A A)
            (iG : ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj G ≅ ModuleCat.of A A)
            (iH : ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj H ≅ ModuleCat.of A A),
            ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map q ≫ iF.hom =
              Functor.OplaxMonoidal.η
                ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) →
            ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map s ≫ iG.hom =
              Functor.OplaxMonoidal.η
                ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) →
            ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map r ≫ iH.hom =
              Functor.OplaxMonoidal.η
                ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) →
            (∀ a b : A, iH.hom
              ((((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map e.hom)
                (Functor.LaxMonoidal.μ ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) F G
                  ((iF.inv a) ⊗ₜ[A] (iG.inv b)))) = a * b) ∧
            (∀ c : A, (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map e.inv)
              (iH.inv c) =
                Functor.LaxMonoidal.μ ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) F G
                  ((iF.inv c) ⊗ₜ[A] (iG.inv 1)))) ∧
        (t (IsLocalRing.closedPoint Ω) ∉ E ∩ D →
          IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj (F ⊗ G)) ∧
          IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj H) ∧
          ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map e.hom = 0)) := by
  classical
  have _hflat := hflat
  let m := etaleQuotientTensorGenerator A T q s
  have hon (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
      (ht : t (IsLocalRing.closedPoint Ω) ∈ E ∩ D) :
      IsIso (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map m) := by
    obtain ⟨iF, hiF⟩ := (hq Ω t).1 ht.1
    obtain ⟨iG, hiG⟩ := (hs Ω t).1 ht.2
    exact normalized_tensor_isIso _ q s iF iG hiF hiG
  have hoff (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
      (ht : t (IsLocalRing.closedPoint Ω) ∉ E ∩ D) :
      IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj (F ⊗ G)) := by
    apply tensor_stalk_zero A T t
    by_cases hE : t (IsLocalRing.closedPoint Ω) ∈ E
    · exact Or.inr ((hs Ω t).2 (fun hD ↦ ht ⟨hE, hD⟩))
    · exact Or.inl ((hq Ω t).2 hE)
  have hepi (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
      Epi (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map m) := by
    by_cases ht : t (IsLocalRing.closedPoint Ω) ∈ E ∩ D
    · have := hon Ω t ht
      infer_instance
    · exact (hoff Ω t ht).epi _
  have : Epi m := ⟨by
    intro Z f g h
    apply stalk_ext A T
    intro Ω _ _ t
    let P := (pointSmallEtale t).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} A)
    have := hepi Ω t
    apply (cancel_epi (P.map m)).mp
    change P.map m ≫ P.map f = P.map m ≫ P.map g
    simpa only [P.map_comp] using congrArg P.map h⟩
  have hk : kernel.ι m ≫ r = 0 := by
    apply stalk_ext A T
    intro Ω _ _ t
    let P := (pointSmallEtale t).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} A)
    rw [P.map_comp, P.map_zero]
    by_cases ht : t (IsLocalRing.closedPoint Ω) ∈ E ∩ D
    · have := hon Ω t ht
      have hz : P.map (kernel.ι m) = 0 := by
        apply (cancel_mono (P.map m)).mp
        rw [← P.map_comp, kernel.condition, P.map_zero, zero_comp]
      rw [hz, zero_comp]
    · exact ((hr Ω t).2 ht).eq_of_tgt _ _
  have : Epi (ShortComplex.kernelSequence m).g := by
    change Epi m
    infer_instance
  let e₀ : F ⊗ G ⟶ H := (ShortComplex.kernelSequence_exact m).desc r hk
  have he₀ : m ≫ e₀ = r := (ShortComplex.kernelSequence_exact m).g_desc r hk
  have : IsIso e₀ := by
    apply isIso_of_isIso_sheafFiber_map
    intro x
    let t := T.algClosurePoint x
    let P := (pointSmallEtale t).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} A)
    change IsIso (P.map e₀)
    by_cases ht : t (IsLocalRing.closedPoint _) ∈ E ∩ D
    · have := hon _ t ht
      obtain ⟨iH, hiH⟩ := (hr _ t).1 ht
      have : IsIso (P.map r) := IsIso.of_isIso_fac_right hiH
      exact IsIso.of_isIso_fac_left (show P.map m ≫ P.map e₀ = P.map r by
        rw [← P.map_comp, he₀])
    · exact (hoff _ t ht).isIso ((hr _ t).2 ht) _
  let e := asIso e₀
  change m ≫ e.hom = r at he₀
  refine ⟨inferInstance, e, he₀, ?_, ?_, ?_⟩
  · intro f hf
    exact (cancel_epi m).mp (hf.trans he₀.symm)
  · intro U a b
    have hm : (q ⊗ₘ s) ≫ e.hom = (λ_ (𝟙_ _)).hom ≫ r := by
      calc
        _ = (λ_ (𝟙_ _)).hom ≫ (m ≫ e.hom) := by
          simp [m, etaleQuotientTensorGenerator]
        _ = _ := by rw [he₀]
    let P := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)
    have hn := Functor.LaxMonoidal.μ_natural P q s
    have h := congrArg (fun f ↦ f ≫ P.map e.hom) hn
    simp only [Category.assoc] at h
    rw [← P.map_comp, hm, P.map_comp] at h
    have hU := NatTrans.congr_app h U
    exact ConcreteCategory.congr_hom hU (a ⊗ₜ[A] b)
  · intro Ω _ _ t
    constructor
    · intro ht iF iG iH hiF hiG hiH
      let P := (pointSmallEtale t).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} A)
      have := hon Ω t ht
      have hn := normalized_tensor_map P q s iF iG hiF hiG
      have hm : P.map e.hom ≫ iH.hom =
          Functor.OplaxMonoidal.δ P F G ≫ (iF.hom ⊗ₘ iG.hom) ≫
            (λ_ (𝟙_ (ModuleCat.{u + 1} A))).hom := by
        apply (cancel_epi (P.map m)).mp
        rw [← Category.assoc, ← P.map_comp, he₀]
        exact hiH.trans hn.symm
      have hmul : ∀ a b : A, iH.hom (P.map e.hom
          (Functor.LaxMonoidal.μ P F G (iF.inv a ⊗ₜ[A] iG.inv b))) = a * b := by
        intro a b
        have h := congrArg (fun f ↦ Functor.LaxMonoidal.μ P F G ≫ f) hm
        simp only [← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp] at h
        have hab := ConcreteCategory.congr_hom h (iF.inv a ⊗ₜ[A] iG.inv b)
        change iH.hom (P.map e.hom
          (Functor.LaxMonoidal.μ P F G (iF.inv a ⊗ₜ[A] iG.inv b))) =
            (λ_ (ModuleCat.of A A)).hom
              (iF.hom (iF.inv a) ⊗ₜ[A] iG.hom (iG.inv b)) at hab
        erw [ModuleCat.hom_inv_apply iF a, ModuleCat.hom_inv_apply iG b,
          ModuleCat.MonoidalCategory.leftUnitor_hom_apply, smul_eq_mul] at hab
        exact hab
      refine ⟨hmul, ?_⟩
      intro c
      apply (ModuleCat.mono_iff_injective (P.map e.hom ≫ iH.hom)).mp inferInstance
      change iH.hom (P.map e.hom (P.map e.inv (iH.inv c))) = _
      calc
        _ = c := by
          change iH.hom ((P.map e.inv ≫ P.map e.hom) (iH.inv c)) = c
          rw [← P.map_comp, e.inv_hom_id, P.map_id]
          simp
        _ = _ := by simpa using (hmul c 1).symm
    · intro ht
      exact ⟨hoff Ω t ht, (hr Ω t).2 ht, ((hr Ω t).2 ht).eq_of_tgt _ _⟩

end AlgebraicGeometry.Scheme
