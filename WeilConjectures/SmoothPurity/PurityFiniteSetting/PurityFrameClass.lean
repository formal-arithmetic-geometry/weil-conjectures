/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameKummer
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFramePrincipalBoundary

/-!
# The concrete class of an étale frame

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
def-pur-frame-class (blueprint: def-pur-frame-class). The existing EtaleFrame
records the scheme-theoretic generating condition. The coefficient extension
realizes each individual support boundary by Yoneda composition. The ordered
product uses the published supported cup, associating to the left.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- Append one Tate line on the etale site. For d=0 this is the left unit map;
for d>0 it is the defining left-associated tensor power.
Source: def-pur-frame-class, twist addition (blueprint: def-pur-frame-class). -/
def frameEtaleTensorNext (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    (d : ℕ) → P.frameTwistEtale X d ⊗ P.frameTwistEtale X 1 ≅ P.frameTwistEtale X (d + 1)
  | 0 => λ_ (P.frameTwistEtale X 1)
  | _ + 1 => Iso.refl _

/-- Transport this tensor map by the published strong monoidal comparison.
Source: def-pur-frame-class, sheaf tensors (blueprint: def-pur-frame-class). -/
def frameSheafTensorNext (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :
    P.frameTwist X d ⊗ P.frameTwist X 1 ≅ P.frameTwist X (d + 1) :=
  (asIso (Functor.OplaxMonoidal.δ
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
    (P.frameTwistEtale X d) (P.frameTwistEtale X 1))).symm ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapIso
        (P.frameEtaleTensorNext X d)

/-- Apply the ordinary degree-zero tensor map through a named single functor.
Keeping the functor parameter explicit avoids unfolding the localization at each use.
Source: def-pur-frame-class, coefficient tensors (blueprint: def-pur-frame-class). -/
def frameSingleTensorMap {C : Type v} [Category.{w} C] [Abelian C]
    [hD : HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    (S : C ⥤ DerivedCategory C) (hS : S = DerivedCategory.singleFunctor C 0)
    {L M N : C} (μ : L ⊗ M ⟶ N) :
    ((curriedTensor (DerivedCategory C)).obj (S.obj L)).obj (S.obj M) ⟶ S.obj N := by
  subst S
  exact cupDerivedCoefficientMap μ

/-- The K-flat degree-zero tensor comparison followed by the actual sheaf tensor
multiplication. The local freeness theorem makes this the usual identification
of derived and ordinary finite twist tensors.
Source: def-pur-frame-class, final paragraph (blueprint: def-pur-frame-class). -/
def frameTensorNext (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :
    cupTensorObject P X ((cupSingle P X).obj (P.frameTwist X d))
        ((cupSingle P X).obj (P.frameTwist X 1)) ⟶
      (cupSingle P X).obj (P.frameTwist X (d + 1)) :=
  frameSingleTensorMap (hD := cupHasDerivedCategory P X) (hDM := cupMonoidal P X)
    (cupSingle P X) rfl (P.frameSheafTensorNext X d).hom

/-- Closed coefficient pushforwards along isomorphic closed subschemes agree by
the canonical pushforward-composition and constant-pullback comparisons.
Source: def-pur-frame-class, scheme-theoretic support intersection
(blueprint: def-pur-frame-class). -/
def frameClosedCoefficientIso (P : PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X) (e : Z ≅ W)
    (h : e.hom ≫ j = i) :
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ≅
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W) :=
  (lowerStarCongr (ModuleCat.{u + 1} P.Coefficient) h.symm).app (P.constant Z) ≪≫
    ((lowerStarComp (ModuleCat.{u + 1} P.Coefficient) e.hom j).app (P.constant Z)).symm ≪≫
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) j).mapIso
      (((upperStarIsoLowerStarInv (ModuleCat.{u + 1} P.Coefficient) e.symm).app
        (P.constant Z)).symm ≪≫ P.frameConstantPullback e.inv)

/-- The common zero subscheme is the scheme-theoretic intersection of the prefix
zero subscheme and the final principal zero subscheme. The equation over X makes
the isomorphism unique, because the intersection immersion is monic.
Source: def-pur-frame-class, sum of principal ideals
(blueprint: def-pur-frame-class).
Proof: on an affine chart, the prefix ideal plus the last principal ideal is the
ideal generated by the full tuple. The identity of these quotient presentations
gives the unique isomorphism over that chart. These unique maps agree on overlaps
and glue. Their inverses glue too, so the resulting map is an isomorphism. -/
theorem frameIntersection_existsUnique (X : Scheme.{u}) (d : ℕ)
    (f : Fin (d + 1) → Γ(X, ⊤)) :
    ∃! e : X.zeroLocusSubscheme (Set.range f) ≅
        pullback (X.zeroLocusSubschemeι (Set.range (fun k : Fin d ↦ f k.castSucc)))
          (X.zeroLocusSubschemeι {f (Fin.last d)}),
      e.hom ≫ cupIntersection
        (X.zeroLocusSubschemeι (Set.range (fun k : Fin d ↦ f k.castSucc)))
        (X.zeroLocusSubschemeι {f (Fin.last d)}) = X.zeroLocusSubschemeι (Set.range f) := by
  have hf : Set.range f =
      Set.range (fun k : Fin d ↦ f k.castSucc) ∪ {f (Fin.last d)} := by
    ext t
    constructor
    · rintro ⟨k, rfl⟩
      induction k using Fin.lastCases with
      | last => exact Or.inr (Set.mem_singleton _)
      | cast k => exact Or.inl ⟨k, rfl⟩
    · rintro (⟨k, rfl⟩ | ht)
      · exact ⟨k.castSucc, rfl⟩
      · exact ⟨Fin.last d, (Set.mem_singleton_iff.mp ht).symm⟩
  have hs : Ideal.span (Set.range f) =
      Ideal.span (Set.range (fun k : Fin d ↦ f k.castSucc)) ⊔
        Ideal.span {f (Fin.last d)} := by rw [hf, Ideal.span_union]
  let h := Scheme.isPullback_zeroLocusSubschemeι_union (X := X) hs
  have he : h.isoPullback.hom ≫ cupIntersection
      (X.zeroLocusSubschemeι (Set.range (fun k : Fin d ↦ f k.castSucc)))
      (X.zeroLocusSubschemeι {f (Fin.last d)}) =
      X.zeroLocusSubschemeι (Set.range f) := by
    rw [cupIntersection, ← Category.assoc, h.isoPullback_hom_fst]
    exact Scheme.IdealSheafData.inclusion_subschemeι _
  refine ⟨h.isoPullback, he, ?_⟩
  intro e he'
  apply Iso.ext
  exact (cancel_mono (cupIntersection
    (X.zeroLocusSubschemeι (Set.range (fun k : Fin d ↦ f k.castSucc)))
    (X.zeroLocusSubschemeι {f (Fin.last d)}))).mp (he'.trans he.symm)

/-- The unique intersection isomorphism just specified.
Source: def-pur-frame-class, support intersection (blueprint: def-pur-frame-class). -/
def frameIntersectionIso (X : Scheme.{u}) (d : ℕ) (f : Fin (d + 1) → Γ(X, ⊤)) :=
  (frameIntersection_existsUnique X d f).exists.choose

/-- Its defining equation over X.
Source: def-pur-frame-class, support intersection (blueprint: def-pur-frame-class).
Proof: this is the characterizing equation of frameIntersection_existsUnique. -/
theorem frameIntersectionIso_over (X : Scheme.{u}) (d : ℕ)
    (f : Fin (d + 1) → Γ(X, ⊤)) :
    (frameIntersectionIso X d f).hom ≫ cupIntersection
      (X.zeroLocusSubschemeι (Set.range (fun k : Fin d ↦ f k.castSucc)))
      (X.zeroLocusSubschemeι {f (Fin.last d)}) = X.zeroLocusSubschemeι (Set.range f) := by
  exact (frameIntersection_existsUnique X d f).exists.choose_spec

private theorem frameCoefficientRestriction_isIso (P : PurityFiniteSetting.{u})
    {D X : Scheme.{u}} (c : D ⟶ X) [IsIso c] :
    IsIso (cupCoefficientRestriction P c) := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let : Category.{u + 1} A := inferInstance
  let : HasWeakSheafify (Scheme.ProEt.topology X) A := inferInstance
  let : HasWeakSheafify (Scheme.ProEt.topology D) A := inferInstance
  let M := ModuleCat.of P.Coefficient P.Coefficient
  let G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ c
  let H := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (inv c))
  let e : G ≅ H := NatIso.ofComponents (fun V ↦
    MorphismProperty.Over.isoMk (asIso (pullback.fst V.hom c)) (by
      change pullback.fst V.hom c ≫ (V.hom ≫ inv c) = pullback.snd V.hom c
      rw [← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id])) (by
      intro V W g
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift _ _ _ ≫ pullback.fst W.hom c =
        pullback.fst V.hom c ≫ g.left
      exact pullback.lift_fst _ _ _)
  have : G.IsCocontinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology D) :=
    Functor.IsCocontinuous.of_iso e.symm
  let E := Functor.pushforwardContinuousSheafificationCompatibility
    (G := G) A (Scheme.ProEt.topology X) (Scheme.ProEt.topology D)
  let α := ((constantSheafAdj (Scheme.ProEt.topology X) A
    (Scheme.ProEt.isTerminalMkId X)).homEquiv M
      ((lowerStar A c).obj ((constantSheaf (Scheme.ProEt.topology D) A).obj M))).symm
    ((toSheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj M)).app
      (op (G.obj (Scheme.ProEt.mk (𝟙 X)))))
  have hα : α = E.hom.app ((Functor.const D.ProEtᵒᵖ).obj M) := by
    apply ((constantSheafAdj (Scheme.ProEt.topology X) A
      (Scheme.ProEt.isTerminalMkId X)).homEquiv M _).injective
    dsimp only [α]
    rw [Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_unit]
    change _ = (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj M)).app (op (Scheme.ProEt.mk (𝟙 X))) ≫ _
    exact (congrArg (fun η ↦ η.app (op (Scheme.ProEt.mk (𝟙 X))))
      (G.toSheafify_pullbackSheafificationCompatibility A
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj M))).symm
  have : IsIso α := by rw [hα]; infer_instance
  change IsIso ((cupConstantIso P X).hom ≫ α ≫
    (lowerStar A c).map (cupConstantIso P D).inv)
  infer_instance

/-- An empty tuple cuts out the zero ideal, so its coefficient restriction is an
isomorphism. This also covers the empty scheme.
Source: def-pur-frame-class, c=0 (blueprint: def-pur-frame-class).
Proof: the ideal sheaf generated by an empty family is zero. Its quotient is the
original structure sheaf, so its closed subscheme is X. Restriction of constants
along this isomorphism is invertible, by the canonical constant comparison. -/
theorem frameEmptyRestriction_isIso (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (f : Fin 0 → Γ(X, ⊤)) :
    IsIso (cupCoefficientRestriction P (X.zeroLocusSubschemeι (Set.range f))) := by
  let c := X.zeroLocusSubschemeι (Set.range f)
  let r := Scheme.Hom.liftZeroLocusSubscheme (𝟙 X) (s := Set.range f) (fun t ht ↦ by
    obtain ⟨a, _⟩ := ht
    exact Fin.elim0 a)
  have hr : r ≫ c = 𝟙 X :=
    Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι _ _
  have : IsIso c := ⟨⟨r, by
    apply (cancel_mono c).mp
    simp only [Category.assoc, hr, Category.comp_id, Category.id_comp], hr⟩⟩
  exact frameCoefficientRestriction_isIso P c

/-- Form the empty supported product through a named functor. Substitution of the
coefficient equality occurs before applying the functor and its zero-shift comparison.
Source: def-pur-frame-class, empty product (blueprint: def-pur-frame-class). -/
def frameSingleUnit {C : Type v} [Category.{w} C] {D : Type*} [Category D]
    [HasShift D ℤ] (S : C ⥤ D) {L M N : C} (q : L ⟶ M) (hq : IsIso q) (h : L = N) :
    S.obj M ⟶ (S.obj N)⟦(0 : ℤ)⟧ := by
  subst N
  exact S.map (@inv _ _ _ _ q hq) ≫ (shiftFunctorZero D ℤ).inv.app _

/-- The supported unit for the zero ideal, with the usual zero-shift comparison.
Source: def-pur-frame-class, empty product (blueprint: def-pur-frame-class). -/
def frameEmptyClass (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (f : Fin 0 → Γ(X, ⊤)) :
    cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
      ((cupSingle P X).obj (P.frameTwist X 0)) 0 :=
  frameSingleUnit (cupSingle P X)
    (L := P.constant X) (N := P.frameTwist X 0)
    (M := (lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (X.zeroLocusSubschemeι (Set.range f))).obj
        (P.constant (X.zeroLocusSubscheme (Set.range f))))
    (cupCoefficientRestriction P (X.zeroLocusSubschemeι (Set.range f)))
    (P.frameEmptyRestriction_isIso X f) rfl

/-- Each new factor contributes degree two.
Source: def-pur-frame-class, degree addition (blueprint: def-pur-frame-class).
Proof: distribute multiplication by two over d+1 in the integers. -/
theorem frameDegreeNext (d : ℕ) : 2 * (d : ℤ) + 2 = 2 * ((d + 1 : ℕ) : ℤ) := by
  simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]

/-- The degree-zero sheaf specialization of the published supported cup. Both
inputs are bounded below via the existing singleFunctor into D⁺, so this calls
supportedCup directly. Its underlying degree-zero objects are definitionally
the ordinary single functor objects.
Source: def-pur-frame-class, ordered supported cup (blueprint: def-pur-frame-class). -/
def frameCupSheaves (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (s : X ⟶ Spec (.of P.field.k)) (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    (a b : ℤ) (α : cupSupportedHom P i ((cupSingle P X).obj F) a)
    (β : cupSupportedHom P j ((cupSingle P X).obj G) b) :
    cupSupportedHom P (cupIntersection i j)
      (cupTensorObject P X ((cupSingle P X).obj F) ((cupSingle P X).obj G)) (a + b) :=
  letI : X.Over (Spec (.of P.field.k)) := ⟨s⟩
  supportedCup P i j
    ⟨(cupSingle P X).obj F, ⟨0, by
      change DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.singleFunctor _ 0).obj _) 0
      infer_instance⟩⟩
    ⟨(cupSingle P X).obj G, ⟨0, by
      change DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.singleFunctor _ 0).obj _) 0
      infer_instance⟩⟩ a b α β

/-- Transport a supported cup along its source identification, coefficient map and
degree equality. This is ordinary composition and the shift functor.
Source: def-pur-frame-class, support intersection and degree/twist addition
(blueprint: def-pur-frame-class). -/
def frameCupTransport {C : Type v} [Category.{w} C] [HasShift C ℤ]
    {H N V T : C} (r : H ⟶ N) (a b : ℤ) (h : a = b)
    (γ : N ⟶ V⟦a⟧) (t : V ⟶ T) : H ⟶ T⟦b⟧ :=
  r ≫ γ ≫ t⟦a⟧' ≫ (eqToIso (congrArg (fun k : ℤ ↦ T⟦k⟧) h)).hom

/-- Append the final Kummer boundary to the prefix product. The published
cupComposite is exactly the body of supportedCup; both inputs here are sheaves
in degree zero and hence bounded below. It uses the inverse coefficient map,
the tensor of the two classes, and the fixed right-shift-first comparison.
Source: def-pur-frame-class, ordered left-associated product
(blueprint: def-pur-frame-class). -/
def frameCupNext (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (d : ℕ) (f : Fin (d + 1) → Γ(X, ⊤))
    (α : cupSupportedHom P
      (X.zeroLocusSubschemeι (Set.range (fun k : Fin d ↦ f k.castSucc)))
      ((cupSingle P X).obj (P.frameTwist X d)) (2 * (d : ℤ))) :
    cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
      ((cupSingle P X).obj (P.frameTwist X (d + 1))) (2 * ((d + 1 : ℕ) : ℤ)) :=
  frameCupTransport
    ((cupSingle P X).map
      (P.frameClosedCoefficientIso (X.zeroLocusSubschemeι (Set.range f))
        (cupIntersection
          (X.zeroLocusSubschemeι (Set.range (fun k : Fin d ↦ f k.castSucc)))
          (X.zeroLocusSubschemeι {f (Fin.last d)}))
        (frameIntersectionIso X d f) (frameIntersectionIso_over X d f)).hom)
    (2 * (d : ℤ) + 2) (2 * ((d + 1 : ℕ) : ℤ)) (frameDegreeNext d)
    (P.frameCupSheaves a
      (X.zeroLocusSubschemeι (Set.range (fun k : Fin d ↦ f k.castSucc)))
      (X.zeroLocusSubschemeι {f (Fin.last d)}) (P.frameTwist X d) (P.frameTwist X 1)
      (2 * (d : ℤ)) 2 α (P.frameBoundary X a (f (Fin.last d))))
    (P.frameTensorNext X d)

/-- The dependent left fold used for ordered frame products. Its recurrence is the
ordinary natural-number recursor, with the result family kept as a parameter.
Source: def-pur-frame-class, ordered product (blueprint: def-pur-frame-class). -/
def frameFold {A : ℕ → Type v} {H : (c : ℕ) → A c → Type w}
    (base : (f : A 0) → H 0 f) (takePrefix : (d : ℕ) → A (d + 1) → A d)
    (step : (d : ℕ) → (f : A (d + 1)) → H d (takePrefix d f) → H (d + 1) f) :
    (c : ℕ) → (f : A c) → H c f :=
  Nat.rec base (fun d previous f ↦ step d f (previous (takePrefix d f)))

/-- The explicit left fold: begin at the supported unit, then append f_1,...,f_c
in that order, using each function's own support boundary.
Source: def-pur-frame-class, displayed product (blueprint: def-pur-frame-class). -/
def frameBoundaryProduct (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) :
    (c : ℕ) → (f : Fin c → Γ(X, ⊤)) →
      cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
        ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ))
  := frameFold (fun f ↦ P.frameEmptyClass X f)
    (fun _d f k ↦ f k.castSucc) (fun d f α ↦ P.frameCupNext X a d f α)
/-- The class of the existing scheme-theoretic etale frame. The isPullback field
identifies the displayed zero subscheme with Z times_V U; e is merely etale and
is not required to be an open immersion. Smoothness and the pointwise Krull
codimension are the precise hypotheses of the node. The ambient relative dimension d
is independent of the coefficient level n; neither the dimension nor the smoothness
witnesses enter the boundary product. The dimension d is explicit: the
instance argument alone cannot determine it (its search would be stuck on d).
Source: blueprint main-20261015, def-pur-frame-class, displayed definition
(blueprint: def-pur-frame-class). -/
def frameClass (P : PurityFiniteSetting.{u}) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    (d : ℕ) [SmoothOfRelativeDimension d v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (_hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞)) (F : i.EtaleFrame c) :
    cupSupportedHom P (F.U.zeroLocusSubschemeι (Set.range F.f))
      ((cupSingle P F.U).obj (P.frameTwist F.U c)) (2 * (c : ℤ)) :=
  P.frameBoundaryProduct F.U (F.e ≫ v ≫ b) c F.f

end WeilConjectures.PurityFiniteSetting
