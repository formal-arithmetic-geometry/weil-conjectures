module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Extension across a point with valuation local ring

Source: Stacks Project, Morphisms of Schemes, Tag 0BX7, lemma-extend-across,
integral Noetherian specialization
(blueprint: lem-sfb-rational-map-extension-valuation-point).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- A morphism on a dense open of an integral Noetherian scheme to a proper target over
an arbitrary base extends across any point whose local ring is a valuation ring.
Source: Stacks Project, Morphisms of Schemes, Tag 0BX7, lemma-extend-across
(blueprint: lem-sfb-rational-map-extension-valuation-point).

Proof:
1. By lem-sc-scheme-sober and lem-sc-integral-scheme-stalks-in-function-field,
   the generic stalk K is the fraction field of A = O_{X,x}. The generic point lies in U.
   The affine formula in lem-weil-pbc-spec-local-ring-canonical-morphism identifies the
   composite Spec K → Spec A → X with the canonical generic-point morphism. Restricting
   f to Spec K gives h : Spec K → Y over S.
2. By lemma-nagata-proper-valuative-criterion-existence-api, properness of Y → S
   extends h to t : Spec A → Y over S, since A is a valuation ring.
3. Properness implies local finite type (def-weil-proper-morphism). Since X is locally
   Noetherian, lem-sfb-local-ring-map-spread spreads t to g : W → Y over S on an open
   neighbourhood W of x, with g agreeing with t on Spec A.
4. The open D = U ∩ W is integral, hence reduced. The generic-point morphism Spec K → D
   is dominant, and f and g agree after composition with it, by steps 1--3. Their maps
   to S agree. Relative separatedness of Y → S (def-weil-proper-morphism) and
   lem-sfb-relative-separated-dominant-ext therefore give equality on D.
5. Apply lem-weil-pbc-scheme-morphism-gluing to obtain F on V = U ∪ W. Its uniqueness
   clause shows that F is over S, since its composites to S agree on U and W.
   Thus V contains U and x, and the restriction of F to U is f. -/
theorem exists_extension_at_valuation_stalk
    (S X Y : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (a : X ⟶ S) (b : Y ⟶ S) [IsProper b]
    (U : X.Opens) (hU : Dense (U : Set X))
    (f : U.toScheme ⟶ Y) (hf : f ≫ b = U.ι ≫ a)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ (V : X.Opens) (hUV : U ≤ V), x ∈ V ∧
      ∃ F : V.toScheme ⟶ Y, F ≫ b = V.ι ≫ a ∧ X.homOfLE hUV ≫ F = f := by
  have hηU : genericPoint X ∈ U :=
    (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr
      (by simpa using hU.nonempty)
  let j := Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField))
  have hj : j ≫ X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
    X.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)
  let h := U.fromSpecStalkOfMem (genericPoint X) hηU ≫ f
  have hex : ValuativeCriterion.Existence b := by
    have hb : UniversallyClosed b := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hb
    exact hb.1
  let sq : ValuativeCommSq b :=
    { R := X.presheaf.stalk x
      K := X.functionField
      i₁ := h
      i₂ := X.fromSpecStalk x ≫ a
      commSq := ⟨by
        change h ≫ b = j ≫ X.fromSpecStalk x ≫ a
        rw [← Category.assoc, hj]
        simp [h, hf]⟩ }
  obtain ⟨t, ht, htb⟩ := (hex sq).exists_lift
  change j ≫ t = h at ht
  change t ≫ b = X.fromSpecStalk x ≫ a at htb
  obtain ⟨W, hxW, g, htg, hg⟩ := spread_out_of_isGermInjective' a b t htb
  have hηW : genericPoint X ∈ W :=
    ((genericPoint_spec X).specializes trivial).mem_open W.isOpen hxW
  have hWgen : W.fromSpecStalkOfMem (genericPoint X) hηW =
      j ≫ W.fromSpecStalkOfMem x hxW := by
    rw [← cancel_mono W.ι]
    simp [hj]
  let P : Bool → X.Opens := fun i ↦ if i then W else U
  let k : ∀ i, (P i).toScheme ⟶ Y := fun i ↦
    match i with
    | false => f
    | true => g
  have hηP : ∀ i, genericPoint X ∈ P i := by
    intro i
    cases i
    · exact hηU
    · exact hηW
  have hk : ∀ i, (P i).fromSpecStalkOfMem (genericPoint X) (hηP i) ≫ k i = h := by
    intro i
    cases i
    · rfl
    · change W.fromSpecStalkOfMem (genericPoint X) hηW ≫ g = h
      rw [hWgen, Category.assoc, ← htg, ht]
  have hkb : ∀ i, k i ≫ b = (P i).ι ≫ a := by
    intro i
    cases i
    · exact hf
    · exact hg
  have hkk : ∀ i l, X.homOfLE (inf_le_left : P i ⊓ P l ≤ P i) ≫ k i =
      X.homOfLE (inf_le_right : P i ⊓ P l ≤ P l) ≫ k l := by
    intro i l
    let D := P i ⊓ P l
    have hηD : genericPoint X ∈ D := ⟨hηP i, hηP l⟩
    have : Nonempty D := ⟨⟨_, hηD⟩⟩
    let iD := D.fromSpecStalkOfMem (genericPoint X) hηD
    have hi (Q : X.Opens) (hDQ : D ≤ Q) : iD ≫ X.homOfLE hDQ =
        Q.fromSpecStalkOfMem (genericPoint X) (hDQ hηD) := by
      rw [← cancel_mono Q.ι]
      simp [iD]
    have : IsDominant (X.fromSpecStalk (genericPoint X)) := by
      constructor
      intro y
      have hmem : genericPoint X ∈ Set.range (X.fromSpecStalk (genericPoint X)) :=
        ⟨IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)),
          Scheme.fromSpecStalk_closedPoint⟩
      exact closure_mono (Set.singleton_subset_iff.mpr hmem)
        ((genericPoint_spec X).symm ▸ Set.mem_univ y)
    have : IsDominant (iD ≫ D.ι) := by
      simpa [iD] using
        (inferInstance : IsDominant (X.fromSpecStalk (genericPoint X)))
    have : IsDominant iD := IsDominant.of_comp_of_isOpenImmersion (g := D.ι) iD
    refine ext_of_isDominant_of_isSeparated b ?_ iD ?_
    · simp [hkb]
    · rw [← Category.assoc, hi, ← Category.assoc, hi, hk, hk]
  let C := Scheme.Opens.iSupOpenCover P
  have compat : ∀ i l, CategoryTheory.Limits.pullback.fst (C.f i) (C.f l) ≫ k i =
      CategoryTheory.Limits.pullback.snd _ _ ≫ k l := by
    intro i l
    dsimp only [C, Scheme.Opens.iSupOpenCover]
    rw [← cancel_epi (isPullback_opens_inf_le (le_iSup P i)
      (le_iSup P l)).isoPullback.hom,
      CategoryTheory.IsPullback.isoPullback_hom_fst_assoc,
      CategoryTheory.IsPullback.isoPullback_hom_snd_assoc]
    exact hkk i l
  let F := C.glueMorphisms k compat
  have hF (i) : X.homOfLE (le_iSup P i) ≫ F = k i :=
    C.ι_glueMorphisms k compat i
  refine ⟨⨆ i, P i, le_iSup P false, ?_, F, ?_, hF false⟩
  · exact (le_iSup P true) hxW
  · apply C.hom_ext
    intro i
    change X.homOfLE (le_iSup P i) ≫ F ≫ b = _
    rw [← Category.assoc, hF, hkb]
    simp [C, Scheme.Opens.iSupOpenCover]

end AlgebraicGeometry
