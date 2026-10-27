module

public import Sheaf.Paper.FiniteClopenDerivedDecomposition
public import Sheaf.Paper.FiniteClopenExceptionalRestriction
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.SmoothFiniteDualizingInverse
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # A smooth dualizing inverse with varying relative dimension

Source: blueprint main-20261015, sec-six-functors-basics/sk-def-purity-conv/
def-pur-section-invariant.md, final invertibility assertion
(blueprint: lem-pur-varying-dimension-dualizing-inverse).

The component equations prescribe both inverse maps, rather than just their objects.
Integral restriction data are comparisons of actual strict coefficient systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w c v ci vi
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The inverse-assembly assertion, with all its maps written out. `good` is the
recorded finite-Tor predicate; at field stages the ambient category already is Dbc.
This only packages the conclusion of this node and introduces no coefficient operation.
Source: blueprint section-invariant, finite-clopen inverse assembly, step 5
(blueprint: lem-pur-varying-dimension-dualizing-inverse). -/
def DualizingInverseAssembly
    {C : Type c} [Category.{v} C] {I : Type w}
    {Ci : I → Type ci} [∀ i, Category.{vi} (Ci i)]
    (tensor : C × C ⥤ C) (unit : C) (good : ObjectProperty C)
    (restriction : ∀ i, C ⥤ Ci i)
    (componentTensor : ∀ i, Ci i × Ci i ⥤ Ci i)
    (componentUnit : ∀ i, Ci i) (componentGood : ∀ i, ObjectProperty (Ci i))
    (omega : C) : Prop :=
  good omega ∧
  (∀ i, componentGood i ((restriction i).obj omega)) ∧
  (∃ Q : C, good Q ∧ Nonempty (tensor.obj (omega, Q) ≅ unit) ∧
    Nonempty (tensor.obj (Q, omega) ≅ unit)) ∧
  ∃ (t : ∀ i, tensor ⋙ restriction i ≅
      ((restriction i).prod (restriction i)) ⋙ componentTensor i)
    (z : ∀ i, (restriction i).obj unit ≅ componentUnit i),
    ∀ (Qi : ∀ i, Ci i), (∀ i, componentGood i (Qi i)) →
      ∀ (ei : ∀ i, (componentTensor i).obj ((restriction i).obj omega, Qi i) ≅
          componentUnit i)
        (ei' : ∀ i, (componentTensor i).obj (Qi i, (restriction i).obj omega) ≅
          componentUnit i),
        ∃ (Q : C), good Q ∧
          ∃ (e : tensor.obj (omega, Q) ≅ unit) (e' : tensor.obj (Q, omega) ≅ unit)
            (p : ∀ i, (restriction i).obj Q ≅ Qi i),
            (∀ i, (restriction i).map e.hom ≫ (z i).hom =
              (t i).hom.app (omega, Q) ≫
                (componentTensor i).map
                  (X := ((restriction i).obj omega, (restriction i).obj Q))
                  (Y := ((restriction i).obj omega, Qi i)) (𝟙 _, (p i).hom) ≫ (ei i).hom) ∧
            (∀ i, (restriction i).map e'.hom ≫ (z i).hom =
              (t i).hom.app (Q, omega) ≫
                (componentTensor i).map
                  (X := ((restriction i).obj Q, (restriction i).obj omega))
                  (Y := (Qi i, (restriction i).obj omega)) ((p i).hom, 𝟙 _) ≫ (ei' i).hom)

private theorem assemble_dualizing_inverse
    {C : Type c} [Category.{v} C] {I : Type w}
    {Ci : I → Type ci} [∀ i, Category.{vi} (Ci i)]
    (tensor : C × C ⥤ C) (unit : C) (good : ObjectProperty C)
    (restriction : ∀ i, C ⥤ Ci i)
    (componentTensor : ∀ i, Ci i × Ci i ⥤ Ci i)
    (componentUnit : ∀ i, Ci i) (componentGood : ∀ i, ObjectProperty (Ci i))
    (omega : C) [(Functor.pi' restriction).IsEquivalence]
    (hgood : ∀ K, good K ↔ ∀ i, componentGood i ((restriction i).obj K))
    (hiso : ∀ i {K L : Ci i}, (K ≅ L) → componentGood i K → componentGood i L)
    (t : ∀ i, tensor ⋙ restriction i ≅
      ((restriction i).prod (restriction i)) ⋙ componentTensor i)
    (z : ∀ i, (restriction i).obj unit ≅ componentUnit i)
    (hcomp : ∀ i, componentGood i ((restriction i).obj omega) ∧
      ∃ Qi, componentGood i Qi ∧
        Nonempty ((componentTensor i).obj ((restriction i).obj omega, Qi) ≅ componentUnit i) ∧
        Nonempty ((componentTensor i).obj (Qi, (restriction i).obj omega) ≅ componentUnit i)) :
    DualizingInverseAssembly tensor unit good restriction componentTensor componentUnit
      componentGood omega := by
  classical
  let F := Functor.pi' restriction
  have glue (Qi : ∀ i, Ci i) (hQi : ∀ i, componentGood i (Qi i))
      (ei : ∀ i, (componentTensor i).obj ((restriction i).obj omega, Qi i) ≅ componentUnit i)
      (ei' : ∀ i, (componentTensor i).obj (Qi i, (restriction i).obj omega) ≅ componentUnit i) :
      ∃ Q, good Q ∧
        ∃ (e : tensor.obj (omega, Q) ≅ unit) (e' : tensor.obj (Q, omega) ≅ unit)
          (p : ∀ i, (restriction i).obj Q ≅ Qi i),
          (∀ i, (restriction i).map e.hom ≫ (z i).hom =
            (t i).hom.app (omega, Q) ≫
              (componentTensor i).map
                (X := ((restriction i).obj omega, (restriction i).obj Q))
                (Y := ((restriction i).obj omega, Qi i)) (𝟙 _, (p i).hom) ≫ (ei i).hom) ∧
          (∀ i, (restriction i).map e'.hom ≫ (z i).hom =
            (t i).hom.app (Q, omega) ≫
              (componentTensor i).map
                (X := ((restriction i).obj Q, (restriction i).obj omega))
                (Y := (Qi i, (restriction i).obj omega)) ((p i).hom, 𝟙 _) ≫ (ei' i).hom) := by
    let Q := F.objPreimage Qi
    let p (i : I) : (restriction i).obj Q ≅ Qi i :=
      (Pi.eval Ci i).mapIso (F.objObjPreimageIso Qi)
    let a (i : I) : (restriction i).obj (tensor.obj (omega, Q)) ≅
        (restriction i).obj unit :=
      (t i).app (omega, Q) ≪≫
        (componentTensor i).mapIso ((Iso.refl _).prod (p i)) ≪≫ ei i ≪≫ (z i).symm
    let a' (i : I) : (restriction i).obj (tensor.obj (Q, omega)) ≅
        (restriction i).obj unit :=
      (t i).app (Q, omega) ≪≫
        (componentTensor i).mapIso ((p i).prod (Iso.refl _)) ≪≫ ei' i ≪≫ (z i).symm
    let e : tensor.obj (omega, Q) ≅ unit := F.preimageIso (Pi.isoMk a)
    let e' : tensor.obj (Q, omega) ≅ unit := F.preimageIso (Pi.isoMk a')
    refine ⟨Q, (hgood Q).mpr (fun i ↦ hiso i (p i).symm (hQi i)),
      e, e', p, ?_, ?_⟩
    · intro i
      have he : (restriction i).map e.hom = (a i).hom :=
        congrFun (F.map_preimage (Pi.isoMk a).hom) i
      rw [he]
      simp [a, Category.assoc]
    · intro i
      have he : (restriction i).map e'.hom = (a' i).hom :=
        congrFun (F.map_preimage (Pi.isoMk a').hom) i
      rw [he]
      simp [a', Category.assoc]
  refine ⟨(hgood omega).mpr (fun i ↦ (hcomp i).1), fun i ↦ (hcomp i).1, ?_, t, z, glue⟩
  choose Qi hQi hei hei' using fun i ↦ (hcomp i).2
  obtain ⟨Q, hQ, e, e', _⟩ := glue Qi hQi (fun i ↦ (hei i).some)
    (fun i ↦ (hei' i).some)
  exact ⟨Q, hQ, ⟨e⟩, ⟨e'⟩⟩

private theorem fiberDimension_on_smooth_open {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : X.Opens) (d : ℕ) [SmoothOfRelativeDimension d (W.ι ≫ g)]
    (x : X) (hx : x ∈ W) : topologicalKrullDimAt (g.asFiber x) = d := by
  let F := (g.fiberι (g x)) ⁻¹ᵁ W
  have hF : g.asFiber x ∈ F := by
    change g.fiberι _ (g.asFiber x) ∈ W
    rwa [Scheme.Hom.fiberι_asFiber]
  have hpb : IsPullback (g.fiberι (g x) ∣_ W)
      (F.ι ≫ g.fiberToSpecResidueField (g x))
      (W.ι ≫ g) (Y.fromSpecResidueField (g x)) :=
    (isPullback_morphismRestrict (g.fiberι (g x)) W).paste_vert
      (IsPullback.of_hasPullback _ _)
  have : SmoothOfRelativeDimension d (F.ι ≫ g.fiberToSpecResidueField (g x)) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback hpb inferInstance
  rw [← IsOpen.topologicalKrullDimAt_eq F.isOpen hF]
  exact @topologicalKrullDimAt_eq_of_smoothOfRelativeDimension _ _ _
    (F.ι ≫ g.fiberToSpecResidueField (g x)) d this ⟨_, hF⟩

private theorem smooth_dimension_on_open_immersion {T X Y : Scheme.{u}}
    (j : T ⟶ X) [IsOpenImmersion j] (g : X ⟶ Y) [Smooth g] (d : ℕ)
    (hU : ∀ x : T, topologicalKrullDimAt (g.asFiber (j x)) = d) :
    SmoothOfRelativeDimension d (j ≫ g) := by
  apply smoothOfRelativeDimension_of_forall_exists_mem
  intro x
  obtain ⟨A, W, -, -, hx, e, n, hn⟩ :=
    Smooth.exists_smoothOfRelativeDimension_resLE g (j x)
  have hW : SmoothOfRelativeDimension n (W.ι ≫ g) := by
    rw [← Scheme.Hom.resLE_comp_ι g e]
    simpa using (inferInstance : SmoothOfRelativeDimension (n + 0) (g.resLE A W e ≫ A.ι))
  have hnd : n = d := by
    exact_mod_cast (fiberDimension_on_smooth_open g W n (j x) hx).symm.trans (hU x)
  subst n
  let O := j ⁻¹ᵁ W
  refine ⟨O, hx, ?_⟩
  have hO : SmoothOfRelativeDimension (0 + d) ((j ∣_ W) ≫ (W.ι ≫ g)) :=
    inferInstance
  simpa only [Nat.zero_add, ← Category.assoc, morphismRestrict_ι] using hO

/-- The fibre-dimension loci are the finite clopen partition, including empty loci.
Source: Stacks 02G1 and blueprint section-invariant, proof steps 1--2
(blueprint: lem-pur-varying-dimension-dualizing-inverse).
Proof: smooth relative dimension is locally constant by
sbc-lem-smooth-relative-dimension-locally-constant. Every level set and its complement
are open. The source is quasi-compact because it is finite type over a field, so the
disjoint open cover has only finitely many nonempty members. Restriction is smooth,
and the local fibre dimension is unchanged on an open subscheme. Closed immersions
are finite type; composition preserves finite type. The restricted diagonal is a
base change of the original closed diagonal, proving separatedness. No separatedness
of either structure morphism and no section are used. The empty source gives the
empty index set. -/
theorem smooth_dimension_clopen_partition (P : PurityFiniteSetting.{u})
    (V B : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (V.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (V.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (B.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (B.left ↘ Spec (.of P.field.k))]
    (g : V.left ⟶ B.left) [g.IsOver (Spec (.of P.field.k))]
    [hsmooth : Smooth g] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    ∃ U : ℕ → V.left.Opens,
      (∀ d : ℕ, (U d : Set V.left) =
        {x | topologicalKrullDimAt (g.asFiber x) = (d : WithBot ℕ∞)}) ∧
      (Set.Finite {d : ℕ | (U d : Set V.left).Nonempty}) ∧
      (∀ d : ℕ, IsClosed (U d : Set V.left)) ∧
      (∀ d e : ℕ, d ≠ e → Disjoint (U d : Set V.left) (U e : Set V.left)) ∧
      (⋃ d : ℕ, (U d : Set V.left)) = Set.univ ∧
      ∀ d : ℕ, SmoothOfRelativeDimension d ((U d).ι ≫ g) ∧
        IsSeparated ((U d).ι ≫ g) ∧ LocallyOfFiniteType ((U d).ι ≫ g) ∧
        QuasiCompact ((U d).ι ≫ g) ∧
        LocallyOfFiniteType ((U d).ι ≫ V.hom) ∧ QuasiCompact ((U d).ι ≫ V.hom) := by
  classical
  have : LocallyOfFiniteType V.hom :=
    inferInstanceAs (LocallyOfFiniteType (V.left ↘ Spec (.of P.field.k)))
  have : QuasiCompact V.hom :=
    inferInstanceAs (QuasiCompact (V.left ↘ Spec (.of P.field.k)))
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  let f : V.left → WithBot ℕ∞ := fun x ↦ topologicalKrullDimAt (g.asFiber x)
  have hf : IsLocallyConstant f := Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber g
  let U : ℕ → V.left.Opens := fun d ↦ ⟨{x | f x = d}, hf.isOpen_fiber _⟩
  have hnat (x : V.left) : ∃ d : ℕ, f x = d := by
    obtain ⟨A, W, -, -, hx, e, n, hn⟩ :=
      Smooth.exists_smoothOfRelativeDimension_resLE g x
    have : SmoothOfRelativeDimension n (W.ι ≫ g) := by
      rw [← Scheme.Hom.resLE_comp_ι g e]
      simpa using (inferInstance : SmoothOfRelativeDimension (n + 0) (g.resLE A W e ≫ A.ι))
    exact ⟨n, fiberDimension_on_smooth_open g W n x hx⟩
  refine ⟨U, fun _ ↦ rfl, ?_, fun d ↦ hf.isClosed_fiber _, ?_, ?_, ?_⟩
  · have hinj : Function.Injective (fun d : ℕ ↦ (d : WithBot ℕ∞)) := by
      intro d e h
      change (d : WithBot ℕ∞) = e at h
      exact_mod_cast h
    apply (hf.range_finite.preimage hinj.injOn).subset
    rintro d ⟨x, hx⟩
    exact ⟨x, hx⟩
  · intro d e hde
    apply Set.disjoint_left.mpr
    intro x hx hy
    apply hde
    have h : (d : WithBot ℕ∞) = e := hx.symm.trans hy
    exact_mod_cast h
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨d, hd⟩ := hnat x
    exact Set.mem_iUnion.mpr ⟨d, hd⟩
  · intro d
    have hclosed : IsClosedImmersion (U d).ι :=
      IsClosedImmersion.of_isPreimmersion _ (by
        rw [Scheme.Opens.range_ι]
        exact hf.isClosed_fiber (d : WithBot ℕ∞))
    exact ⟨smooth_dimension_on_open_immersion (U d).ι g d (fun x ↦ x.property),
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem finiteGood_iso (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (n : ℕ)
    {K L : Scheme.proEtaleDerivedCategory T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))}
    (e : K ≅ L)
    (h : finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) T K) :
    finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) T L := by
  have hc : Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n) T L :=
    (Scheme.finiteTorsionConstructible P.field P.coefficients.l P.coefficients.different
      P.extension (n + 1) (Nat.succ_pos n) T).prop_of_iso e h.1
  obtain ⟨a, b, hab⟩ := h.2
  refine ⟨hc, a, b, hab.1, ?_⟩
  intro C D hC f hf hD M i hi
  obtain ⟨eC⟩ := hC
  exact hab.2 C D ⟨eC ≪≫ e.symm⟩ f hf hD M i hi

section Assembly
variable (P : PurityFiniteSetting.{u})
    (V B : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (V.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (V.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (B.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (B.left ↘ Spec (.of P.field.k))]
    (g : V.left ⟶ B.left) [g.IsOver (Spec (.of P.field.k))]
    [hsmooth : Smooth g] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    {I : Type w} [hfinite : Finite I]
    (Vi : I → Over (Spec (.of P.field.k)))
    [∀ i, LocallyOfFiniteType ((Vi i).left ↘ Spec (.of P.field.k))]
    [∀ i, QuasiCompact ((Vi i).left ↘ Spec (.of P.field.k))]
    (j : ∀ i, Vi i ⟶ V)
    [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hdisjoint : ∀ i i', i ≠ i' →
      Disjoint (Set.range (j i).left) (Set.range (j i').left))
    (hcover : (⋃ i, Set.range (j i).left) = Set.univ)
    (dimension : I → ℕ) (hinjective : Function.Injective dimension)
    (hnonempty : ∀ i, Nonempty (Vi i).left)
    (hdimension : ∀ i, Set.range (j i).left =
      {x | topologicalKrullDimAt (g.asFiber x) = (dimension i : WithBot ℕ∞)})

include hsmooth hfinite hdisjoint hcover hinjective hnonempty hdimension

set_option linter.unusedSectionVars false in
/-- Finite coefficients: the actual exceptional image of A_B has a two-sided
finite-Tor constructible inverse, with any prescribed component inverse maps.
The first family of comparisons identifies the restricted omega with omega_(g_i).
Source: blueprint section-invariant, proof steps 3--5
(blueprint: lem-pur-varying-dimension-dualizing-inverse).
Proof: use lem-pur-finite-clopen-exceptional-restriction at the coefficient unit.
On each pure-dimension locus, lem-pur-finite-setting-comparison-hypotheses supplies
the hypotheses of thm-asd-smooth-tensor. The shifted rank-one local system and its
dual are inverse by lem-pur-shifted-line-site-inverse. Reassemble using
lem-pur-finite-clopen-derived-decomposition: full faithfulness lifts the specified
evaluation maps and their inverses, and faithfulness checks both inverse identities.
The same equivalence detects every common cohomological and Tor interval.
Each component is precisely its labelled nonempty dimension locus. The empty
product clause supplies the unique inverse and maps when V is empty. -/
theorem varyingDimension_finite_dualizing_inverse (n : ℕ) :
    (∀ i, Nonempty
      ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj
          ((clopenFiniteExceptional P P.extension V B g n).obj
            (finiteConstantCoefficientObject P.coefficients.l P.extension B.left n)) ≅
        (clopenFiniteExceptional P P.extension (Vi i) B ((j i).left ≫ g) n).obj
          (finiteConstantCoefficientObject P.coefficients.l P.extension B.left n))) ∧
    DualizingInverseAssembly
      (finiteIntrinsicDerivedTensor P.coefficients.l P.extension V.left n)
      (finiteConstantCoefficientObject P.coefficients.l P.extension V.left n)
      (finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) V.left)
      (fun i ↦ finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
      (fun i ↦ finiteIntrinsicDerivedTensor P.coefficients.l P.extension (Vi i).left n)
      (fun i ↦ finiteConstantCoefficientObject P.coefficients.l P.extension (Vi i).left n)
      (fun i ↦ finiteTorConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) (Vi i).left)
      ((clopenFiniteExceptional P P.extension V B g n).obj
        (finiteConstantCoefficientObject P.coefficients.l P.extension B.left n)) ∧
    ∀ (K : Scheme.proEtaleDerivedCategory V.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)))
      (a b : ℤ), a ≤ b →
      (Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
        ∀ i, Scheme.proEtaleCohomologicalSupport
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) ⊆
            Set.Icc a b) ∧
      (Scheme.HasProEtaleTorAmplitude V.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) K a b ↔
        ∀ i, Scheme.HasProEtaleTorAmplitude (Vi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) a b) := by
  classical
  have : LocallyOfFiniteType V.hom :=
    inferInstanceAs (LocallyOfFiniteType (V.left ↘ Spec (.of P.field.k)))
  have : QuasiCompact V.hom :=
    inferInstanceAs (QuasiCompact (V.left ↘ Spec (.of P.field.k)))
  have : LocallyOfFiniteType B.hom :=
    inferInstanceAs (LocallyOfFiniteType (B.left ↘ Spec (.of P.field.k)))
  have : QuasiCompact B.hom :=
    inferInstanceAs (QuasiCompact (B.left ↘ Spec (.of P.field.k)))
  have := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have := QuasiCompact.compactSpace_of_compactSpace B.hom
  let cpt := HasCompactification.compactification g
  let R (i : I) :=
    ((P.finiteClopenExceptionalRestriction V B g Vi j hdisjoint hcover).2 cpt i).some
  let a (i : I) := (R i).base.finite n |>.app
    (clopenFiniteUnitAt P.coefficients.l P.extension B.left n)
  let r := fun i ↦ finiteDerivedPullback P.coefficients.l P.extension n (j i).left
  let t (i : I) :=
    ((P.finiteClopen_tensor_and_reduction V Vi j hdisjoint hcover i).1 n).some
  let z (i : I) :=
    ((P.finiteClopen_coefficient_units V Vi j hdisjoint hcover i).1 n).some
  let r₀ := fun i ↦
    clopenDerivedRestriction (j i).left (P.clopenRing V.left n false)
  choose c E hQ he using fun i ↦
    P.finiteClopen_finite_restriction_identification V Vi j hdisjoint hcover n i
  have : (Functor.pi' r₀).IsEquivalence :=
    (P.finiteClopen_unbounded_decomposition V Vi j hdisjoint hcover n false).1
  have : (Functor.pi' r).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (F := Functor.pi' r₀ ⋙ Functor.pi (fun i ↦ (E i).functor))
      (NatIso.pi' (fun i ↦ (he i).some))
  refine ⟨fun i ↦ ⟨a i⟩, ?_, ?_⟩
  · apply assemble_dualizing_inverse _ _ _ r _ _ _ _
      (fun K ↦ P.finiteClopen_finiteTor_iff V Vi j hdisjoint hcover n K)
      (fun i _ _ e h ↦ finiteGood_iso P (Vi i).left n e h) t z
    intro i
    have hrel : SmoothOfRelativeDimension (dimension i) ((j i).left ≫ g) :=
      smooth_dimension_on_open_immersion (j i).left g (dimension i) (fun x ↦ by
        have hx : (j i).left x ∈ Set.range (j i).left := Set.mem_range_self x
        rw [hdimension i] at hx
        exact hx)
    obtain ⟨hω, Q, hQ, ⟨e⟩, ⟨e'⟩⟩ :=
      P.smooth_finite_dualizing_inverse (Vi i) B ((j i).left ≫ g) (dimension i) n
    refine ⟨finiteGood_iso P (Vi i).left n (a i).symm hω, Q, hQ, ⟨?_⟩, ⟨?_⟩⟩
    · exact (finiteIntrinsicDerivedTensor P.coefficients.l P.extension (Vi i).left n).mapIso
        ((a i).prod (Iso.refl Q)) ≪≫ e
    · exact (finiteIntrinsicDerivedTensor P.coefficients.l P.extension (Vi i).left n).mapIso
        ((Iso.refl Q).prod (a i)) ≪≫ e'
  · intro K a b hab
    have H := P.finiteClopen_finite_bounds V Vi j hdisjoint hcover n K
    exact ⟨H.2.1 a b hab, H.2.2 a b hab⟩

/-- Integral and field coefficients, using coherent actual exceptional systems.
The identity-component record fixes one global exceptional functor; each component
record has exactly that global functor. Its integral and finite comparisons commute
with strict-system evaluation by the coherence equations of the recorded type.
Consequently its unit comparisons apply to this very global dualizing object.
Source: blueprint section-invariant, proof steps 3--5 and coefficient transports
(blueprint: lem-pur-varying-dimension-dualizing-inverse).
Proof: choose the common strict exceptional system and its clopen restriction
comparisons using lem-pur-finite-clopen-exceptional-restriction. Evaluating these
system maps and applying scalar restriction and the derived inverse limit gives
the integral comparisons. The finite smooth dualizing object on each dimension
locus is a shifted etale line. Its residue reduction is therefore a shifted line;
lem-pur-complete-residue-line-inverse supplies the derived-complete inverse and
both evaluation maps with Tor bounds uniform at every positive level. The clopen
equivalence glues arbitrary prescribed component inverses and their maps by full
faithfulness. Rationalize this pair; then take its image at any common finite
coefficient stage. Common bounds are detected at every reduction by the clopen
equivalence; the quantified interval is independent of the reduction index.
The tensor and unit operations are those on the same integral
representatives, so both inverse identities survive. At the algebraic closure a
finite compositum contains the finitely many component stages. The empty product
case gives the unit as its own inverse. No Tate orientation is used. -/
theorem varyingDimension_dualizing_inverse (cpt : Compactification g) :
    ∃ R : ClopenExceptionalAllCoefficients P V B V g cpt (𝟙 V),
      ∃ Ri : ∀ i, ClopenExceptionalAllCoefficients P V B (Vi i) g cpt (j i),
        (∀ i, (Ri i).base.integral = R.base.integral ∧
          (Ri i).base.rational = R.base.rational ∧
          (Ri i).action.functor = R.action.functor) ∧
        DualizingInverseAssembly
          (P.clopenIntegralTensor V) (P.clopenIntegralUnit V.left)
          (fun K ↦ finiteTorConstructibleIntegral P.coefficients.l P.extension V.left K.obj)
          (fun i ↦ P.clopenIntegralPullback (j i))
          (fun i ↦ P.clopenIntegralTensor (Vi i))
          (fun i ↦ P.clopenIntegralUnit (Vi i).left)
          (fun i K ↦ finiteTorConstructibleIntegral P.coefficients.l P.extension (Vi i).left K.obj)
          (R.base.integral.obj (P.clopenIntegralUnit B.left)) ∧
        DualizingInverseAssembly
          (P.clopenRationalTensor V) (P.clopenRationalUnit V.left) ⊤
          (fun i ↦ P.clopenRationalPullback (j i))
          (fun i ↦ P.clopenRationalTensor (Vi i))
          (fun i ↦ P.clopenRationalUnit (Vi i).left) (fun _ ↦ ⊤)
          (R.base.rational.obj (P.clopenRationalUnit B.left)) ∧
        (∀ A : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar,
          DualizingInverseAssembly
            (P.clopenCommonStageTensor V) (P.clopenCommonStageUnit V.left A) ⊤
            (fun i ↦ P.clopenCommonStagePullback (j i))
            (fun i ↦ P.clopenCommonStageTensor (Vi i))
            (fun i ↦ P.clopenCommonStageUnit (Vi i).left A) (fun _ ↦ ⊤)
            (R.action.functor.obj (P.clopenCommonStageUnit B.left A))) ∧
        ∀ (K : sfIntegralConstructibleCategory P.coefficients.l P.extension V.left)
          (a b : ℤ), a ≤ b →
          ((∀ n : ℕ, Scheme.proEtaleCohomologicalSupport
              ((scalarReductionDerivedExtension P.coefficients.l P.extension V.left n).obj
                K.obj) ⊆ Set.Icc a b) ↔
            ∀ (i : I) (n : ℕ), Scheme.proEtaleCohomologicalSupport
              ((scalarReductionDerivedExtension P.coefficients.l P.extension (Vi i).left n).obj
                ((P.clopenIntegralPullback (j i)).obj K).obj) ⊆ Set.Icc a b) ∧
          ((∀ n : ℕ, Scheme.HasProEtaleTorAmplitude V.left
              (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
              ((scalarReductionDerivedExtension P.coefficients.l P.extension V.left n).obj
                K.obj) a b) ↔
            ∀ (i : I) (n : ℕ), Scheme.HasProEtaleTorAmplitude (Vi i).left
              (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
              ((scalarReductionDerivedExtension P.coefficients.l P.extension (Vi i).left n).obj
                ((P.clopenIntegralPullback (j i)).obj K).obj) a b) := by
  sorry

end Assembly
end WeilConjectures.PurityFiniteSetting
