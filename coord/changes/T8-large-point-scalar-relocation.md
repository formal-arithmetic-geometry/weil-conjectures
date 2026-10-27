# WeilConjectures.LocalFrobeniusLarge.stageScalar

## Reason

The quotient point-fibre construction needs the local scalar tower equation as a separately
provable step. That theorem needs the existing scalar constructions. Move their unchanged
block to a public prerequisite to prevent an import cycle. This is a dependency extraction,
not a split to evade a compile-time limit. No compile has timed out.

## Old

The following block belongs to Sheaf.Paper.LocalFrobeniusLargeCoefficients:

```lean
/-- Actual finite-field inclusion from its recorded small coefficient model.
Source: Weil II (1.1.1)d) (blueprint: def-weil-local-frobenius-trace). -/
def embedding (E : Padic.FiniteCoefficientFields l Ω) : Coefficient.{u} l Ω E →+* Ω :=
  E.val.subtype.comp (Shrink.algEquiv ℚ_[l] E.val).toRingHom

/-- The prescribed finite-stage point fibre, followed by H⁰ and coefficient extension.
Source: blueprint point-fibre convention (blueprint: def-weil-local-frobenius-trace). -/
def stageFibre (E : Padic.FiniteCoefficientFields l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) E ⥤
      ModuleCat.{u + 1} Ω :=
  pointRationalFibre D l hl (Coefficient.{u} l Ω E) ⋙
    DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω E) 0 ⋙
      ModuleCat.extendScalars (embedding l Ω E)

/-- H⁰ of the published normalized rational scalar comparison.
Source: blueprint scalar comparison (blueprint: def-weil-local-frobenius-trace). -/
def scalarCohomology {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) E) :=
  (DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω L) 0).mapIso
    ((pointRationalFibre D l hl (Coefficient.{u} l Ω L)).mapIso
      (eqToIso (congrArg (fun T ↦ T.obj K)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω
          (Spec (.of D.k))).exists.choose_spec.1 E L h))) ≪≫
      ((pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)).app K)) ≪≫
  (DerivedCategory.fieldDerivedHomologyIso
    (coefficientInclusion.{u} l Ω E L h).toRingHom 0).app
      ((pointRationalFibre D l hl (Coefficient.{u} l Ω E)).obj K).obj

private def tensorTower {R S : Type u} {T : Type v} [Field R] [Field S] [Field T]
    (f : R →+* S) (g : S →+* T) (q : R →+* T) (hq : q = g.comp f) :
    ModuleCat.extendScalars.{_, _, u} f ⋙ ModuleCat.extendScalars g ≅
      ModuleCat.extendScalars q := by
  let := f.toAlgebra
  let := g.toAlgebra
  letI := q.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun x ↦
    congrArg (fun k : R →+* T ↦ k x) hq)
  exact NatIso.ofComponents
    (fun M ↦ (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).toModuleIso)
    (fun {M N} k ↦ by
      apply ModuleCat.ExtendScalars.hom_ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add z w hz hw =>
        simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hz hw
      | tmul b m => rfl)

private theorem tensorTower_tmul {R S : Type u} {T : Type v} [Field R] [Field S] [Field T]
    (f : R →+* S) (g : S →+* T) (q : R →+* T) (hq : q = g.comp f)
    (M : ModuleCat.{u} R) (a : T) (b : S) (v : M) :
    (tensorTower f g q hq).hom.app M (a ⊗ₜ[S,g] (b ⊗ₜ[R,f] v)) =
      (a * g b) ⊗ₜ[R,q] v := by
  change (g b * a) ⊗ₜ[R,q] v = _
  rw [mul_comm]

private theorem tensor_normalization_unique
    {R S : Type u} {Ω : Type v} [Field R] [Field S] [Field Ω]
    (f : R →+* S) (g : S →+* Ω) (q : R →+* Ω)
    (A : ModuleCat.{u} R) (B : ModuleCat.{u} S)
    (n : B ≅ (ModuleCat.extendScalars f).obj A)
    (e e' : (ModuleCat.extendScalars g).obj B ⟶
      (ModuleCat.extendScalars q).obj A)
    (he : ∀ (a : Ω) (b : S) (v : A),
      e (a ⊗ₜ[S,g] (n.inv (b ⊗ₜ[R,f] v))) = (a * g b) ⊗ₜ[R,q] v)
    (he' : ∀ (a : Ω) (b : S) (v : A),
      e' (a ⊗ₜ[S,g] (n.inv (b ⊗ₜ[R,f] v))) = (a * g b) ⊗ₜ[R,q] v) :
    e = e' := by
  let c := (ModuleCat.extendScalars g).mapIso n.symm
  apply (cancel_epi c.hom).mp
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  let := f.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | tmul b v =>
    change e ((1 : Ω) ⊗ₜ[S,g] (n.inv (b ⊗ₜ[R,f] v))) =
      e' ((1 : Ω) ⊗ₜ[S,g] (n.inv (b ⊗ₜ[R,f] v)))
    rw [he, he']
  | add z w hz hw =>
    simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hz hw

omit [IsAlgClosure ℚ_[l] Ω] in
private theorem embedding_comp {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (embedding l Ω L).comp (coefficientInclusion l Ω E L h).toRingHom =
      embedding l Ω E := by
  ext x
  change L.val.subtype ((Shrink.algEquiv ℚ_[l] L.val)
    ((Shrink.algEquiv ℚ_[l] L.val).symm
      ((IntermediateField.inclusion h) ((Shrink.algEquiv ℚ_[l] E.val) x)))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

private def scalarTransport
    {C : Type a₁} [Category.{b₁} C] {B : Type a₂} [Category.{b₂} B]
    {A : Type a₃} [Category.{b₃} A] {D : Type a₄} [Category.{b₄} D]
    {E : Type a₅} [Category.{b₅} E] {F : Type a₆} [Category.{b₆} F]
    {T T' : C ⥤ B} (h : T = T') (P : B ⥤ D) (Q : C ⥤ A) (S : A ⥤ D)
    (a : T' ⋙ P ≅ Q ⋙ S) (H : D ⥤ E) (J : A ⥤ F) (G : F ⥤ E)
    (b : S ⋙ H ≅ J ⋙ G) : T ⋙ P ⋙ H ≅ Q ⋙ J ⋙ G :=
  Functor.isoWhiskerRight (Functor.isoWhiskerRight (eqToIso h) P ≪≫ a) H ≪≫
    Functor.isoWhiskerLeft Q b

private theorem scalarTransport_app
    {C : Type a₁} [Category.{b₁} C] {B : Type a₂} [Category.{b₂} B]
    {A : Type a₃} [Category.{b₃} A] {D : Type a₄} [Category.{b₄} D]
    {E : Type a₅} [Category.{b₅} E] {F : Type a₆} [Category.{b₆} F]
    {T T' : C ⥤ B} (h : T = T') (P : B ⥤ D) (Q : C ⥤ A) (S : A ⥤ D)
    (a : T' ⋙ P ≅ Q ⋙ S) (H : D ⥤ E) (J : A ⥤ F) (G : F ⥤ E)
    (b : S ⋙ H ≅ J ⋙ G) (K : C) :
    (scalarTransport h P Q S a H J G b).app K =
      H.mapIso (P.mapIso (eqToIso (congrArg (fun T : C ⥤ B ↦ T.obj K) h)) ≪≫
        a.app K) ≪≫ b.app (Q.obj K) := by
  subst T'
  unfold scalarTransport
  apply Iso.ext
  simp only [Iso.app_hom, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Functor.mapIso_hom]

private def scalarTransportComponents
    {C : Type a₁} [Category.{b₁} C] {B : Type a₂} [Category.{b₂} B]
    {A : Type a₃} [Category.{b₃} A] {D : Type a₄} [Category.{b₄} D]
    {E : Type a₅} [Category.{b₅} E] {F : Type a₆} [Category.{b₆} F]
    {T T' : C ⥤ B} (h : T = T') (P : B ⥤ D) (Q : C ⥤ A) (S : A ⥤ D)
    (a : T' ⋙ P ≅ Q ⋙ S) (H : D ⥤ E) (J : A ⥤ F) (G : F ⥤ E)
    (b : S ⋙ H ≅ J ⋙ G) : T ⋙ P ⋙ H ≅ Q ⋙ J ⋙ G :=
  NatIso.ofComponents
    (fun K ↦ H.mapIso (P.mapIso
      (eqToIso (congrArg (fun T : C ⥤ B ↦ T.obj K) h)) ≪≫ a.app K) ≪≫ b.app (Q.obj K))
    (fun {K L} f ↦ by
      have hn := (scalarTransport h P Q S a H J G b).hom.naturality f
      change _ ≫ ((scalarTransport h P Q S a H J G b).app L).hom =
        ((scalarTransport h P Q S a H J G b).app K).hom ≫ _ at hn
      simpa only [scalarTransport_app] using hn)

private def scalarCohomologyNat {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  scalarTransportComponents
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω
      (Spec (.of D.k))).exists.choose_spec.1 E L h)
    (pointRationalFibre D l hl (Coefficient.{u} l Ω L))
    (pointRationalFibre D l hl (Coefficient.{u} l Ω E))
    (DerivedCategory.pointFdScalarExtension (coefficientInclusion l Ω E L h).toRingHom)
    (pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h))
    (DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω L) 0)
    (DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω E) 0)
    (ModuleCat.extendScalars (coefficientInclusion l Ω E L h).toRingHom)
    (Functor.isoWhiskerLeft (DerivedCategory.pointFiniteDimensional
      (Coefficient.{u} l Ω E)).ι
        (DerivedCategory.fieldDerivedHomologyIso
          (coefficientInclusion.{u} l Ω E L h).toRingHom 0))

private theorem scalarCohomologyNat_app
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) E) :
    (scalarCohomologyNat D l hl Ω h).app K = scalarCohomology D l hl Ω h K := by
  rfl

attribute [local irreducible] scalarCohomology scalarCohomologyNat

private def comparison
    {C : Type w} [Category.{w'} C] {D : Type z} [Category.{z'} D]
    {R S : Type u} {Ω : Type v} [Field R] [Field S] [Field Ω]
    (f : R →+* S) (g : S →+* Ω) (q : R →+* Ω) (hq : q = g.comp f)
    (U : C ⥤ ModuleCat.{u} R) (V : D ⥤ ModuleCat.{u} S) (T : C ⥤ D)
    (n : T ⋙ V ≅ U ⋙ ModuleCat.extendScalars f) :
    T ⋙ V ⋙ ModuleCat.extendScalars g ≅ U ⋙ ModuleCat.extendScalars q :=
  Functor.isoWhiskerRight n (ModuleCat.extendScalars g) ≪≫
    Functor.isoWhiskerLeft U (tensorTower f g q hq)

private theorem comparison_tmul
    {C : Type w} [Category.{w'} C] {D : Type z} [Category.{z'} D]
    {R S : Type u} {Ω : Type v} [Field R] [Field S] [Field Ω]
    (f : R →+* S) (g : S →+* Ω) (q : R →+* Ω) (hq : q = g.comp f)
    (U : C ⥤ ModuleCat.{u} R) (V : D ⥤ ModuleCat.{u} S) (T : C ⥤ D)
    (n : T ⋙ V ≅ U ⋙ ModuleCat.extendScalars f)
    (K : C) (a : Ω) (b : S) (v : U.obj K) :
    (comparison f g q hq U V T n).hom.app K
      (a ⊗ₜ[S,g] ((n.app K).inv (b ⊗ₜ[R,f] v))) = (a * g b) ⊗ₜ[R,q] v := by
  change (tensorTower f g q hq).hom.app (U.obj K)
    ((ModuleCat.extendScalars g).map ((n.app K).hom)
      (a ⊗ₜ[S,g] ((n.app K).inv (b ⊗ₜ[R,f] v)))) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  have hn : (n.app K).hom ((n.app K).inv (b ⊗ₜ[R,f] v)) = b ⊗ₜ[R,f] v := by
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using
      ConcreteCategory.congr_hom (n.app K).inv_hom_id (b ⊗ₜ[R,f] v)
  rw [hn]
  exact tensorTower_tmul f g q hq (U.obj K) a b v

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] comparison

/-- Tensor flattening fixes the scalar comparison uniquely, also for identity inclusions.
Source: Weil II (1.1.1)d); BS 6.8.4(4)
(blueprint: def-weil-local-frobenius-trace).
Proof: apply H⁰ to the normalized sections/scalar square, then extend to Ω. Flatten
Ω tensor_L (L tensor_E V) by a tensor (b tensor v) ↦ a b tensor v. Its inverse sends
a tensor v to a tensor (1 tensor v). Balanced relations and tensor generation give
naturality and uniqueness. The coefficient inclusions commute with the Shrink equivalences. -/
theorem stageScalar_existsUnique {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    ∃! e : GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω (Spec (.of D.k))
        E L h ⋙ stageFibre D l hl Ω L ≅ stageFibre D l hl Ω E,
      ∀ (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) E)
        (a : Ω) (b : Coefficient.{u} l Ω L)
        (v : (DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω E) 0).obj
          ((pointRationalFibre D l hl (Coefficient.{u} l Ω E)).obj K)),
        e.hom.app K (a ⊗ₜ[Coefficient.{u} l Ω L, embedding l Ω L]
          ((scalarCohomology D l hl Ω h K).inv
            (b ⊗ₜ[Coefficient.{u} l Ω E, (coefficientInclusion l Ω E L h).toRingHom] v))) =
          (a * embedding l Ω L b) ⊗ₜ[Coefficient.{u} l Ω E, embedding l Ω E] v := by
  let U : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) E ⥤
      ModuleCat.{u} (Coefficient.{u} l Ω E) := pointRationalFibre D l hl (Coefficient.{u} l Ω E) ⋙
    DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω E) 0
  let V : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) L ⥤
      ModuleCat.{u} (Coefficient.{u} l Ω L) := pointRationalFibre D l hl (Coefficient.{u} l Ω L) ⋙
    DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω L) 0
  let T := GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω (Spec (.of D.k)) E L h
  let n := scalarCohomologyNat D l hl Ω h
  let e := comparison (coefficientInclusion l Ω E L h).toRingHom
    (embedding l Ω L) (embedding l Ω E) (embedding_comp l Ω h).symm U V T n
  have he := comparison_tmul (coefficientInclusion l Ω E L h).toRingHom
    (embedding l Ω L) (embedding l Ω E) (embedding_comp l Ω h).symm U V T n
  refine ⟨e, ?_, ?_⟩
  · intro K a b v
    have hk := he K a b v
    rw [scalarCohomologyNat_app] at hk
    exact hk
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    exact tensor_normalization_unique
      (coefficientInclusion l Ω E L h).toRingHom (embedding l Ω L) (embedding l Ω E)
      _ _ (scalarCohomology D l hl Ω h K) _ _ (he' K)
      (by
        intro a b v
        have hk := he K a b v
        rw [scalarCohomologyNat_app] at hk
        exact hk)

/-- The uniquely tensor-normalized scalar comparison.
Source: Weil II (1.1.1)d) (blueprint: def-weil-local-frobenius-trace). -/
def stageScalar {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  (stageScalar_existsUnique D l hl Ω h).exists.choose

attribute [local irreducible] stageScalar


```

## New

The exact block above, with identical declaration names, signatures, attributes and bodies,
belongs to Sheaf.Paper.LocalFrobeniusLargeScalarTower. The original module publicly imports
that module and retains both previous public imports. Its quotient proof privately imports StageSystem.Const; the scalar prerequisites and local tower
theorem share the same new publicly imported module. All existing
public scalar definitions, including embedding, stageFibre, scalarCohomology,
stageScalar_existsUnique and stageScalar, remain visible with the same full names.
The new tower theorem states only the equality between successive scalar comparisons.
pointFibre_existsUnique is proved by actual quotient descent and heterogeneous extensionality.
No target statement or mathematical definition changes; no target statement review reopens.

## Users

The downstream scan lists five modules. The only direct external users of the relocated
names are the three stageFibre and twelve embedding mentions in CompletedLocalFibreComparisonData.
Every moved data body and public type is identical, so no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | T8 | Reexports scalar API; proves quotient descent. |
| Sheaf.Paper.LocalFrobeniusLargeScalarTower | new in this delivery | Identical scalar data and proofs, plus the local scalar coherence theorem. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | C7 | Same API and data; unchanged. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Same API and data; unchanged. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed | Same embedding and stageFibre; unchanged. |
| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | B4 | Same API and data; unchanged. |
| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | Q1 | Same API and data; unchanged. |

## Status

landed 20261025T203254-L-2798812 2026-10-25 (merge of deliver/T8/Sheaf.Paper.LocalFrobeniusLargeCoefficients)
