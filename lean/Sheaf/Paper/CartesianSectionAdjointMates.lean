module

public import Sheaf.SixFunctors.FiniteAdjunctionSystemData
public import Sheaf.Paper.CartesianSectionData
import Sheaf.Paper.NormalizedSupportEtalePresentation

/-! # Adjoint mates on cartesian derived sections

Source: current blueprint, lem-coef-finite-exceptional.proof, paragraphs 1--3;
ordinary strict-system refinement of prop-coef-integral-exceptional-adjoint
(blueprint: lem-coef-cartesian-section-adjoint-mates).

The existing full domain has separate finite-Tor bounds at each positive level.
The natural number n denotes the positive coefficient exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FiniteAdjunctionDiagram
namespace WeilConjectures.CartesianSectionAdjoint

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- Construction from an ambient ordinary etale-system adjunction and actual site
comparison. The inverse image and total derived direct image are the recorded
sequence-site functors, rather than arbitrary levelwise lifts. The last equation
identifies the restricted Hom bijection with the composite of these adjunctions.
Source: ordinary strict-system refinement, proof steps 1--3; Zheng 4.10, 5.22
(blueprint: lem-coef-cartesian-section-adjoint-mates). -/
structure EtaleOrigin
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    (r : Realization l E D hl f c SX SZ SY) where
  source : CartesianSectionData.Representability l E (X ↘ Spec (.of D.k))
  target : CartesianSectionData.Representability l E (Y ↘ Spec (.of D.k))
  support : Etale.SystemProjection.Support c (SystemInternalHom.coefficients l E)
  right : SystemInternalHom.Et l E Y ⥤ SystemInternalHom.Et l E X
  adjunction : support.F ⊣ right
  leftComparison : r.F ⋙ (domain l E Y).ι ⋙ target.comparison.R ≅
    (domain l E X).ι ⋙ source.comparison.R ⋙ support.F
  rightComparison : r.G ⋙ (domain l E X).ι ≅
    (domain l E Y).ι ⋙ target.comparison.R ⋙ right ⋙ source.comparison.P
  counitIso : ∀ M : (domain l E X).FullSubcategory,
    IsIso (source.comparison.derivedAdjunction.counit.app M.obj)
  transpose : ∀ (M : (domain l E X).FullSubcategory)
    (N : (domain l E Y).FullSubcategory) (h : r.F.obj M ⟶ N),
    (r.adjunction.homEquiv M N h).hom =
      (@inv _ _ _ _ (source.comparison.derivedAdjunction.counit.app M.obj) (counitIso M)) ≫
        source.comparison.P.map
          (adjunction.homEquiv _ _
            (leftComparison.inv.app M ≫ target.comparison.R.map h.hom)) ≫
        rightComparison.inv.app N


/-- Ordinary mates of every specified transformation of actual compact-support
functors, with their counit-compatible finite evaluations. A geometric compositor
is one such transformation (the other functor can be a composite).
Source: final ordinary-system paragraph; Stacks 07A7
(blueprint: lem-coef-cartesian-section-adjoint-mates). -/
def MateEvaluation
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    (r : Realization l E D hl f c SX SZ SY) : Prop :=
  ∀ (F' : (domain l E X).FullSubcategory ⥤ (domain l E Y).FullSubcategory)
    (G' : (domain l E Y).FullSubcategory ⥤ (domain l E X).FullSubcategory)
    (a' : F' ⊣ G') (α : r.F ⟶ F') (n : ℕ)
    (Fn : (FiniteExceptional.domain l E X n).FullSubcategory ⥤
      (FiniteExceptional.domain l E Y n).FullSubcategory)
    (Gn : (FiniteExceptional.domain l E Y n).FullSubcategory ⥤
      (FiniteExceptional.domain l E X n).FullSubcategory)
    (an : Fn ⊣ Gn)
    (left : F' ⋙ evaluation l E Y n ≅ evaluation l E X n ⋙ Fn)
    (right : G' ⋙ evaluation l E X n ≅ evaluation l E Y n ⋙ Gn)
    (αn : FiniteExceptional.F l E D hl f c n ⟶ Fn),
    (∀ N : (domain l E Y).FullSubcategory,
      left.hom.app (G'.obj N) ≫ Fn.map (right.hom.app N) ≫
        an.counit.app ((evaluation l E Y n).obj N) =
          (evaluation l E Y n).map (a'.counit.app N)) →
    (∀ M : (domain l E X).FullSubcategory,
      (evaluation l E Y n).map (α.app M) ≫ left.hom.app M =
        (r.supportEvaluation n).hom.app M ≫ αn.app ((evaluation l E X n).obj M)) →
    (∀ N : (domain l E Y).FullSubcategory,
      (evaluation l E X n).map ((conjugateEquiv a' r.adjunction α).app N) ≫
        (r.exceptionalEvaluation n).hom.app N =
      right.hom.app N ≫
        (conjugateEquiv an (FiniteExceptional.adjunction l E D hl f c n) αn).app
          ((evaluation l E Y n).obj N)) ∧
    (conjugateEquiv a' r.adjunction).symm (conjugateEquiv a' r.adjunction α) = α

private theorem realization_etale_origin
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    (r : Realization l E D hl f c SX SZ SY) :
    Nonempty (EtaleOrigin l E D hl f c r) := by
  obtain ⟨source, target, support, right, adj, left, hc, preserves, a, ha⟩ :=
    normalizedSupportEtalePresentation l E D hl f c r.support r.F r.supportIso
  let e := r.adjunction.rightAdjointUniq a
  refine ⟨{
    source := source
    target := target
    support := support
    right := right
    adjunction := adj
    leftComparison := left
    rightComparison := Functor.isoWhiskerRight e (domain l E X).ι
    counitIso := hc
    transpose := ?_ }⟩
  intro M N h
  have he : r.adjunction.homEquiv M N h ≫ e.hom.app N = a.homEquiv M N h := by
    rw [r.adjunction.homEquiv_unit, a.homEquiv_unit, Category.assoc,
      e.hom.naturality, ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]
  change (r.adjunction.homEquiv M N h).hom =
    inv (source.comparison.derivedAdjunction.counit.app M.obj) ≫
      source.comparison.P.map
        (adj.homEquiv _ _ (left.inv.app M ≫ target.comparison.R.map h.hom)) ≫
      (e.inv.app N).hom
  rw [← Category.assoc, ← ha M N h, ← he]
  change _ = ((r.adjunction.homEquiv M N h).hom ≫ (e.hom.app N).hom) ≫
    (e.inv.app N).hom
  rw [Category.assoc]
  change _ = (r.adjunction.homEquiv M N h).hom ≫
    ((e.hom.app N) ≫ (e.inv.app N)).hom
  rw [e.hom_inv_id_app]
  exact (Category.comp_id _).symm

private theorem realization_mate_evaluation
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    (r : Realization l E D hl f c SX SZ SY) :
    MateEvaluation l E D hl f c r := by
  intro F' G' a' α n Fn Gn an left right αn hc hα
  refine ⟨?_, (conjugateEquiv a' r.adjunction).symm_apply_apply α⟩
  intro N
  apply ((FiniteExceptional.adjunction l E D hl f c n).homEquiv _ _).symm.injective
  change (FiniteExceptional.F l E D hl f c n).map _ ≫
      (FiniteExceptional.adjunction l E D hl f c n).counit.app _ =
    (FiniteExceptional.F l E D hl f c n).map _ ≫
      (FiniteExceptional.adjunction l E D hl f c n).counit.app _
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi ((r.supportEvaluation n).hom.app (G'.obj N))).1
  have hleft := (r.supportEvaluation n).hom.naturality
    ((conjugateEquiv a' r.adjunction α).app N)
  dsimp only [Functor.comp_map] at hleft
  rw [← reassoc_of% hleft, r.counit, ← (evaluation l E Y n).map_comp]
  rw [conjugateEquiv_counit]
  rw [(evaluation l E Y n).map_comp]
  rw [← hc N, reassoc_of% (hα (G'.obj N))]
  have hn := αn.naturality (right.hom.app N)
  rw [← reassoc_of% hn, conjugateEquiv_counit]

/-- The complete ordinary-system adjoint and mapping assertion. Existence of the
right adjoint, its etale origin, the canonical finite comparisons and Phi are all
conclusions. Unit/counit triangles are identities in the full system category.

Source: current blueprint lem-coef-finite-exceptional.proof, paragraphs 1--3;
ordinary refinement of prop-coef-integral-exceptional-adjoint, middle RHom
calculation and final paragraph (blueprint: lem-coef-cartesian-section-adjoint-mates).

Proof: the system compact-support projection theorem constructs the actual functor,
its evaluations and quotient comparisons on unbounded strict etale systems. The
etale-system adjoint theorem constructs its ambient right adjoint. Free insertion
and its sigma equation identify the evaluated right adjoint by representing Hom
bijections, including counits, units and the quotient mate b. Levelwise normalized
adjoint descent restricts to bounded constructible finite-Tor levels, without a
common bound, and transports through the actual etale/proetale comparison.
The finite exceptional theorem identifies b with the invertible counit transpose
and its cocycle. System internal-Hom representability and semilinear derived
sections identify the fiberwise mapping systems and their evaluations. The enriched
projection-adjunction theorem, applied to the actual projection and system counit,
constructs Phi and its inverse by the all-test tensor-Hom bijections. Yoneda proves
their inverse and naturality identities before finite evaluation. The finite Hom
identifications give the specified finite derived adjunction and its degree-zero
unit/counit formulas. Applying the actual derived-limit functor preserves those
already established inverse identities. Finally ordinary system transpose coherence
identifies mates of every specified transformation, including composition, and
identifies tensor-evaluation and tensor-Hom transposes with their finite evaluations.
No equality of system maps is deduced merely from equality of finite evaluations. -/
theorem cartesianSectionAdjointMates
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) :
    ∃ (SX : CoefficientDerivedSystemCalculus l E X)
      (SZ : CoefficientDerivedSystemCalculus l E c.Z)
      (SY : CoefficientDerivedSystemCalculus l E Y)
      (r : Realization l E D hl f c SX SZ SY)
      (g : Geometry l E f SX SY) (s : SectionsPush g)
      (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
      (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
      (Φ : Enriched r g s βX βY),
      Nonempty (EtaleOrigin l E D hl f c r) ∧
      MateEvaluation l E D hl f c r ∧
      (∀ (m n : ℕ) (h : n ≤ m), IsIso (FiniteExceptional.b l E D hl f c h)) ∧
      (∀ (M : (domain l E X).FullSubcategory) (N : (domain l E Y).FullSubcategory)
        (h : r.F.obj M ⟶ N),
        r.adjunction.homEquiv M N h = r.adjunction.unit.app M ≫ r.G.map h) ∧
      (∀ (M : (domain l E X).FullSubcategory) (N : (domain l E Y).FullSubcategory)
        (h : M ⟶ r.G.obj N),
        (r.adjunction.homEquiv M N).symm h = r.F.map h ≫ r.adjunction.counit.app N) ∧
      (∀ (M : (domain l E X).FullSubcategory) (N : (domain l E Y).FullSubcategory),
        IsIso (coefficientMappingLimit.{u+1}.map (Φ.iso.hom.app (op M, N))) ∧
        coefficientMappingLimit.{u+1}.map (Φ.iso.hom.app (op M, N)) ≫
          coefficientMappingLimit.{u+1}.map (Φ.iso.inv.app (op M, N)) = 𝟙 _ ∧
        coefficientMappingLimit.{u+1}.map (Φ.iso.inv.app (op M, N)) ≫
          coefficientMappingLimit.{u+1}.map (Φ.iso.hom.app (op M, N)) = 𝟙 _) ∧
      (∀ (W : Scheme.{u}) (_hW : W = X ∨ W = Y),
        ∀ A : SemilinearSections.Data.{u + 1, u, u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf.{u, u} l E W)
          (coefficientSequenceCommRingTransition.{u, u} l E W),
          SemilinearSections.SystemTensorTransposeCoherence.{u + 1, u, u}
            (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf.{u, u} l E W)
            (coefficientSequenceCommRingTransition.{u, u} l E W) A) := by
  obtain ⟨SX, SZ, SY, SS, _, _, _, _, βX, βY, r, g, s, aX, aY,
    _, _, ⟨Φ⟩, _, _⟩ := finiteAdjunctionDiagramRealization l E D hl f c
  refine ⟨SX, SZ, SY, r, g, s, βX, βY, Φ, ?_,
    realization_mate_evaluation l E D hl f c r, ?_, ?_, ?_, ?_, ?_⟩
  · exact realization_etale_origin l E D hl f c r
  · intro m n h
    exact (FiniteExceptional.finite_exceptional l E D hl f c).2.1 h
  · intro M N h
    exact r.adjunction.homEquiv_unit M N h
  · intro M N h
    exact r.adjunction.homEquiv_counit M N h
  · intro M N
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [← Functor.map_comp, Φ.iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    · rw [← Functor.map_comp, Φ.iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  · intro W hW A
    let Xo : Over (Spec (.of D.k)) := Over.mk (X ↘ Spec (.of D.k))
    let Yo : Over (Spec (.of D.k)) := Over.mk (Y ↘ Spec (.of D.k))
    let fo : Xo ⟶ Yo := Over.homMk f (comp_over f _)
    let : LocallyOfFiniteType Xo.hom := inferInstanceAs
      (LocallyOfFiniteType (X ↘ Spec (.of D.k)))
    let : QuasiCompact Xo.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))
    let : IsSeparated Xo.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of D.k)))
    let : LocallyOfFiniteType Yo.hom := inferInstanceAs
      (LocallyOfFiniteType (Y ↘ Spec (.of D.k)))
    let : QuasiCompact Yo.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))
    let : IsSeparated Yo.hom := inferInstanceAs (IsSeparated (Y ↘ Spec (.of D.k)))
    let : LocallyOfFiniteType fo.left := inferInstanceAs (LocallyOfFiniteType f)
    let : QuasiCompact fo.left := inferInstanceAs (QuasiCompact f)
    let : IsSeparated fo.left := inferInstanceAs (IsSeparated f)
    have hc := (systemAdjunctionTransposeCoherence l E D hl
      Xo Yo fo c).1 W
    have hW' : W = X ∨ W = Y ∨ W = c.Z := hW.imp_right Or.inl
    exact hc hW' true A

end WeilConjectures.CartesianSectionAdjoint
