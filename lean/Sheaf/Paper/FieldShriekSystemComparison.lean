module

public import Sheaf.Paper.FieldShriekSystemEvaluation
public import Sheaf.Paper.FieldShriekSupportEvaluation
public import Sheaf.Paper.FieldShriekSystemFiniteLaws
public import Sheaf.Paper.FieldShriekSystemMixed
public import Sheaf.Paper.FieldShriekSystemCoherence
import Sheaf.SecSmoothPurity.ReductionDirectImage
import Sheaf.Paper.FieldShriekSystemRealization
import Sheaf.Paper.FieldShriekSystemCocycle
import Sheaf.Paper.FieldShriekSystemMixedCompatibility

/-! # Coherent compact-support comparison on coefficient systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: lem-sp-field-shriek-system-comparison).

All arrows below live in the ordinary derived category of the ringed sequence site.
The recorded section-preserving equivalence identifies this with the original strict
tower category. Index n denotes positive exponent n+1. The structures package the
specified constructions and their laws as conclusions, rather than assuming the
comparison or choosing a lift of its finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] coefficientMap HasDerivedCategory.standard

/-- Invertibility on the recorded normalized full subcategory.
Source: blueprint (2), finite isomorphisms and conservativity
(blueprint: lem-sp-field-shriek-system-comparison). -/
structure InvertibilityLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  invertible : ∀ (E F : Index P) (h : E ≤ F)
    (M : SpTowerShriek.D P.coefficients.l E.val X), normalized P D E X M →
    IsIso ((comparison P D h c).app M)

/-- The complete system comparison assertion, retaining every clause.
Source: blueprint (2), all comparison clauses
(blueprint: lem-sp-field-shriek-system-comparison). -/
structure Laws (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    extends InvertibilityLaw P D c, MixedLaw P D c, CoherenceLaw P D c

/-- The specified natural isomorphism on the recorded normalized full subcategory.
Its forward morphism is literally the proper/open word, not an unspecified isomorphism.
Source: blueprint (2), b : C_Y P_A isomorphic to P_B C_X
(blueprint: lem-sp-field-shriek-system-comparison). -/
def iso (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (l : Laws P D c) {E F : Index P} (h : E ≤ F) :
    (normalized P D E X).ι ⋙
        (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c ⋙
          (D.scalars E F h Y).T) ≅
      (normalized P D E X).ι ⋙
        ((D.scalars E F h X).T ⋙
          SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c) :=
  NatIso.ofComponents
    (fun M ↦ @asIso _ _ _ _ ((comparison P D h c).app M.obj)
      (l.invertible E F h M.obj M.property))
    (fun v ↦ (comparison P D h c).naturality v.hom)

private theorem invertible_of_evaluation_square
    {C : Type*} [Category C] {A B D E F G : C}
    (f : A ⟶ B) (a : A ⟶ D) (a' : D ⟶ E) (b : B ⟶ F) (b' : F ⟶ G)
    (g : E ⟶ G) (ha : IsIso a) (ha' : IsIso a') (hb : IsIso b) (hb' : IsIso b')
    (hg : IsIso g) (h : f ≫ b ≫ b' = a ≫ a' ≫ g) : IsIso f := by
  have := ha
  have := ha'
  have := hb
  have := hb'
  have := hg
  have : IsIso (f ≫ b ≫ b') := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right f (b ≫ b')

private theorem ell_torsion (E : Index P) (n : ℕ) :
    ∃ a : ℕ, ∀ x : SpTowerShriek.R P.coefficients.l E.val n,
      (P.coefficients.l ^ a) • x = 0 := by
  refine ⟨n + 1, fun x ↦ ?_⟩
  have h : ((P.coefficients.l ^ (n + 1) : ℕ) :
      SpTowerShriek.R P.coefficients.l E.val n) = 0 := by
    have hz := (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (I := spEllIdeal P.coefficients.l E.val)
        (Ideal.subset_span (Set.mem_singleton
          (P.coefficients.l : Padic.coefficientExtensionIntegers P.coefficients.l E.val)))
        (n + 1)))
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hz
  rw [nsmul_eq_mul, h, zero_mul]

private theorem comparison_invertible (D : Models P)
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (c : Compactification f)
    (e : EvaluationLaw P D c) : InvertibilityLaw P D c := by
  have : Fact P.field.p.Prime := ⟨P.field.prime⟩
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
  have : CharP P.field.k P.field.p :=
    charP_of_injective_algebraMap' P.field.k₀ P.field.p
  refine ⟨fun E F h M hM ↦ ?_⟩
  apply (D.base F).calculus Y |>.detects
  intro n
  let r := SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
    ((D.coordinates E).abelian X)
  let K := r.inverse.obj M
  have hK := hM.1.1 n
  obtain ⟨a, b, _, hv⟩ := hK.1
  have hb : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X
        (SpTowerShriek.R P.coefficients.l E.val n))) i).obj
          ((spDerivedCoefficientEvaluation P.coefficients.l E.val X
            ((D.coordinates E).abelian X) n).obj K))} := by
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hv i (Or.inl h))),
      le_of_not_gt (fun h ↦ hi (hv i (Or.inr h)))⟩
  have hi := (reductionDirectImage_isIso P.coefficients.l P.field.p P.field.prime.pos
    P.coefficients.different.symm P.field.k f c.i c.g c.comm.symm
    (ell_torsion P E n) (ell_torsion P F n) ((D.coefficients E F h).quotient n)
    ((spDerivedCoefficientEvaluation P.coefficients.l E.val X
      ((D.coordinates E).abelian X) n).obj K) hb hK.2.1 hK.2.2).1
  let z : (SpTowerShriek.Ev P.coefficients.l E.val X n).obj M ≅
      (spDerivedCoefficientEvaluation P.coefficients.l E.val X
        ((D.coordinates E).abelian X) n).obj K :=
    ((SpTowerShriek.Ev P.coefficients.l E.val X n).mapIso (r.counitIso.app M)).symm ≪≫
      (SpTowerCalculus.levelComparison P.coefficients.l E.val (D.base E)
        (D.coordinates E) X n).app K
  have hfinite : IsIso ((reductionDirectImageComparison ((D.coefficients E F h).quotient n)
      c.i c.g).app ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M)) :=
    (NatTrans.isIso_app_iff_of_iso
      (reductionDirectImageComparison ((D.coefficients E F h).quotient n) c.i c.g) z).mpr hi
  exact invertible_of_evaluation_square
    ((SpTowerShriek.Ev P.coefficients.l F.val Y n).map ((comparison P D h c).app M))
    ((e.scalarEvaluation E F h Y n).iso.hom.app _)
    ((scalarExtensionFunctor ((D.coefficients E F h).quotient n) Y).map
      ((supportEvaluation P D E c n (e.supportCoordinates E n)).hom.app M))
    ((supportEvaluation P D F c n (e.supportCoordinates F n)).hom.app _)
    ((reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val n) c.i c.g).map
      ((e.scalarEvaluation E F h X n).iso.hom.app M))
    ((reductionDirectImageComparison ((D.coefficients E F h).quotient n) c.i c.g).app
      ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M))
    ((e.scalarEvaluation E F h Y n).iso.app _).isIso_hom
    ((scalarExtensionFunctor ((D.coefficients E F h).quotient n) Y).mapIso
      ((supportEvaluation P D E c n (e.supportCoordinates E n)).app M)).isIso_hom
    ((supportEvaluation P D F c n (e.supportCoordinates F n)).app _).isIso_hom
    ((reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val n) c.i c.g).mapIso
      ((e.scalarEvaluation E F h X n).iso.app M)).isIso_hom
    hfinite (e.evaluation E F h n M)

/-- The proper/open coefficient comparison on ordinary derived strict systems is
invertible on normalized constructible towers and has the specified finite evaluations,
mixed quotient compatibility, and coefficient-extension composition and identity laws.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2)
(blueprint: lem-sp-field-shriek-system-comparison).

Proof: (1) On the fixed compactification use the actual geometric/scalar pullback
comparison on simultaneous section models. Take its proper adjunction mate; it is
the transpose of scalar extension of the proper counit
(lem-coef-semilinear-derived-sections).
(2) The inverse open-unit mate is the open tensor isomorphism. Its generator formula
is [x] tensor s mapped to [x tensor s], and the ringed-open total-tensor K-flat theorem
identifies it on the signed total complexes, including nonflat quotient maps
(lem-sf-open-tensor-normalization, lem-sf-ringed-slice-tensor-generators,
lem-sf-ringed-open-total-tensor-kflat).
(3) Compose the proper mate with proper image of this open map. Evaluation commutes
with the actual scalar and geometric adjunction transposes, so its evaluation is
exactly reductionDirectImageComparison (det-sp-tower-shriek-levels,
det-sp-reduction-direct-image).
(4) Each normalized constructible input has bounded constructible finite-Tor levels.
The finite rings are ell-primary and ell differs from the field characteristic.
The finite comparison is invertible, and joint conservativity of exact system
evaluation proves invertibility of this already constructed system map.
(5) On simultaneous flat-term K-flat representatives, the scalar/pullback squares
compose by balanced multiplication on nested scalar tensors. The canonical scalar
associators have exactly this normalization (lem-pur-system-scalar-coherence).
(6) Mate pasting gives composition and identity for the proper factors; the open
unit mate and its generator formula give the same laws for the open factors
(lem-weil-pbc-mate-pasting).
(7) Naturality moves the intermediate open factor past the second proper mate.
Substitution of the two factor cocycles gives the displayed composition equation
in the ordinary derived category of whole systems. Tensor unitors give identity.
(8) For n greater than or equal to m, the actual direct-image transition is the
finite proper mate followed by direct image of the input reduction. Both scalar
paths are the same quotient inclusion R_n to S_m. The finite coefficient cocycle
and naturality identify both reassociated comparison words with that composite.
This verifies the transition of the existing system map, without inferring equality
of system morphisms from evaluated equalities. Equal indices give the unitors. -/
theorem field_shriek_system_comparison
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f) :
    ∃ D : Models P, Nonempty (Laws P D c) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : LocallyOfFiniteType f := inferInstance
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of P.field.k))
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  obtain ⟨D, ⟨e⟩⟩ := field_shriek_system_realization P c
  obtain ⟨mixed, _⟩ := field_shriek_system_mixed P D X Y f c e
  obtain ⟨coherence⟩ := field_shriek_system_cocycle P D c
  exact ⟨D, ⟨{ toInvertibilityLaw := comparison_invertible P D X Y f c e
               toMixedLaw := mixed
               toCoherenceLaw := coherence }⟩⟩

end AlgebraicGeometry.ProEtale.FieldShriekSystem
