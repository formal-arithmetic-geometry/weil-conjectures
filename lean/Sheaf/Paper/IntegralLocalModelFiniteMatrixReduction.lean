module

public import Sheaf.Paper.IntegralMatrixModelData
import Sheaf.Paper.IntegralMatrixLocalResolution
import Sheaf.Paper.IntegralMatrixCohomology
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.FinitePresentation

/-! # Simultaneous finite matrix models for integral local reductions

Source: Stacks 093J, 093M, 06YQ, 06YY, 07A6.
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe r t w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
namespace IntegralMatrix

variable (l : ℕ) [Fact l.Prime] (E : Type r) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {C : Type r} [SmallCategory C] (J : GrothendieckTopology C)
variable [hD : ∀ (D : Type (r + 1)) [Category.{r} D] [Abelian D],
  HasDerivedCategory.{w} D]

omit hD in
private theorem finiteResidues (n : ℕ) : Finite (Residues l E n) := by
  obtain ⟨m, hm⟩ := (sp_coefficient_ideals_cofinal l E).2 (n + 1)
  have hf : Finite (Padic.coefficientExtensionRing l E m) := by
    by_cases hm0 : m = 0
    · subst m
      change Finite (_ ⧸ _ ^ 0)
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    · exact Padic.finite_coefficientExtensionRing l E m (Nat.one_le_iff_ne_zero.mpr hm0)
  let := hf
  have : Finite (WeilConjectures.CompletedSite.residue
      (Padic.coefficientExtensionIntegers l E)
      (l : Padic.coefficientExtensionIntegers l E) n) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hm)
  exact inferInstanceAs (Finite (ULift _))

omit hD in
private theorem finitePidResolution {A : Type r} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] (N : ModuleCat.{r} A) [Module.FinitePresentation A N] :
    ∃ (a b : ℕ) (d : Matrix (Fin b) (Fin a) A) (p : (Fin b → A) →ₗ[A] N),
      Function.Injective (Matrix.toLin' d) ∧
      Function.Exact (Matrix.toLin' d) p ∧ Function.Surjective p := by
  classical
  obtain ⟨b, _, p, _, hp, _⟩ := Module.FinitePresentation.exists_fin' A N
  obtain ⟨a, basis⟩ := Submodule.basisOfPid (Pi.basisFun A (Fin b)) (LinearMap.ker p)
  let f : (Fin a → A) →ₗ[A] (Fin b → A) :=
    (LinearMap.ker p).subtype.comp basis.equivFun.symm.toLinearMap
  refine ⟨a, b, LinearMap.toMatrix' f, p, ?_, ?_, hp⟩
  · rw [Matrix.toLin'_toMatrix']
    exact Subtype.val_injective.comp basis.equivFun.symm.injective
  · rw [Matrix.toLin'_toMatrix', LinearMap.exact_iff]
    symm
    change LinearMap.range f = LinearMap.ker p
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Submodule.range_subtype]

omit hD in
private theorem scalarFinitePresentation {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ) :
    Finite (scalarKernel l E d n) ∧ Finite (scalarCokernel l E d n) ∧
    Module.FinitePresentation (Residues l E n) (scalarKernel l E d n) ∧
    Module.FinitePresentation (Residues l E n) (scalarCokernel l E d n) := by
  let := finiteResidues l E n
  have hfc : Finite (scalarCokernel l E d n) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective (LinearMap.range
      (Matrix.toLin' (reduced l E d n))))
  let := hfc
  exact ⟨inferInstance, hfc,
    Module.finitePresentation_of_finite _ _, Module.finitePresentation_of_finite _ _⟩

omit hD in
private theorem isZero_of_local (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{r} R)
    (h : ∀ V : C, ∃ W : Sieve V, W ∈ J V ∧
      ∀ (U : C) (f : U ⟶ V), W f → IsZero (M.over U)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  ext V x
  obtain ⟨W, hW, hzero⟩ := h V.unop
  apply M.isSheaf.isSeparated V.unop W hW
  intro U f hf
  have hz := hzero U f hf
  have he := congrArg
    (fun g : M.over U ⟶ M.over U ↦ g.val.app (op (Over.mk (𝟙 U)))
      (M.val.map f.op x)) (hz.eq_of_src (𝟙 (M.over U)) 0)
  change M.val.map f.op x = 0 at he
  change M.val.map f.op x = M.val.map f.op 0
  rw [map_zero]
  exact he

/-- A single integral matrix computes every positive derived reduction, with the actual
quotient transitions and the finite constant kernel and cokernel cohomology.

Source: Stacks 093J, 093M, 0AUW, 06YQ, 0E8K, 06YY and 07A6; blueprint
sk-def-sp-normalized-towers, constructibility paragraph
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction).

Proof plan:
1. Resolve L[0] by a flat-term K-flat complex (lem-pc-kflat-resolution). Exact slice
restriction preserves K-flatness (lem-sfb-ringed-site-restriction-kflat). The normalized
pure-tensor comparison of lem-sfb-localized-site-tensor-restriction identifies restriction
of its reduction with reduction of its restriction, naturally in every quotient map.
2. The integer ring is a DVR (lem-weil-l-adic-extension-integers-dvr), hence Noetherian
(lem-weil-pbc-pid-noetherian-normal). The scalar finite-free resolution theorem
lem-sfb-scalar-finite-free-resolutions gives one injective matrix d and its cokernel N.
Exact constant realization (lem-weil-pbc-finite-type-constant-exact) and completion
flatness (lem-weil-pbc-completed-constant-sheaf-reduction, Stacks 093M) preserve this
sequence. Its last term is the supplied local model of L.
3. The resulting two-term free sheaf resolution is K-flat by
lem-sfb-ringed-finite-free-resolution-tensor. Derived change of rings computes every
reduction using this same resolution. The basis formulas send b tensor (a_i) to (ba_i),
identifying its differential with the reduction of d in degrees -1 and 0.
4. The normalized unit and adjunct of lem-pur-sheaf-ring-derived-coefficient-adjunction
send x to x tensor 1 and x tensor a to a g(x). Therefore the actual quotient transition
is x tensor a mapped to x tensor q(a). In the free bases it is entrywise quotient.
The restriction interchange is fixed by its localization equation; these identities
prove all transition squares, including identity transitions, on the original cover.
5. Factor ell as a unit times pi^e, e positive, using the extending absolute value and
lem-weil-l-adic-extension-integers-dvr. Thus (ell^(n+1))=(pi^(e(n+1))). The finite residue
field and lem-weil-valued-dvr-finite-quotients give finiteness even when ell is ramified.
6. Exact constant realization identifies the two-term complex cohomology with the
constant scalar kernel and cokernel. All other degrees are zero.
7. The kernel is a subset of a finite free finite-ring module and the cokernel is a
quotient of one. Each is finite. A finite module has a presentation with generators
indexed by its elements and relations indexed by the finite kernel of that generator
map. Hence both modules are finitely presented.
8. The same local models give locally constant finite-type cohomology. Vanishing
outside the two degrees descends along the original covering sieves. Empty covering
sieves, zero ranks and N=0 are allowed; neither torsion-freeness nor Noetherianity of S
is used. -/
theorem integral_local_model_finite_matrix_reduction
    (S : Scheme.{t}) (_site : C ≌ S.ProEt)
    (_topology : J = _site.functor.inducedTopology (Scheme.ProEt.topology S))
    (L : Modules J (completion l E J))
    (_hL : HasFiniteScalarConstantLocalModel J (Scalars l E) (completion l E J)
      (scalarMap l E J) L) :
    (∀ n : ℕ, Finite (Residues l E n)) ∧
    (∀ (U : C) (N : ModuleCat.{r} (Scalars l E)),
      HasFiniteScalarConstantModelOn J (Scalars l E) (completion l E J)
        (scalarMap l E J) L U N →
      ∃ (a b : ℕ) (d : Matrix (Fin b) (Fin a) (Scalars l E))
        (p : (Fin b → Scalars l E) →ₗ[Scalars l E] N),
        Function.Injective (Matrix.toLin' d) ∧
        Function.Exact (Matrix.toLin' d) p ∧ Function.Surjective p ∧
        ∃ eN : ((model l E J).obj N).over U ≅ L.over U,
          ∃ hz : ((model l E J).map (ModuleCat.ofHom (Matrix.toLin' d))).over U ≫
            ((model l E J).map (ModuleCat.ofHom p)).over U ≫ eN.hom = 0,
          (ShortComplex.mk
            (((model l E J).map (ModuleCat.ofHom (Matrix.toLin' d))).over U)
            (((model l E J).map (ModuleCat.ofHom p)).over U ≫ eN.hom) hz).ShortExact ∧
          Nonempty (SimultaneousModels l E J L U d) ∧
          ∀ n : ℕ,
            Finite (scalarKernel l E d n) ∧ Finite (scalarCokernel l E d n) ∧
            Module.FinitePresentation (Residues l E n) (scalarKernel l E d n) ∧
            Module.FinitePresentation (Residues l E n) (scalarCokernel l E d n) ∧
            Nonempty (((DerivedCategory.homologyFunctor
                (SheafOfModules.{r}
                  ((SheafOfModules.derivedChangeRingIndependentCoefficients J
                    (coefficient l E J n)).over U)) (-1)).obj
              (localReduction l E J L U n)) ≅
                (((constantAtLevel l E J n).obj
                  (ModuleCat.of (Residues l E n) (scalarKernel l E d n))).over U)) ∧
            Nonempty (((DerivedCategory.homologyFunctor
                (SheafOfModules.{r}
                  ((SheafOfModules.derivedChangeRingIndependentCoefficients J
                    (coefficient l E J n)).over U)) 0).obj
              (localReduction l E J L U n)) ≅
                (((constantAtLevel l E J n).obj
                  (ModuleCat.of (Residues l E n) (scalarCokernel l E d n))).over U))) ∧
    (∀ (n : ℕ) (i : ℤ), i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (Modules J (coefficient l E J n)) i).obj (reduction l E J L n))) ∧
    (∀ (n : ℕ) (i : ℤ), i = -1 ∨ i = 0 → ∀ V : C,
      ∃ W : Sieve V, W ∈ J V ∧ ∀ (U : C) (f : U ⟶ V), W f →
        ∃ M : ModuleCat.{r} (Residues l E n), Module.Finite (Residues l E n) M ∧
          Nonempty ((((DerivedCategory.homologyFunctor
        (Modules J (coefficient l E J n)) i).obj
            (reduction l E J L n)).over U) ≅
              (((constantAtLevel l E J n).obj M).over U))) := by
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    hdvr.2.2.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing (Scalars l E) :=
    IsPrincipalIdealRing.of_surjective ULift.ringEquiv.symm
      ULift.ringEquiv.symm.surjective
  have : IsDomain (Scalars l E) :=
    ULift.ringEquiv.toMulEquiv.isDomain (Padic.coefficientExtensionIntegers l E)
  have localModels (U : C) (N : ModuleCat.{r} (Scalars l E))
      (hN : HasFiniteScalarConstantModelOn J (Scalars l E) (completion l E J)
        (scalarMap l E J) L U N) :
      ∃ (a b : ℕ) (d : Matrix (Fin b) (Fin a) (Scalars l E)),
        Nonempty (SimultaneousModels l E J L U d) := by
    let := hN.1
    obtain ⟨a, b, d, p, hd, hex, hp⟩ := finitePidResolution N
    obtain ⟨eN, hz, hs, hm⟩ := local_resolution l E J S _site _topology L U N hN d p hd hex hp
    exact ⟨a, b, d, hm⟩
  refine ⟨finiteResidues l E, ?_, ?_, ?_⟩
  · intro U N hN
    let := hN.1
    obtain ⟨a, b, d, p, hd, hex, hp⟩ := finitePidResolution N
    obtain ⟨eN, hz, hs, hm⟩ := local_resolution l E J S _site _topology L U N hN d p hd hex hp
    refine ⟨a, b, d, p, hd, hex, hp, eN, hz, hs, hm, ?_⟩
    intro n
    obtain ⟨models⟩ := hm
    obtain ⟨_, _, _, hk, hc⟩ :=
      matrix_cohomology l E J U d n (reduction l E J L n) (models.comparison n)
    obtain ⟨hfk, hfc, hpk, hpc⟩ := scalarFinitePresentation l E d n
    exact ⟨hfk, hfc, hpk, hpc, hk, hc⟩
  · intro n i hi1 hi0
    apply isZero_of_local J
    intro V
    obtain ⟨W, hW, hmodels⟩ := _hL V
    refine ⟨W, hW, ?_⟩
    intro U f hf
    obtain ⟨N, hN⟩ := hmodels U f hf
    obtain ⟨a, b, d, ⟨models⟩⟩ := localModels U N hN
    exact (matrix_cohomology l E J U d n (reduction l E J L n)
      (models.comparison n)).2.2.1 i hi1 hi0
  · intro n i hi V
    obtain ⟨W, hW, hmodels⟩ := _hL V
    refine ⟨W, hW, ?_⟩
    intro U f hf
    obtain ⟨N, hN⟩ := hmodels U f hf
    obtain ⟨a, b, d, ⟨models⟩⟩ := localModels U N hN
    have hcalc := matrix_cohomology l E J U d n (reduction l E J L n)
      (models.comparison n)
    let := finiteResidues l E n
    rcases hi with rfl | rfl
    · exact ⟨ModuleCat.of (Residues l E n) (scalarKernel l E d n),
        Module.Finite.of_finite, hcalc.1⟩
    · exact ⟨ModuleCat.of (Residues l E n) (scalarCokernel l E d n),
        (by
          let := (scalarFinitePresentation l E d n).2.1
          exact Module.Finite.of_finite), hcalc.2.1⟩

end IntegralMatrix
end AlgebraicGeometry.ProEtale
