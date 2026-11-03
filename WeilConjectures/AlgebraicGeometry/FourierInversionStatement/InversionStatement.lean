/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeGeometricFourier.NativeGeometricFourierModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FourierStalk.CanonicalStalkComparison
public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.CondensedFourierFirstFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedKernelTransformComposition
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCup.CondensedTraceCup
public import WeilConjectures.AlgebraicGeometry.DualBundlePairing
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-! # Base change and Fourier inversion

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-fourier-inversion/sk-thm-inversion/_section.md,
its proof, and the setting in sk-lem-as-properties (blueprint: sk-thm-inversion).

The coefficients are the pulled-back continuous-function condensed ring of E.
All derived categories and their bounded constructible full subcategories below
are the ordinary module-derived categories. The rank-zero and empty-base cases
are included. No constructibility or finite-type condition is placed on a new base.

The geometric Weil clauses use the published geometric model
`CondensedRing.NativeGeometricFourier` (its `transform` and `transformDatum`).
The finite-field stalk clause uses the published comparison
`CondensedRing.FourierStalk.finiteStalkComparison` and its local data.
Neither notion is redefined here.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FourierInversionStatement
open AlgebraicGeometry.ProEtale.CondensedRing

/-- The existing ordinary module-derived category, abbreviated only for readability.
Source: setting (blueprint: sk-thm-inversion). -/
abbrev D (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The existing bounded constructible full subcategory and its ambient morphisms.
Source: setting (blueprint: sk-thm-inversion). -/
abbrev BC (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  BoundedConstructible (condensedRingObj Λ X)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The inclusion of the recorded full bounded constructible subcategory.
Source: setting (blueprint: sk-thm-inversion). -/
abbrev inclusion (X : Scheme.{u}) : BC Λ X ⥤ D Λ X :=
  (boundedConstructible (condensedRingObj Λ X)).ι

/-- The recorded total derived pullback; this includes whole geometric derived stalks.
Source: base-change and stalk clauses (blueprint: sk-thm-inversion). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) : D Λ Y ⥤ D Λ X :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctor

/-- The recorded transform, with the product's structure induced from its base.
The existing degree-q kernel and rank shift are used without changing either.
Source: formula (18.1) (blueprint: sk-thm-inversion). -/
def transform (k₀ : Type u) [Field k₀] [Fintype k₀]
    {S V V' : Scheme.{u}} (s : S ⟶ Spec (.of k₀))
    (π : V ⟶ S) (π' : V' ⟶ S) (ψ : AddChar k₀ (MonObj.Γ Λ))
    (b : Γ(pullback π π', ⊤)) (c : Compactification (pullback.snd π π')) (r : ℤ) :
    D Λ V ⥤ D Λ V' :=
  letI : (pullback π π').Over (Spec (.of k₀)) :=
    ⟨pullback.fst π π' ≫ π ≫ s⟩
  condensedFourierTransform Λ k₀ π π' ψ b c r

/-- The kernel of the existing transform, with the same inherited finite-field structure.
Source: formula (18.1) (blueprint: sk-thm-inversion). -/
def kernel (k₀ : Type u) [Field k₀] [Fintype k₀]
    {S V V' : Scheme.{u}} (s : S ⟶ Spec (.of k₀))
    (π : V ⟶ S) (π' : V' ⟶ S) (ψ : AddChar k₀ (MonObj.Γ Λ))
    (b : Γ(pullback π π', ⊤)) :=
  letI : (pullback π π').Over (Spec (.of k₀)) :=
    ⟨pullback.fst π π' ≫ π ≫ s⟩
  condensedFourierKernel Λ k₀ π π' ψ b

/-- Tensor by the published signed rational Tate line, with its actual root construction.
Source: K(m) and the inversion twists (blueprint: sk-thm-inversion). -/
def twist (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) (m : ℤ) :
    D (Profinite.continuousMapRingObj E) X ⥤ D (Profinite.continuousMapRingObj E) X :=
  tensorRight ((DerivedCategory.singleFunctor _ 0).obj
    (spInternalSignedTwist X _ (spRationalTwist X ℓ E) m))

/-- Negation is specified in every dual-bundle chart, so it cannot be an arbitrary map.
Source: [-1]_V in the second inversion formula (blueprint: sk-thm-inversion). -/
def IsBundleNegation {S V Vdual : Scheme.{u}} {π : V ⟶ S} {πdual : Vdual ⟶ S}
    {r : ℕ} {b : Γ(pullback π πdual, ⊤)}
    (bundle : DualBundlePairing π πdual r b) (n : V ⟶ V) : Prop :=
  ∀ i : bundle.I, bundle.iV i ≫ n =
    (bundle.frameV i).hom ≫ AffineSpace.neg (ULift.{u} (Fin r)) (bundle.U i).toScheme ≫
      (bundle.frameV i).inv ≫ bundle.iV i

/-- Base linearity expressed as an isomorphism of bifunctors on the two bounded
constructible input categories, retaining naturality in both variables.
Source: first paragraph and Complement (blueprint: sk-thm-inversion). -/
def baseTensor {S V : Scheme.{u}} (π : V ⟶ S) : BC Λ S ⥤ (D Λ V ⥤ D Λ V) :=
  inclusion Λ S ⋙ pull Λ π ⋙ (curriedTensor (D Λ V)).flip

/-- The whole relative proposition over the finite field. Each comparison is natural;
the fibre uses the compactification pulled back to the geometric point.
Source: _section.md, setting, first paragraph, (18.2), and both inversion formulas
(blueprint: sk-thm-inversion).

Proof in words, in the nine-step order of the DAG:
1. prop-kernel-lisse makes the evaluation kernel locally free of rank one and flat.
   thm-fd-transform-well-defined applies pullback, tensor, shriek and the rank shift.
2. Form the Cartesian second-projection square for an arbitrary base change.
   The original compactification is Noetherian; det-prop-sf-cbc (b) allows any new base.
3. Pullback composition, its monoidal comparison and kernel pullback identify the
   changed integrand. Specialize the same exchange to a geometric point for (18.2).
4. The projection formula identifies tensor by a base complex on both sides.
   The isomorphism is natural in both inputs; its Tate specialization gives twists.
5. Kernel composition gives the triple-product convolution with total shift 2r.
   The inverse-character integral vanishes off the diagonal, and the same-character
   integral off the antidiagonal. Localization reconstructs each supported kernel.
6. On its support the zero-character unit and vector trace identify the kernel with
   E(-r)[-2r]. Graph-kernel assembly cancels the shift 2r and yields both formulas.
7. On a line the same localization and trace give delta_0(-1)[-1]; restricting the
   skyscraper to its zero-coordinate support gives E[1].
8. All comparisons are the proper/open exchange, projection, localization, unit and
   trace comparisons defined over k0, hence commute with Weil data and Frobenius.
9. The same base-change/projection/composition calculation gives convolution for
   admissible coefficients. Kernel multiplication and inverses are projector identities.
-/
theorem relative_fourier_inversion
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    {S V Vdual : Scheme.{u}} (s : S ⟶ Spec (.of k₀))
    [LocallyOfFiniteType s] [QuasiCompact s] [IsSeparated s]
    (π : V ⟶ S) (πdual : Vdual ⟶ S) (r : ℕ)
    (b : Γ(pullback π πdual, ⊤)) (bundle : DualBundlePairing π πdual r b)
    (c : Compactification (pullback.snd π πdual))
    (cdual : Compactification (pullback.snd πdual π)) :
    (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (pullback π πdual),
      ∀ i : U.I₀, Nonempty ((CondensedRing.upperStar
        (Profinite.continuousMapRingObj E) (U.f i)).obj
          (kernel (Profinite.continuousMapRingObj E) k₀ s π πdual
            ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b) ≅
        Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) (U.X i)))) ∧
    (∀ K : D (Profinite.continuousMapRingObj E) V,
      boundedConstructible _ K → boundedConstructible _
        ((transform (Profinite.continuousMapRingObj E) k₀ s π πdual
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ)
          b c (r : ℤ)).obj K)) ∧
    (∃ e : transform (Profinite.continuousMapRingObj E) k₀ s π πdual
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ) ⋙
        shiftFunctor _ (1 : ℤ) ≅ shiftFunctor _ (1 : ℤ) ⋙
        transform (Profinite.continuousMapRingObj E) k₀ s π πdual
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ),
      ∀ T : Triangle (D (Profinite.continuousMapRingObj E) V), T ∈ distTriang _ →
        boundedConstructible _ T.obj₁ → boundedConstructible _ T.obj₂ →
        boundedConstructible _ T.obj₃ →
        Triangle.mk
          ((transform (Profinite.continuousMapRingObj E) k₀ s π πdual
            ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ)
            b c (r : ℤ)).map T.mor₁)
          ((transform (Profinite.continuousMapRingObj E) k₀ s π πdual
            ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ)
            b c (r : ℤ)).map T.mor₂)
          ((transform (Profinite.continuousMapRingObj E) k₀ s π πdual
            ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ)
            b c (r : ℤ)).map T.mor₃ ≫ e.inv.app T.obj₁) ∈ distTriang _) ∧
    (∀ (S' W Wdual : Scheme.{u}) (g : S' ⟶ S)
      (ρ : W ⟶ S') (ρdual : Wdual ⟶ S') (gV : W ⟶ V) (gdual : Wdual ⟶ Vdual)
      (sqV : IsPullback gV ρ π g) (sqDual : IsPullback gdual ρdual πdual g)
      (c' : Compactification (pullback.snd ρ ρdual)),
      Nonempty (inclusion (Profinite.continuousMapRingObj E) V ⋙
        transform (Profinite.continuousMapRingObj E) k₀ s π πdual
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ) ⋙
        pull (Profinite.continuousMapRingObj E) gdual ≅
        inclusion (Profinite.continuousMapRingObj E) V ⋙
        pull (Profinite.continuousMapRingObj E) gV ⋙
        transform (Profinite.continuousMapRingObj E) k₀ (g ≫ s) ρ ρdual
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ)
          ((pullback.map ρ ρdual π πdual gV gdual g sqV.w.symm sqDual.w.symm).appTop b)
          c' (r : ℤ))) ∧
    Nonempty (baseTensor (Profinite.continuousMapRingObj E) π ⋙
      (Functor.whiskeringRight _ _ _).obj
        (transform (Profinite.continuousMapRingObj E) k₀ s π πdual
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ)) ⋙
      (Functor.whiskeringLeft _ _ _).obj (inclusion (Profinite.continuousMapRingObj E) V) ≅
      baseTensor (Profinite.continuousMapRingObj E) πdual ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (inclusion (Profinite.continuousMapRingObj E) V ⋙
          transform (Profinite.continuousMapRingObj E) k₀ s π πdual
            ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ))) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ Vdual),
      Nonempty (inclusion (Profinite.continuousMapRingObj E) V ⋙
        transform (Profinite.continuousMapRingObj E) k₀ s π πdual
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ) ⋙
        pull (Profinite.continuousMapRingObj E) ξ ≅
        inclusion (Profinite.continuousMapRingObj E) V ⋙
        pull (Profinite.continuousMapRingObj E)
          (pullback.fst (pullback.snd π πdual) ξ ≫ pullback.fst π πdual) ⋙
        tensorRight ((pull (Profinite.continuousMapRingObj E)
          (pullback.fst (pullback.snd π πdual) ξ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (kernel (Profinite.continuousMapRingObj E) k₀ s π πdual
              ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b))) ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.continuousMapRingObj E) (c.baseChange ξ) ⋙ shiftFunctor _ (r : ℤ))) ∧
    (Nonempty (inclusion (Profinite.continuousMapRingObj E) V ⋙
        transform (Profinite.continuousMapRingObj E) k₀ s π πdual
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ) ⋙
        transform (Profinite.continuousMapRingObj E) k₀ s πdual π
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ⁻¹)
          ((pullbackSymmetry πdual π).hom.appTop b) cdual (r : ℤ) ≅
        inclusion (Profinite.continuousMapRingObj E) V ⋙ twist ℓ E V (-(r : ℤ)))) ∧
    (∃ n : V ⟶ V, IsBundleNegation bundle n ∧
      Nonempty (inclusion (Profinite.continuousMapRingObj E) V ⋙
        transform (Profinite.continuousMapRingObj E) k₀ s π πdual
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ) ⋙
        transform (Profinite.continuousMapRingObj E) k₀ s πdual π
          ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ)
          ((pullbackSymmetry πdual π).hom.appTop b) cdual (r : ℤ) ≅
        inclusion (Profinite.continuousMapRingObj E) V ⋙
          twist ℓ E V (-(r : ℤ)) ⋙ pull (Profinite.continuousMapRingObj E) n)) := by
  sorry

/-- On the line the coefficient unit transforms to delta_0(-1)[-1] and the
zero-section skyscraper transforms to the unit shifted by one.
Source: current blueprint, sk-thm-inversion, the two first formulas
(blueprint: sk-thm-inversion).
Proof: the same localization, zero-root unit and rank-one trace used in step 7
of the main theorem give the unit formula. For the skyscraper, restrict the
kernel to the zero-coordinate support, use its specified unit trivialization,
and apply compact-support composition. These constructions are defined over k₀. -/
theorem line_formulas
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ),
      ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k₀)) ↘ Spec (.of k₀))
      (AffineSpace PUnit (Spec (.of k₀)) ↘ Spec (.of k₀)))) :
    condensedFourierFirstFormulas (Profinite.continuousMapRingObj E) k₀ k₀
      ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c
      (spRationalTwist (AffineSpace PUnit (Spec (.of k₀))) ℓ E) := by
  simpa using (condensedFourier_first_formula p ℓ hpℓ k₀ E hμ ψ hψ k₀
    (Or.inl inferInstance) c).1

/-- Multiplicativity and the tensor inverse of the arbitrary-pairing kernel,
including the trivial character and an empty product. The definitions `kernel`
and `transform` above impose no vector-bundle condition.
Source: current blueprint, sk-thm-inversion, Complement
(blueprint: sk-thm-inversion).
Proof: pull the projector tensor-product and zero-character unit identifications
back along the pairing. The inverse-character specialization has product one.
The normalized Artin--Schreier cover trivializes the kernel and these maps;
therefore descent gives the displayed isomorphisms for all admissible rings. -/
theorem kernel_complement
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (hΛ : CondensedRing.IsAdmissibleCoefficient Λ)
    (hq : IsUnit (Fintype.card k₀ : MonObj.Γ Λ))
    {S V V' : Scheme.{u}} (s : S ⟶ Spec (.of k₀))
    (π : V ⟶ S) (π' : V' ⟶ S)
    (ψ ψ' : AddChar k₀ (MonObj.Γ Λ)) (b : Γ(pullback π π', ⊤)) :
    Nonempty (kernel Λ k₀ s π π' ψ b ⊗ kernel Λ k₀ s π π' ψ' b ≅
      kernel Λ k₀ s π π' (ψ * ψ') b) ∧
    Nonempty (kernel Λ k₀ s π π' ψ b ⊗ kernel Λ k₀ s π π' ψ⁻¹ b ≅
      Mod.regular (condensedRingObj Λ (pullback π π'))) := by
  let : (pullback π π').Over (Spec (.of k₀)) :=
    ⟨pullback.fst π π' ≫ π ≫ s⟩
  have h := AlgebraicGeometry.Etale.prop_kernel_lisse.2.2.2
    Λ k₀ hq hΛ (pullback π π') ψ ψ' b
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- The arbitrary-kernel convolution formula, for all three non-torsion
admissible coefficient families over the finite field. Finite coefficients are
read on the etale site in the proved `Etale.nonempty_iso_kernelTransform_comp`.
Source: current blueprint, sk-thm-inversion, Complement
(blueprint: sk-thm-inversion).
Proof: expand the two transforms. Compact-support base change rewrites the middle
pullback and shriek as the corresponding two triple-product projections. The
proper and open projection formulas move the second kernel inside. Compact-support
composition, monoidality and the projection formula for the remaining projection
give the convolution. The shifts add. Stability puts every intermediate object
in the bounded constructible category, equal to Dctf for these coefficients. -/
theorem kernel_composition
    (p : ℕ) [Fact p.Prime]
    (hΛ : ∃ (ℓ : ℕ) (_hℓ : Fact ℓ.Prime), ℓ ≠ p ∧
      ((∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ))))
    (hp : IsUnit (p : MonObj.Γ Λ))
    (k₀ : Type u) [Field k₀] [Finite k₀] [CharP k₀ p]
    {S V V' V'' : Scheme.{u}} (s : S ⟶ Spec (.of k₀))
    (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)
    [LocallyOfFiniteType s] [QuasiCompact s] [IsSeparated s]
    [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π]
    [LocallyOfFiniteType π'] [QuasiCompact π'] [IsSeparated π']
    [LocallyOfFiniteType π''] [QuasiCompact π''] [IsSeparated π'']
    (c₁₂ : Compactification (pullback.snd π π'))
    (c₂₃ : Compactification (pullback.snd π' π''))
    (c₁₃ : Compactification (pullback.snd π π''))
    (cconv : Compactification (pullback.tripleProj₁₃ π π' π''))
    (K : D Λ (pullback π π')) (K' : D Λ (pullback π' π''))
    (hK : boundedConstructible _ K) (hK' : boundedConstructible _ K') (a b : ℤ) :
    boundedConstructible _ (CondensedRing.condensedKernelConvolution Λ π π' π'' cconv K K') ∧
    Nonempty (inclusion Λ V ⋙ CondensedRing.condensedKernelTransform Λ π π' c₁₂ K a ⋙
      CondensedRing.condensedKernelTransform Λ π' π'' c₂₃ K' b ≅
      inclusion Λ V ⋙ CondensedRing.condensedKernelTransform Λ π π'' c₁₃
        (CondensedRing.condensedKernelConvolution Λ π π' π'' cconv K K') (a + b)) := by
  let : S.Over (Spec (.of k₀)) := ⟨s⟩
  let : V.Over (Spec (.of k₀)) := ⟨π ≫ s⟩
  let : V'.Over (Spec (.of k₀)) := ⟨π' ≫ s⟩
  let : V''.Over (Spec (.of k₀)) := ⟨π'' ≫ s⟩
  let : LocallyOfFiniteType (S ↘ Spec (.of k₀)) := by
    change LocallyOfFiniteType s
    infer_instance
  let : QuasiCompact (S ↘ Spec (.of k₀)) := by
    change QuasiCompact s
    infer_instance
  let : IsSeparated (S ↘ Spec (.of k₀)) := by
    change IsSeparated s
    infer_instance
  let : LocallyOfFiniteType (V ↘ Spec (.of k₀)) := by
    change LocallyOfFiniteType (π ≫ s)
    infer_instance
  let : QuasiCompact (V ↘ Spec (.of k₀)) := by
    change QuasiCompact (π ≫ s)
    infer_instance
  let : IsSeparated (V ↘ Spec (.of k₀)) := by
    change IsSeparated (π ≫ s)
    infer_instance
  let : LocallyOfFiniteType (V' ↘ Spec (.of k₀)) := by
    change LocallyOfFiniteType (π' ≫ s)
    infer_instance
  let : QuasiCompact (V' ↘ Spec (.of k₀)) := by
    change QuasiCompact (π' ≫ s)
    infer_instance
  let : IsSeparated (V' ↘ Spec (.of k₀)) := by
    change IsSeparated (π' ≫ s)
    infer_instance
  let : LocallyOfFiniteType (V'' ↘ Spec (.of k₀)) := by
    change LocallyOfFiniteType (π'' ≫ s)
    infer_instance
  let : QuasiCompact (V'' ↘ Spec (.of k₀)) := by
    change QuasiCompact (π'' ≫ s)
    infer_instance
  let : IsSeparated (V'' ↘ Spec (.of k₀)) := by
    change IsSeparated (π'' ≫ s)
    infer_instance
  obtain ⟨hconv, F, ⟨e₁⟩, ⟨e₂⟩⟩ := condensedKernelTransform_comp
    Λ p hΛ hp k₀ (Or.inl inferInstance) (S := S) (V := V) (V' := V') (V'' := V'')
      π π' π'' c₁₂ c₂₃ c₁₃ cconv K K' hK hK' a b
  exact ⟨hconv, ⟨e₁.symm ≪≫ e₂⟩⟩

/-- Tate twists commute with the relative Fourier transform, as a natural
isomorphism on the whole bounded constructible input category.
Source: current blueprint, sk-thm-inversion, Complement
(blueprint: sk-thm-inversion).
Proof: the Tate line is pulled back from S. Apply base linearity to its signed
power in degree zero. The canonical root pullback comparison identifies its
pullbacks with the signed Tate lines on the two bundles. -/
theorem twists_commute
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ),
      ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    {S V Vdual : Scheme.{u}} (s : S ⟶ Spec (.of k₀))
    [LocallyOfFiniteType s] [QuasiCompact s] [IsSeparated s]
    (π : V ⟶ S) (πdual : Vdual ⟶ S) (r : ℕ)
    (b : Γ(pullback π πdual, ⊤)) (bundle : DualBundlePairing π πdual r b)
    (c : Compactification (pullback.snd π πdual)) (m : ℤ) :
    Nonempty (inclusion (Profinite.continuousMapRingObj E) V ⋙ twist ℓ E V m ⋙
      transform (Profinite.continuousMapRingObj E) k₀ s π πdual
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ) ≅
      inclusion (Profinite.continuousMapRingObj E) V ⋙
      transform (Profinite.continuousMapRingObj E) k₀ s π πdual
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) b c (r : ℤ) ⋙
      twist ℓ E Vdual m) := by
  sorry

namespace WeilData
/-- The dependency's recorded ordinary derived Frobenius action.
Source: Weil sentence (blueprint: sk-thm-inversion). -/
abbrev action := @CondensedRing.StrictWeilCondensed.action.{u}
/-- The dependency's canonical tensor Weil datum, including the tensorator.
Source: Weil sentence (blueprint: sk-thm-inversion). -/
abbrev tensorDatum := @CondensedRing.StrictWeilCondensed.tensorDatum.{u}
/-- The dependency's recorded geometric Frobenius, on arbitrary arithmetic models.
Source: Weil sentence (blueprint: sk-thm-inversion). -/
abbrev modelFrobenius := CondensedRing.StrictWeilCondensed.modelFrobenius.{u}
end WeilData

namespace Geometric
variable (D : WeilConjectures.FiniteFieldDatum.{u})
open CondensedRing.NativeGeometricFourier

/-- The signed Tate line on the geometric fibre used in the inversion identities.
Source: Weil sentence, Tate twist clause (blueprint: sk-thm-inversion). -/
abbrev tateLine (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (X : Over (Spec (.of D.k₀))) (m : ℤ) :=
  CondensedRing.StrictWeilCondensed.derivedTateLine ell (.rational E) (fiber D X) m

/-- The standard Weil Tate datum on a geometric fibre.
Source: the Tate-data clause of `sk-def-sf-weil-complexes` (blueprint: sk-thm-inversion). -/
abbrev tateDatum (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (hpell : D.p ≠ ell)
    (X : Over (Spec (.of D.k₀))) (m : ℤ) :=
  let T : Over (Spec (.of D.k)) :=
    Over.mk (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  letI : ∀ x : T.left, Invertible (ell : T.left.residueField x) :=
    CondensedRing.TraceCup.residueInverse ell D hpell.symm T
  CondensedRing.StrictWeilCondensed.tateDatum ell (.rational E)
    (CondensedRing.StrictWeilCondensed.modelFrobenius D X) m

/-- The tensor datum for a given Weil structure and Tate datum.
Source: Weil sentence, Tate twist clause (blueprint: sk-thm-inversion). -/
abbrev twistDatum (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (hpell : D.p ≠ ell)
    (X : Over (Spec (.of D.k₀))) (m : ℤ)
    (K : category D (Profinite.continuousMapRingObj E) X)
    (φ : (CondensedRing.StrictWeilCondensed.action (Profinite.continuousMapRingObj E)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X)).obj K ≅ K) :=
  CondensedRing.StrictWeilCondensed.tensorDatum (Profinite.continuousMapRingObj E)
    (CondensedRing.StrictWeilCondensed.modelFrobenius D X) φ (tateDatum D ell E hpell X m)

/-- Arithmetic descent of a derived pullback along a model projection fixed by `g`:
the exact-pullback comparison, the derived pullback compositor, and the equality
`g ≫ π = π`. No isomorphism is chosen from an existence statement.
Source: Weil sentence, the arithmetic structure of E and delta_0 on the line
(blueprint: sk-thm-inversion). -/
def derivedDescent (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (π : X ⟶ Y) (g : X ≅ X)
    (h : g.hom ≫ π = π)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (CondensedRing.StrictWeilCondensed.action Λ g).obj
        ((CondensedRing.upperStar Λ π).leftDerivedFunctor.obj A) ≅
      (CondensedRing.upperStar Λ π).leftDerivedFunctor.obj A :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g.hom).symm.app _ ≪≫
    (CondensedRing.leftDerivedUpperStarComp Λ g.hom π).symm.app A ≪≫
      eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).leftDerivedFunctor.obj A) h)

/-- The standard arithmetic Weil structure on the geometric pullback of a complex on
the arithmetic model, by descent along the model projection fixed by model Frobenius.
Source: Weil sentence, first formulas over k₀ (blueprint: sk-thm-inversion). -/
def arithmeticDatum (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Over (Spec (.of D.k₀)))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :=
  letI := Fintype.ofFinite D.k₀
  derivedDescent Λ (projection D X) (CondensedRing.StrictWeilCondensed.modelFrobenius D X)
    (D.galoisMap_projections X.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).1 A

/-- Both inversion maps commute with every Weil structure and the standard Tate data.
The transforms are the published geometric model `NativeGeometricFourier.transform`,
with its specified Frobenius `NativeGeometricFourier.transformDatum`.
Source: inversion and Weil sentences (blueprint: sk-thm-inversion).
Proof: convolution, diagonal or antidiagonal localization, the zero-root unit and
vector trace are the source's steps 5--6. They are arithmetic maps; proper/open
exchange coherence makes them commute with the prescribed data. The shifts cancel,
leaving the root-defined Tate line and exactly the following two equations. -/
theorem weil_inversion
    (ell : ℕ) [Fact ell.Prime] (hpell : D.p ≠ ell)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (hμ : ∀ ζ : rootsOfUnity D.p (PadicAlgCl ell),
      ((ζ : (PadicAlgCl ell)ˣ) : PadicAlgCl ell) ∈ E.1)
    (ψ : AddChar D.k₀ E) (hψ : ψ ≠ 1)
    {S V Vdual : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (π : V ⟶ S) (πdual : Vdual ⟶ S) (r : ℕ)
    (b : Γ(pullback π.left πdual.left, ⊤))
    (bundle : DualBundlePairing π.left πdual.left r b)
    (c : Compactification (pullback.snd π.left πdual.left))
    (cdual : Compactification (pullback.snd πdual.left π.left)) :
    let R := Profinite.continuousMapRingObj E
    let χ := (Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ
    let bdual := (pullbackSymmetry πdual.left π.left).hom.appTop b
    (∃ e : inclusion R (fiber D V) ⋙
        NativeGeometricFourier.transform D R π πdual χ b c (r : ℤ) ⋙
        NativeGeometricFourier.transform D R πdual π χ⁻¹ bdual cdual (r : ℤ) ≅
        inclusion R (fiber D V) ⋙ tensorRight (tateLine D ell E V (-(r : ℤ))),
      ∀ (K : BC R (fiber D V))
        (φ : (WeilData.action R (WeilData.modelFrobenius D V)).obj K.obj ≅ K.obj),
        (WeilData.action R (WeilData.modelFrobenius D V)).map (e.hom.app K) ≫
            (twistDatum D ell E hpell V (-(r : ℤ)) K.obj φ).hom =
          (transformDatum D R πdual π χ⁻¹ bdual cdual (r : ℤ) _
            (transformDatum D R π πdual χ b c (r : ℤ) K.obj φ)).hom ≫ e.hom.app K) ∧
    (∃ (n : V ⟶ V), IsBundleNegation bundle n.left ∧
      ∃ e : inclusion R (fiber D V) ⋙
          NativeGeometricFourier.transform D R π πdual χ b c (r : ℤ) ⋙
          NativeGeometricFourier.transform D R πdual π χ bdual cdual (r : ℤ) ≅
          inclusion R (fiber D V) ⋙ tensorRight (tateLine D ell E V (-(r : ℤ))) ⋙
            (CondensedRing.upperStar R (map D n)).leftDerivedFunctor,
        ∀ (K : BC R (fiber D V))
          (φ : (WeilData.action R (WeilData.modelFrobenius D V)).obj K.obj ≅ K.obj),
          (WeilData.action R (WeilData.modelFrobenius D V)).map (e.hom.app K) ≫
              (pullDatum D R n _ (twistDatum D ell E hpell V (-(r : ℤ)) K.obj φ)).hom =
            (transformDatum D R πdual π χ bdual cdual (r : ℤ) _
              (transformDatum D R π πdual χ b c (r : ℤ) K.obj φ)).hom ≫ e.hom.app K) := by
  sorry

/-- Base tensoring in two variables on the geometric fibres.
Source: base-linearity sentence (blueprint: sk-thm-inversion). -/
def baseTensor (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (D : WeilConjectures.FiniteFieldDatum.{u})
    {S V : Over (Spec (.of D.k₀))} (π : V ⟶ S) :
    BC Λ (fiber D S) ⥤ (category D Λ V ⥤ category D Λ V) :=
  inclusion Λ (fiber D S) ⋙ (CondensedRing.upperStar Λ (map D π)).leftDerivedFunctor ⋙
    (curriedTensor (category D Λ V)).flip

/-- Base linearity, including equality of the actual Weil morphisms.
Source: base-linearity and Weil sentences (blueprint: sk-thm-inversion).
Proof: reassociate the integrand, move the base factor across the equality of
projections, apply proper/open projection, and commute tensor with shift.
Monoidality and exchange coherence give the displayed equation for both inputs. -/
theorem weil_base_linear
    (ell : ℕ) [Fact ell.Prime] (hpell : D.p ≠ ell)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (hμ : ∀ ζ : rootsOfUnity D.p (PadicAlgCl ell),
      ((ζ : (PadicAlgCl ell)ˣ) : PadicAlgCl ell) ∈ E.1)
    (ψ : AddChar D.k₀ E) (hψ : ψ ≠ 1)
    {S V Vdual : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (π : V ⟶ S) (πdual : Vdual ⟶ S) (r : ℕ)
    (b : Γ(pullback π.left πdual.left, ⊤))
    (bundle : DualBundlePairing π.left πdual.left r b)
    (c : Compactification (pullback.snd π.left πdual.left)) :
    let R := Profinite.continuousMapRingObj E
    let χ := (Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ
    ∃ e : baseTensor R D π ⋙
        (Functor.whiskeringRight _ _ _).obj
          (NativeGeometricFourier.transform D R π πdual χ b c (r : ℤ)) ⋙
        (Functor.whiskeringLeft _ _ _).obj (inclusion R (fiber D V)) ≅
        baseTensor R D πdual ⋙ (Functor.whiskeringLeft _ _ _).obj
          (inclusion R (fiber D V) ⋙
            NativeGeometricFourier.transform D R π πdual χ b c (r : ℤ)),
      ∀ (N : BC R (fiber D S)) (K : BC R (fiber D V))
        (θ : (WeilData.action R (WeilData.modelFrobenius D S)).obj N.obj ≅ N.obj)
        (φ : (WeilData.action R (WeilData.modelFrobenius D V)).obj K.obj ≅ K.obj),
        (WeilData.action R (WeilData.modelFrobenius D Vdual)).map ((e.hom.app N).app K) ≫
            (WeilData.tensorDatum R (WeilData.modelFrobenius D Vdual)
              (transformDatum D R π πdual χ b c (r : ℤ) K.obj φ)
              (pullDatum D R πdual N.obj θ)).hom =
          (transformDatum D R π πdual χ b c (r : ℤ) _
            (WeilData.tensorDatum R (WeilData.modelFrobenius D V)
              φ (pullDatum D R π N.obj θ))).hom ≫ (e.hom.app N).app K := by
  sorry

/-- Arithmetic base change is compatible with the prescribed Weil data.
Source: base-change and Weil sentences (blueprint: sk-thm-inversion).
Proof: apply the compact-support exchange on the product square, then identify
the kernel and pulled integrand by the tensorator and compositor. Paste its
arithmetic Frobenius square. Exchange cube coherence identifies both composites
with the same proper/open exchange followed by the input datum. -/
theorem weil_base_change
    (ell : ℕ) [Fact ell.Prime] (hpell : D.p ≠ ell)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (hμ : ∀ ζ : rootsOfUnity D.p (PadicAlgCl ell),
      ((ζ : (PadicAlgCl ell)ˣ) : PadicAlgCl ell) ∈ E.1)
    (ψ : AddChar D.k₀ E) (hψ : ψ ≠ 1)
    {S S' V Vdual W Wdual : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (g : S' ⟶ S) (π : V ⟶ S) (πdual : Vdual ⟶ S)
    (ρ : W ⟶ S') (ρdual : Wdual ⟶ S') (gV : W ⟶ V) (gdual : Wdual ⟶ Vdual)
    (sqV : IsPullback gV.left ρ.left π.left g.left)
    (sqDual : IsPullback gdual.left ρdual.left πdual.left g.left)
    (r : ℕ) (b : Γ(pullback π.left πdual.left, ⊤))
    (bundle : DualBundlePairing π.left πdual.left r b)
    (c : Compactification (pullback.snd π.left πdual.left))
    (c' : Compactification (pullback.snd ρ.left ρdual.left)) :
    let R := Profinite.continuousMapRingObj E
    let χ := (Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ
    let b' := (pullback.map ρ.left ρdual.left π.left πdual.left
      gV.left gdual.left g.left sqV.w.symm sqDual.w.symm).appTop b
    ∃ e : inclusion R (fiber D V) ⋙
        NativeGeometricFourier.transform D R π πdual χ b c (r : ℤ) ⋙
        (CondensedRing.upperStar R (map D gdual)).leftDerivedFunctor ≅
        inclusion R (fiber D V) ⋙
          (CondensedRing.upperStar R (map D gV)).leftDerivedFunctor ⋙
          NativeGeometricFourier.transform D R ρ ρdual χ b' c' (r : ℤ),
      ∀ (K : BC R (fiber D V))
        (φ : (WeilData.action R (WeilData.modelFrobenius D V)).obj K.obj ≅ K.obj),
        (WeilData.action R (WeilData.modelFrobenius D Wdual)).map (e.hom.app K) ≫
            (transformDatum D R ρ ρdual χ b' c' (r : ℤ) _
              (pullDatum D R gV K.obj φ)).hom =
          (pullDatum D R gdual _
            (transformDatum D R π πdual χ b c (r : ℤ) K.obj φ)).hom ≫ e.hom.app K := by
  sorry

/-- The first formulas respect the arithmetic unit, zero skyscraper and standard
Tate structures after geometric base change.
Source: first formulas and Weil sentence (blueprint: sk-thm-inversion).
Proof: localization reconstructs the unit transform on zero; compact base change,
zero-root trivialization and rank-one trace give delta_0(-1)[-1]. Restricting the
skyscraper integrand to zero leaves the unit and shift [1]. These are arithmetic
adjunction, exchange, unit and trace maps, hence commute with arithmeticDatum. -/
theorem weil_line_formulas
    (ell : ℕ) [Fact ell.Prime] (hpell : D.p ≠ ell)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (hμ : ∀ ζ : rootsOfUnity D.p (PadicAlgCl ell),
      ((ζ : (PadicAlgCl ell)ˣ) : PadicAlgCl ell) ∈ E.1)
    (ψ : AddChar D.k₀ E) (hψ : ψ ≠ 1)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (AffineSpace PUnit (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)))) :
    let R := Profinite.continuousMapRingObj E
    let X : Over (Spec (.of D.k₀)) :=
      Over.mk (AffineSpace PUnit (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
    let S : Over (Spec (.of D.k₀)) := Over.mk (𝟙 _)
    let π : X ⟶ S := Over.homMk X.hom (Category.comp_id X.hom)
    let χ := (Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ
    let b := AffineSpace.stdPairing PUnit (Spec (.of D.k₀))
    let F := NativeGeometricFourier.transform D R π π χ b c 1
    let G := (CondensedRing.upperStar R (projection D X)).leftDerivedFunctor
    let U := condensedFourierUnit R X.left
    let Δ := condensedFourierDelta R D.k₀
    let TΔ := (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist X.left _ (spRationalTwist X.left ell E) Δ (-1))
    let TU := (shiftFunctor _ (1 : ℤ)).obj U
    (∃ e : F.obj (G.obj U) ≅ G.obj TΔ,
      (WeilData.action R (WeilData.modelFrobenius D X)).map e.hom ≫
          (arithmeticDatum D R X TΔ).hom =
        (transformDatum D R π π χ b c 1 (G.obj U) (arithmeticDatum D R X U)).hom ≫
          e.hom) ∧
    (∃ e : F.obj (G.obj Δ) ≅ G.obj TU,
      (WeilData.action R (WeilData.modelFrobenius D X)).map e.hom ≫
          (arithmeticDatum D R X TU).hom =
        (transformDatum D R π π χ b c 1 (G.obj Δ) (arithmeticDatum D R X Δ)).hom ≫
          e.hom) := by
  sorry

end Geometric
end AlgebraicGeometry.ProEtale.FourierInversionStatement

namespace AlgebraicGeometry.ProEtale.FourierInversionStatement.Stalk
open CondensedRing CondensedRing.FourierStalk
variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable {S₀ V₀ Y₀ : Over (Spec (.of D₀.k₀))}
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

end AlgebraicGeometry.ProEtale.FourierInversionStatement.Stalk
