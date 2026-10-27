/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Derivation.Lie

/-! # Étale coordinate derivations and formal Taylor comparison

Source: Stacks Project, algebra.tex, Tags 0H93, 00RX and 00RO; more-algebra.tex,
Tag 07PE(2); schemes.tex, Tag 01HV
(blueprint: lem-trf-etale-coordinate-derivations-jacobian).

## Main definitions and statements

- `etaleCoordinateSection`: the restricted pullback of a standard coordinate.
- `HasEtaleCoordinateCalculus`: the full basis, derivation and Taylor conclusion.
- `hasEtaleCoordinateCalculus`: that conclusion for a finite-type scheme with étale coordinates.

The auxiliary abbreviations install the actual scalar maps on sections and stalks.
`HasEtaleCoordinateCalculus` expands all clauses of the conclusion; it does not assume them.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The scalar map on sections induced by the structure morphism to `Spec k`.
Source: Stacks Project, algebra.tex, Tag 00RO, applied to sections over a k-scheme
(blueprint: lem-trf-etale-coordinate-derivations-jacobian). -/
abbrev etaleCoordinateSectionAlgebra (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (V : U.Opens) : Algebra k Γ(U, V) :=
  ((ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop ≫
    U.presheaf.map (homOfLE le_top).op).hom.toAlgebra

/-- The scalar map on a stalk induced by the structure morphism to `Spec k`.
Source: Stacks Project, schemes.tex, Tag 01HV
(blueprint: lem-trf-etale-coordinate-derivations-jacobian). -/
abbrev etaleCoordinateStalkAlgebra (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (p : U) : Algebra k (U.presheaf.stalk p) :=
  ((ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop ≫
    U.presheaf.germ ⊤ p trivial).hom.toAlgebra

/-- Derivations of sections with their canonical k-algebra structure.
Source: Stacks Project, algebra.tex, Tag 00RO
(blueprint: lem-trf-etale-coordinate-derivations-jacobian). -/
abbrev EtaleCoordinateSectionDerivation (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (V : U.Opens) :=
  letI := etaleCoordinateSectionAlgebra k U V
  Derivation k Γ(U, V) Γ(U, V)

/-- Derivations of the actual local ring with its canonical k-algebra structure.
Source: Stacks Project, schemes.tex, Tag 01HV
(blueprint: lem-trf-etale-coordinate-derivations-jacobian). -/
abbrev EtaleCoordinateStalkDerivation (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (p : U) :=
  letI := etaleCoordinateStalkAlgebra k U p
  Derivation k (U.presheaf.stalk p) (U.presheaf.stalk p)

/-- The coordinate function restricted to an open, using Mathlib's affine-space coordinates.
Source: Stacks Project, algebra.tex, Tags 0H93 and 00RX
(blueprint: lem-trf-etale-coordinate-derivations-jacobian). -/
def etaleCoordinateSection (k : Type u) [Field k] (U : Scheme.{u}) (n : ℕ)
    (x : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))) (V : U.Opens)
    (i : Fin n) : Γ(U, V) :=
  U.presheaf.map (homOfLE le_top).op
    (x.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up i)))

/-- Expanded conclusion: a differential basis and evaluation bijection for every module,
unique commuting derivations on each affine open, a common compatible family on local rings,
and the first and all iterated Taylor comparison identities, on sections and on germs.
The `List.foldr` terms are finite iterated derivatives in the ring of regular sections itself;
the empty word is the identity. All scalar structures below are the canonical maps above.
Source: Stacks Project, algebra.tex, Tags 0H93, 00RX and 00RO; more-algebra.tex, Tag 07PE(2)
(blueprint: lem-trf-etale-coordinate-derivations-jacobian). -/
def HasEtaleCoordinateCalculus (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (n : ℕ)
    (x : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))) : Prop :=
  ∃ (D : ∀ (V : U.Opens), IsAffineOpen V → Fin n →
      EtaleCoordinateSectionDerivation k U V)
    (d : ∀ p : U, Fin n → EtaleCoordinateStalkDerivation k U p),
    (∀ (V : U.Opens) (hV : IsAffineOpen V),
      letI := etaleCoordinateSectionAlgebra k U V
      (∃ b : Module.Basis (Fin n) Γ(U, V) (KaehlerDifferential k Γ(U, V)),
        ∀ i : Fin n, b i = KaehlerDifferential.D k Γ(U, V)
          (etaleCoordinateSection k U n x V i)) ∧
      (∀ (M : Type v) [AddCommGroup M] [Module Γ(U, V) M],
        letI : Module k M := Module.compHom M (algebraMap k Γ(U, V))
        Function.Bijective (fun E : Derivation k Γ(U, V) M ↦
          fun i : Fin n ↦ E (etaleCoordinateSection k U n x V i))) ∧
      (∀ i j : Fin n, D V hV i (etaleCoordinateSection k U n x V j) =
        if i = j then 1 else 0) ∧
      (∀ (i : Fin n) (E : Derivation k Γ(U, V) Γ(U, V)),
        (∀ j : Fin n, E (etaleCoordinateSection k U n x V j) =
          if i = j then 1 else 0) → E = D V hV i) ∧
      (∀ (i j : Fin n) (c : Γ(U, V)), D V hV i (D V hV j c) =
        D V hV j (D V hV i c)) ∧
      (∀ c : Γ(U, V), KaehlerDifferential.D k Γ(U, V) c =
        ∑ i : Fin n, D V hV i c • KaehlerDifferential.D k Γ(U, V)
          (etaleCoordinateSection k U n x V i)) ∧
      (∀ (W : U.Opens) (hW : IsAffineOpen W) (hWV : W ≤ V)
          (i : Fin n) (c : Γ(U, V)),
        U.presheaf.map (homOfLE hWV).op (D V hV i c) =
          D W hW i (U.presheaf.map (homOfLE hWV).op c)) ∧
      (∀ (p : U) (hp : p ∈ V) (i : Fin n) (c : Γ(U, V)),
        d p i (U.presheaf.germ V p hp c) = U.presheaf.germ V p hp (D V hV i c)) ∧
      (∀ (L : Type w) [Field L] [Algebra k L]
          (τ : Γ(U, V) →ₐ[k] MvPowerSeries (Fin n) L) (a : Fin n → L),
        (∀ i : Fin n, τ (etaleCoordinateSection k U n x V i) =
          MvPowerSeries.C (a i) + MvPowerSeries.X i) →
        (∀ (i : Fin n) (c : Γ(U, V)),
          MvPowerSeries.pderiv L i (τ c) = τ (D V hV i c)) ∧
        (∀ (is : List (Fin n)) (c : Γ(U, V)),
          is.foldr (fun i s ↦ MvPowerSeries.pderiv L i s) (τ c) =
            τ (is.foldr (fun i b ↦ D V hV i b) c)) ∧
        (∀ (p : U) (hp : p ∈ V),
          letI := etaleCoordinateStalkAlgebra k U p
          ∀ τp : U.presheaf.stalk p →ₐ[k] MvPowerSeries (Fin n) L,
          (∀ c : Γ(U, V), τp (U.presheaf.germ V p hp c) = τ c) →
          (∀ (i : Fin n) (c : U.presheaf.stalk p),
            MvPowerSeries.pderiv L i (τp c) = τp (d p i c)) ∧
          (∀ (is : List (Fin n)) (c : U.presheaf.stalk p),
            is.foldr (fun i s ↦ MvPowerSeries.pderiv L i s) (τp c) =
              τp (is.foldr (fun i b ↦ d p i b) c))))) ∧
    (∀ (p : U) (i j : Fin n) (c : U.presheaf.stalk p),
      d p i (d p j c) = d p j (d p i c))

/-- The differentials of the pulled-back coordinates form a basis on every affine open.
The scalar map is the one induced by the structure morphism, including on the empty open.
Source: Stacks Project, algebra.tex, Tags 0H93 and 00RX; morphisms.tex, Tag 02GJ
(blueprint: lem-trf-etale-coordinate-derivations-jacobian).

Proof: Restrict the étale coordinate morphism to the affine open V. Identify affine space
with the spectrum of the polynomial ring over k and V with the spectrum of its sections.
The affine-spectrum correspondence identifies the restricted morphism with the k-algebra
map sending each variable to its pulled-back coordinate section. The affine étale criterion
makes this map étale, hence formally étale. Differential base change gives the isomorphism
A tensor_{k[T]} Omega_{k[T]/k} = Omega_{A/k}. Base-change the polynomial differential basis
and map it through this isomorphism; the image of 1 tensor dT_i is the required differential.
Reindex from ULift (Fin n) to Fin n. This works for n = 0 and for the zero section ring. -/
private theorem coordinateAffineBasis (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (n : ℕ)
    (x : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)))
    [x.IsOver (Spec (.of k))] [Etale x] (V : U.Opens) (hV : IsAffineOpen V) :
    letI : Algebra k Γ(U, V) :=
      ((ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop ≫
        U.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    ∃ b : Module.Basis (Fin n) Γ(U, V) (KaehlerDifferential k Γ(U, V)),
      ∀ i : Fin n, b i = KaehlerDifferential.D k Γ(U, V)
        (U.presheaf.map (homOfLE le_top).op
          (x.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up i)))) := by
  classical
  let : Algebra k Γ(U, V) :=
    ((ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop ≫
      U.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let σ := ULift.{u} (Fin n)
  let T := AffineSpace σ (Spec (.of k))
  let π := T ↘ Spec (.of k)
  let θ : MvPolynomial σ k →+* Γ(T, ⊤) :=
    MvPolynomial.eval₂Hom ((ΓSpecIso (.of k)).inv ≫ π.appTop).hom
      (AffineSpace.coord (Spec (.of k)))
  have hθiso : IsIso (CommRingCat.ofHom θ) := by
    have : IsIso ((ΓSpecIso (.of (MvPolynomial σ k))).hom ≫ CommRingCat.ofHom θ) := by
      rw [show (ΓSpecIso (.of (MvPolynomial σ k))).hom ≫ CommRingCat.ofHom θ =
        (AffineSpace.SpecIso σ (.of k)).hom.appTop from
          (AffineSpace.SpecIso_hom_appTop (n := σ) (.of k)).symm]
      infer_instance
    exact IsIso.of_isIso_comp_left (ΓSpecIso (.of (MvPolynomial σ k))).hom
      (CommRingCat.ofHom θ)
  let θe := RingEquiv.ofBijective θ (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom θ))
  let r := x.appLE ⊤ V le_top
  have hr : r.hom.Etale := x.etale_appLE (isAffineOpen_top T) hV le_top
  let ρ : MvPolynomial σ k →ₐ[k] Γ(U, V) :=
    MvPolynomial.aeval (fun j ↦ U.presheaf.map (homOfLE le_top).op
      (x.appTop (AffineSpace.coord (Spec (.of k)) j)))
  have hρ : ρ.toRingHom = r.hom.comp θ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change ρ (MvPolynomial.C a) = r (θ (MvPolynomial.C a))
      dsimp only [ρ, θ]
      rw [MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C]
      change U.presheaf.map (homOfLE le_top).op
        ((U ↘ Spec (.of k)).appTop ((ΓSpecIso (.of k)).inv a)) =
        U.presheaf.map (homOfLE le_top).op
          (x.appTop (π.appTop ((ΓSpecIso (.of k)).inv a)))
      have hx : π.appTop ≫ x.appTop = (U ↘ Spec (.of k)).appTop := by
        rw [← Scheme.Hom.comp_appTop]
        exact congrArg Scheme.Hom.appTop (comp_over x (Spec (.of k)))
      exact congrArg (fun f ↦ U.presheaf.map (homOfLE le_top).op
        (f ((ΓSpecIso (.of k)).inv a))) hx.symm
    · intro j
      simp [ρ, θ, r, Scheme.Hom.appLE]
  have hρet : ρ.toRingHom.Etale := by
    rw [hρ]
    exact RingHom.Etale.respectsIso.2 r.hom θe hr
  let : Algebra (MvPolynomial σ k) Γ(U, V) := ρ.toRingHom.toAlgebra
  let : IsScalarTower k (MvPolynomial σ k) Γ(U, V) :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (ρ.commutes a).symm)
  let : Algebra.Etale (MvPolynomial σ k) Γ(U, V) := hρet
  let e := ((KaehlerDifferential.mvPolynomialBasis k σ).baseChange Γ(U, V)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k
      (MvPolynomial σ k) Γ(U, V))
  refine ⟨e.reindex Equiv.ulift, fun i ↦ ?_⟩
  rw [Module.Basis.reindex_apply]
  dsimp only [e]
  rw [Module.Basis.map_apply]
  rw [Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  congr 1
  exact MvPolynomial.aeval_X _ _



private noncomputable def coordinateDerivation {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] {n : ℕ} (b : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (i : Fin n) : Derivation k A A :=
  (b.coord i).compDer (KaehlerDifferential.D k A)

private theorem coordinateDerivation_apply {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] {n : ℕ} (b : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (i : Fin n) (a : A) : coordinateDerivation b i a = b.repr (KaehlerDifferential.D k A a) i :=
  rfl

private theorem coordinateDerivation_coordinate {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] {n : ℕ} (z : Fin n → A)
    (b : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (hb : ∀ i, b i = KaehlerDifferential.D k A (z i)) (i j : Fin n) :
    coordinateDerivation b i (z j) = if i = j then 1 else 0 := by
  classical
  rw [coordinateDerivation_apply, ← hb j, Module.Basis.repr_self_apply]
  split_ifs with h <;> simp_all

private theorem coordinateEvaluation_bijective {k A M : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    {n : ℕ} (z : Fin n → A) (b : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (hb : ∀ i, b i = KaehlerDifferential.D k A (z i)) :
    Function.Bijective (fun E : Derivation k A M ↦ fun i ↦ E (z i)) := by
  constructor
  · intro E F h
    apply (KaehlerDifferential.linearMapEquivDerivation k A).symm.injective
    apply b.ext
    intro i
    simpa only [KaehlerDifferential.linearMapEquivDerivation_symm_apply, hb,
      Derivation.liftKaehlerDifferential_comp_D] using congrFun h i
  · intro f
    refine ⟨KaehlerDifferential.linearMapEquivDerivation k A (b.constr A f), ?_⟩
    funext i
    simp only [KaehlerDifferential.linearMapEquivDerivation_apply_apply, ← hb,
      Module.Basis.constr_basis]

private theorem coordinateDerivation_commute {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] {n : ℕ} (z : Fin n → A)
    (b : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (hb : ∀ i, b i = KaehlerDifferential.D k A (z i)) (i j : Fin n) (c : A) :
    coordinateDerivation b i (coordinateDerivation b j c) =
      coordinateDerivation b j (coordinateDerivation b i c) := by
  classical
  have h : ⁅coordinateDerivation b i, coordinateDerivation b j⁆ = 0 := by
    apply (coordinateEvaluation_bijective z b hb).injective
    funext l
    simp only [Derivation.commutator_apply, coordinateDerivation_coordinate z b hb]
    split_ifs <;> simp
  have hc := Derivation.congr_fun h c
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using hc

private theorem coordinateDerivation_differential {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] {n : ℕ} (z : Fin n → A)
    (b : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (hb : ∀ i, b i = KaehlerDifferential.D k A (z i)) (c : A) :
    KaehlerDifferential.D k A c =
      ∑ i : Fin n, coordinateDerivation b i c • KaehlerDifferential.D k A (z i) := by
  simpa only [coordinateDerivation_apply, Module.Basis.equivFun_apply, ← hb] using
    (b.sum_equivFun (KaehlerDifferential.D k A c)).symm

private theorem derivation_compare {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] {n : ℕ} (z : Fin n → A)
    (b : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (hb : ∀ i, b i = KaehlerDifferential.D k A (z i))
    (f : A →ₐ[k] B) (D : Derivation k A A) (E : Derivation k B B)
    (h : ∀ j, E (f (z j)) = f (D (z j))) (c : A) : E (f c) = f (D c) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ (f.commutes r).symm)
  have he : E.compAlgebraMap A = (Algebra.linearMap A B).compDer D := by
    apply (coordinateEvaluation_bijective z b hb).injective
    funext j
    exact h j
  exact Derivation.congr_fun he c

private theorem coordinateDerivation_natural {k A B : Type*}
    [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    {n : ℕ} (z : Fin n → A) (t : Fin n → B)
    (b : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (e : Module.Basis (Fin n) B (KaehlerDifferential k B))
    (hb : ∀ i, b i = KaehlerDifferential.D k A (z i))
    (he : ∀ i, e i = KaehlerDifferential.D k B (t i))
    (f : A →ₐ[k] B) (hf : ∀ j, f (z j) = t j) (i : Fin n) (c : A) :
    coordinateDerivation e i (f c) = f (coordinateDerivation b i c) := by
  classical
  apply derivation_compare z b hb f
  intro j
  rw [hf, coordinateDerivation_coordinate t e he, coordinateDerivation_coordinate z b hb]
  split_ifs <;> simp

private theorem coordinateDerivation_taylor {k A L : Type*}
    [CommRing k] [CommRing A] [CommRing L] [Algebra k A] [Algebra k L]
    {n : ℕ} (z : Fin n → A) (b : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (hb : ∀ i, b i = KaehlerDifferential.D k A (z i))
    (τ : A →ₐ[k] MvPowerSeries (Fin n) L) (a : Fin n → L)
    (hτ : ∀ j, τ (z j) = MvPowerSeries.C (a j) + MvPowerSeries.X j)
    (i : Fin n) (c : A) : MvPowerSeries.pderiv L i (τ c) =
      τ (coordinateDerivation b i c) := by
  classical
  apply derivation_compare z b hb τ (coordinateDerivation b i)
    ((MvPowerSeries.pderiv L i).restrictScalars k)
  intro j
  change MvPowerSeries.pderiv L i (τ (z j)) = _
  rw [hτ, coordinateDerivation_coordinate z b hb]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, MvPowerSeries.pderiv_X_of_ne (Ne.symm hij)]

private theorem iterated_comparison {ι A B : Type*} (D : ι → A → A) (E : ι → B → B)
    (f : A → B) (h : ∀ i c, E i (f c) = f (D i c)) (is : List ι) (c : A) :
    is.foldr (fun i s ↦ E i s) (f c) = f (is.foldr (fun i s ↦ D i s) c) := by
  induction is with
  | nil => rfl
  | cons i is ih => simpa only [List.foldr_cons, ih] using h i (is.foldr D c)

private noncomputable def coordinateRestriction (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (V W : U.Opens) (hWV : W ≤ V) :
    letI := etaleCoordinateSectionAlgebra k U V
    letI := etaleCoordinateSectionAlgebra k U W
    Γ(U, V) →ₐ[k] Γ(U, W) := by
  letI := etaleCoordinateSectionAlgebra k U V
  letI := etaleCoordinateSectionAlgebra k U W
  refine { (U.presheaf.map (homOfLE hWV).op).hom with commutes' := ?_ }
  intro r
  change U.presheaf.map (homOfLE hWV).op
    (U.presheaf.map (homOfLE le_top).op
      (((ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop) r)) =
    U.presheaf.map (homOfLE le_top).op
      (((ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop) r)
  have h : U.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      U.presheaf.map (homOfLE hWV).op =
      U.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun f ↦ f (((ΓSpecIso (.of k)).inv ≫
    (U ↘ Spec (.of k)).appTop) r)) h

private noncomputable def coordinateGerm (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (V : U.Opens) (p : U) (hp : p ∈ V) :
    letI := etaleCoordinateSectionAlgebra k U V
    letI := etaleCoordinateStalkAlgebra k U p
    Γ(U, V) →ₐ[k] U.presheaf.stalk p := by
  letI := etaleCoordinateSectionAlgebra k U V
  letI := etaleCoordinateStalkAlgebra k U p
  refine { (U.presheaf.germ V p hp).hom with commutes' := ?_ }
  intro r
  exact U.presheaf.germ_res_apply (homOfLE le_top) p hp
    (((ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop) r)

private theorem coordinateRestriction_coordinate (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (n : ℕ)
    (x : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)))
    (V W : U.Opens) (hWV : W ≤ V) (i : Fin n) :
    coordinateRestriction k U V W hWV (etaleCoordinateSection k U n x V i) =
      etaleCoordinateSection k U n x W i := by
  change U.presheaf.map (homOfLE hWV).op
    (U.presheaf.map (homOfLE le_top).op _) = U.presheaf.map (homOfLE le_top).op _
  have h : U.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      U.presheaf.map (homOfLE hWV).op =
      U.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun f ↦ f (x.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up i)))) h

private theorem coordinateGerm_coordinate (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (n : ℕ)
    (x : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)))
    (V : U.Opens) (p : U) (hp : p ∈ V) (i : Fin n) :
    coordinateGerm k U V p hp (etaleCoordinateSection k U n x V i) =
      U.presheaf.germ ⊤ p trivial (x.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up i))) :=
  U.presheaf.germ_res_apply (homOfLE le_top) p hp _

private theorem coordinateStalkBasis (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] (n : ℕ)
    (x : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)))
    [x.IsOver (Spec (.of k))] [Etale x] (p : U) :
    letI := etaleCoordinateStalkAlgebra k U p
    ∃ b : Module.Basis (Fin n) (U.presheaf.stalk p)
        (KaehlerDifferential k (U.presheaf.stalk p)),
      ∀ i, b i = KaehlerDifferential.D k (U.presheaf.stalk p)
        (U.presheaf.germ ⊤ p trivial
          (x.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up i)))) := by
  classical
  let := etaleCoordinateStalkAlgebra k U p
  obtain ⟨V, hV, hp, _⟩ := exists_isAffineOpen_mem_and_subset (X := U) (x := p)
    (U := ⊤) trivial
  let := etaleCoordinateSectionAlgebra k U V
  let : Algebra Γ(U, V) (U.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk U.presheaf ⟨p, hp⟩
  let : IsScalarTower k Γ(U, V) (U.presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ (coordinateGerm k U V p hp).commutes r |>.symm)
  let := hV.isLocalization_stalk ⟨p, hp⟩
  let : Algebra.FormallyEtale Γ(U, V) (U.presheaf.stalk p) :=
    Algebra.FormallyEtale.of_isLocalization
      (Rₘ := U.presheaf.stalk p) (hV.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl
  obtain ⟨b, hb⟩ := coordinateAffineBasis k U n x V hV
  let e := (b.baseChange (U.presheaf.stalk p)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k Γ(U, V) (U.presheaf.stalk p))
  refine ⟨e, fun i ↦ ?_⟩
  change (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
    k Γ(U, V) (U.presheaf.stalk p)) ((b.baseChange (U.presheaf.stalk p)) i) = _
  rw [Module.Basis.baseChange_apply, hb,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  exact congrArg (KaehlerDifferential.D k (U.presheaf.stalk p))
    (coordinateGerm_coordinate k U n x V p hp i)

/-- Étale coordinates give regular coordinate derivations and formal Taylor comparison,
including zero coordinates and the empty affine open.
Source: Stacks Project, algebra.tex, Tags 0H93 (differential base change), 00RX (polynomial
basis) and 00RO (universal derivation); more-algebra.tex, Tag 07PE(2), and schemes.tex, 01HV
(blueprint: lem-trf-etale-coordinate-derivations-jacobian).

Proof:
1. Restrict the étale map to each affine open. The affine-spectrum correspondence identifies
   it with the k-algebra map from the polynomial ring taking variables to the given sections.
   The affine étale criterion, formally étale differential base change, and the polynomial
   Kähler basis give the basis of coordinate differentials, also for zero variables.
2. The universal derivation identifies derivations into any module with linear maps out of
   the differential module. Evaluating on its basis is bijective. The standard tuples give
   the unique coordinate derivations; applying the dual maps gives the displayed formula
   for dc. Each finite iterate remains an element of the ring of regular functions.
3. Expand the Leibniz rule for the commutator. Mixed terms cancel, so it is a derivation.
   It kills all coordinate functions, hence vanishes by the evaluation bijection.
4. Restriction followed by differentiation and differentiation followed by restriction are
   derivations with the same coordinate values. The evaluation bijection identifies them.
   The affine-stalk localization theorem and unique localization extension (07PE(2)) give
   local derivations by D(a/s)=D(a)/s-aD(s)/s². Uniqueness makes them independent of the
   affine neighbourhood and makes their commutators zero.
5. The partial derivative after τ and τ after the coordinate derivative are k-derivations
   into the series ring, considered as an A-module through τ. Their coordinate values agree,
   hence evaluation bijectivity identifies them. Induction on a word gives all iterates.
   If τ extends to a stalk, differentiating an inverse gives the same quotient rule, hence
   the same comparison for every germ; induction again gives all iterates.
6. For n=0 the differential module and all derivations vanish and all sums are empty.
   The empty word comparison is the identity. No factorials are inverted, so all
   characteristics and field extensions are included. For the empty affine open its ring
   and modules are zero, and there is no unital map from it to a nonzero series ring. -/
theorem hasEtaleCoordinateCalculus (k : Type u) [Field k] (U : Scheme.{u})
    [U.Over (Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))] (n : ℕ)
    (x : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)))
    [x.IsOver (Spec (.of k))] [Etale x] : HasEtaleCoordinateCalculus.{u, v, w} k U n x := by
  classical
  let b (V : U.Opens) (hV : IsAffineOpen V) :
      letI := etaleCoordinateSectionAlgebra k U V
      Module.Basis (Fin n) Γ(U, V) (KaehlerDifferential k Γ(U, V)) :=
    (coordinateAffineBasis k U n x V hV).choose
  have hb (V : U.Opens) (hV : IsAffineOpen V) :
      ∀ i, b V hV i = @KaehlerDifferential.D k Γ(U, V) _ _
        (etaleCoordinateSectionAlgebra k U V) (etaleCoordinateSection k U n x V i) :=
    (coordinateAffineBasis k U n x V hV).choose_spec
  let z (p : U) (i : Fin n) := U.presheaf.germ ⊤ p trivial
    (x.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up i)))
  let e (p : U) :
      letI := etaleCoordinateStalkAlgebra k U p
      Module.Basis (Fin n) (U.presheaf.stalk p)
        (KaehlerDifferential k (U.presheaf.stalk p)) :=
    (coordinateStalkBasis k U n x p).choose
  have he (p : U) : ∀ i, e p i = @KaehlerDifferential.D k (U.presheaf.stalk p) _ _
      (etaleCoordinateStalkAlgebra k U p) (z p i) :=
    (coordinateStalkBasis k U n x p).choose_spec
  let D (V : U.Opens) (hV : IsAffineOpen V) (i : Fin n) :
      EtaleCoordinateSectionDerivation k U V := by
    let := etaleCoordinateSectionAlgebra k U V
    exact coordinateDerivation (b V hV) i
  let d (p : U) (i : Fin n) : EtaleCoordinateStalkDerivation k U p := by
    let := etaleCoordinateStalkAlgebra k U p
    exact coordinateDerivation (e p) i
  refine ⟨D, d, ?_, ?_⟩
  · intro V hV
    let := etaleCoordinateSectionAlgebra k U V
    refine ⟨⟨b V hV, hb V hV⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro M _ _
      let : Module k M := Module.compHom M (algebraMap k Γ(U, V))
      let : IsScalarTower k Γ(U, V) M := IsScalarTower.of_compHom k Γ(U, V) M
      exact coordinateEvaluation_bijective (etaleCoordinateSection k U n x V) (b V hV)
        (hb V hV)
    · exact coordinateDerivation_coordinate (etaleCoordinateSection k U n x V) (b V hV)
        (hb V hV)
    · intro i E hE
      apply (coordinateEvaluation_bijective (etaleCoordinateSection k U n x V)
        (b V hV) (hb V hV)).injective
      funext j
      exact (hE j).trans
        (coordinateDerivation_coordinate (etaleCoordinateSection k U n x V)
          (b V hV) (hb V hV) i j).symm
    · exact coordinateDerivation_commute (etaleCoordinateSection k U n x V) (b V hV)
        (hb V hV)
    · exact coordinateDerivation_differential (etaleCoordinateSection k U n x V) (b V hV)
        (hb V hV)
    · intro W hW hWV i c
      let := etaleCoordinateSectionAlgebra k U W
      exact (coordinateDerivation_natural (etaleCoordinateSection k U n x V)
        (etaleCoordinateSection k U n x W) (b V hV) (b W hW) (hb V hV) (hb W hW)
        (coordinateRestriction k U V W hWV)
        (coordinateRestriction_coordinate k U n x V W hWV) i c).symm
    · intro p hp i c
      let := etaleCoordinateStalkAlgebra k U p
      exact coordinateDerivation_natural (etaleCoordinateSection k U n x V) (z p)
        (b V hV) (e p) (hb V hV) (he p) (coordinateGerm k U V p hp)
        (coordinateGerm_coordinate k U n x V p hp) i c
    · intro L _ _ τ a hτ
      have hcomp (i : Fin n) (c : Γ(U, V)) :
          MvPowerSeries.pderiv L i (τ c) = τ (D V hV i c) :=
        coordinateDerivation_taylor (etaleCoordinateSection k U n x V) (b V hV)
          (hb V hV) τ a hτ i c
      refine ⟨hcomp, ?_, ?_⟩
      · exact iterated_comparison (fun i ↦ D V hV i) (fun i ↦ MvPowerSeries.pderiv L i)
          τ hcomp
      · intro p hp
        let := etaleCoordinateStalkAlgebra k U p
        intro τp hτp
        have hz (j : Fin n) : τp (z p j) =
            MvPowerSeries.C (a j) + MvPowerSeries.X j := by
          calc
            τp (z p j) = τp (U.presheaf.germ V p hp
                (etaleCoordinateSection k U n x V j)) :=
              congrArg τp (coordinateGerm_coordinate k U n x V p hp j).symm
            _ = τ (etaleCoordinateSection k U n x V j) := hτp _
            _ = _ := hτ j
        have hcomp' (i : Fin n) (c : U.presheaf.stalk p) :
            MvPowerSeries.pderiv L i (τp c) = τp (d p i c) :=
          coordinateDerivation_taylor (z p) (e p) (he p) τp a hz i c
        exact ⟨hcomp', iterated_comparison (fun i ↦ d p i)
          (fun i ↦ MvPowerSeries.pderiv L i) τp hcomp'⟩
  · intro p i j c
    let := etaleCoordinateStalkAlgebra k U p
    exact coordinateDerivation_commute (z p) (e p) (he p) i j c

end AlgebraicGeometry.Scheme
