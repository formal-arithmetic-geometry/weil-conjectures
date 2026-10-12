/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.FieldTheory.GaloisAutomorphismExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Realizing equivariant germs on a one-point etale scheme

Source: Stacks Project, Tags 04JM and 03QW.
(blueprint: lem-exc-field-equivariant-germs-one-point).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- A separable embedding lands in the embedded separable closure, even if Ω is
transcendental over K. The relative separable closure in Ω is another separable
closure of K, and the specified embedding of Ks induces an isomorphism onto it.
Source: Stacks Project, Tag 03QW, finite separable residue-field factorization. -/
private theorem factor_separable_embedding
    (K Ks Ω L : Type u) [Field K] [Field Ks] [Field Ω] [Field L]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra K L]
    [Algebra.IsSeparable K L] (σ : L →ₐ[K] Ω) :
    ∃ σs : L →ₐ[K] Ks,
      (IsScalarTower.toAlgHom K Ks Ω).comp σs = σ := by
  let A := separableClosure K Ω
  let j : Ks →ₐ[K] A := (IsScalarTower.toAlgHom K Ks Ω).codRestrict A.toSubalgebra
    (fun x ↦ (mem_separableClosure_iff.mpr
      ((Algebra.IsSeparable.isSeparable K x).map
        (IsScalarTower.toAlgHom K Ks Ω) (RingHom.injective _))))
  have : IsSepClosed Ks := IsSepClosure.sep_closed K
  let e : Ks ≃ₐ[K] A := AlgEquiv.ofBijective j
    (Normal.toIsAlgebraic.algHom_bijective₂ j (IsSepClosed.lift : A →ₐ[K] Ks)).1
  let σA : L →ₐ[K] A := σ.codRestrict A.toSubalgebra
    (fun x ↦ mem_separableClosure_iff.mpr
      ((Algebra.IsSeparable.isSeparable K x).map σ σ.injective))
  refine ⟨e.symm.toAlgHom.comp σA, ?_⟩
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply (σA x))

/-- Conjugacy of separable embeddings, with the automorphism's restriction to Ks.
Source: Stacks Project, Tag 03QW. Factor both embeddings through Ks, extend the
isomorphism of their images by normality, and then extend to Ω. -/
private theorem separable_embeddings_conjugate
    (K Ks Ω L : Type u) [Field K] [Field Ks] [Field Ω] [Field L]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra K L]
    [Algebra.IsSeparable K L] (σ σ' : L →ₐ[K] Ω) :
    ∃ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
      (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω) ∧ τ.toAlgHom.comp σ = σ' := by
  obtain ⟨σs, hσ⟩ := factor_separable_embedding K Ks Ω L σ
  obtain ⟨σs', hσ'⟩ := factor_separable_embedding K Ks Ω L σ'
  let e := σs.equivFieldRange.symm.trans σs'.equivFieldRange
  let g := e.liftNormal Ks
  have hg : g.toAlgHom.comp σs = σs' := by
    ext x
    have h := e.liftNormal_commutes Ks (σs.equivFieldRange x)
    simpa [e, g] using h
  obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g
  refine ⟨g, τ, hτ, ?_⟩
  ext x
  have hσx := DFunLike.congr_fun hσ x
  have hσ'x := DFunLike.congr_fun hσ' x
  have hgx := DFunLike.congr_fun hg x
  have hτx := DFunLike.congr_fun hτ (σs x)
  change τ (σ x) = σ' x
  change algebraMap Ks Ω (σs x) = σ x at hσx
  change algebraMap Ks Ω (σs' x) = σ' x at hσ'x
  change g (σs x) = σs' x at hgx
  change algebraMap Ks Ω (g (σs x)) = τ (algebraMap Ks Ω (σs x)) at hτx
  rw [← hσx, ← hτx, hgx, hσ'x]

/-- Geometric lifts of a one-point etale scheme are conjugate.
Source: Stacks Project, Tags 02GL and 03QW. The residue-field point is an
isomorphism onto the reduced one-point scheme. Etaleness makes the residue
extension separable. Apply conjugacy of its two embeddings into Ω. -/
private theorem onePoint_lifts_transitive
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ x x' : p.fiber.obj X,
      ∃ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
        (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω) ∧
        x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left := by
  classical
  dsimp only
  intro x x'
  let y : X.left := Classical.choice (inferInstance : Nonempty X.left)
  let q : X.left ⟶ Spec (.of K) := X.hom
  let L := X.left.residueField y
  let j := X.left.fromSpecResidueField y
  let i := Spec.homEquiv (j ≫ q)
  let : Algebra K L := i.hom.toAlgebra
  have : IsClosedImmersion ((Spec (.of K)).fromSpecResidueField (q y)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)
  have : Surjective ((Spec (.of K)).fromSpecResidueField (q y)) :=
    ⟨fun z ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective
    ((Spec (.of K)).fromSpecResidueField (q y))
  have : Etale (Spec.map (q.residueFieldMap y)) :=
    HasRingHomProperty.Spec_iff.mpr (q.etale_residueFieldMap y)
  have : Etale (j ≫ q) := by
    dsimp [j]
    rw [← q.SpecMap_residueFieldMap_fromSpecResidueField y]
    infer_instance
  have hi : Spec.map i = j ≫ q := Spec.homEquiv.symm_apply_apply _
  have : Etale (Spec.map i) := hi ▸ ‹Etale (j ≫ q)›
  have : Algebra.Etale K L := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact HasRingHomProperty.Spec_iff.mp ‹Etale (Spec.map i)›
  have : Algebra.IsSeparable K L :=
    (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
  have : DiscreteTopology X.left := inferInstance
  have : IsClosedImmersion j := .of_isPreimmersion j (isClosed_discrete _)
  have : Surjective j := ⟨fun z ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : IsReduced X.left := isReduced_of_etale q
  have : IsIso j := isIso_of_isClosedImmersion_of_surjective j
  let t (a : (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) := a.left ≫ inv j
  have ht (a) : t a ≫ Spec.map i =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [hi]
    dsimp [t]
    rw [Category.assoc, IsIso.inv_hom_id_assoc]
    exact Over.w a
  let σ (a) : L →ₐ[K] Ω :=
    { (Spec.homEquiv (t a)).hom with
      commutes' := by
        intro k
        have h := ht a
        rw [← Spec.homEquiv.symm_apply_apply (t a)] at h
        change Spec.map (Spec.homEquiv (t a)) ≫ Spec.map i = _ at h
        rw [← Spec.map_comp] at h
        have h' := Spec.homEquiv.symm.injective h
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h') k }
  have hσ (a) : Spec.map (CommRingCat.ofHom (σ a).toRingHom) = t a :=
    Spec.homEquiv.symm_apply_apply _
  obtain ⟨g, τ, hτ, h⟩ := separable_embeddings_conjugate K Ks Ω L (σ x) (σ x')
  refine ⟨g, τ, hτ, ?_⟩
  have ht' : t x' = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ t x := by
    rw [← hσ, ← hσ, ← Spec.map_comp]
    exact congrArg (fun f : L →ₐ[K] Ω ↦
      Spec.map (CommRingCat.ofHom f.toRingHom)) h.symm
  have hx (a) : t a ≫ j = a.left := by
    dsimp [t]
    simp
  rw [← hx x', ht', Category.assoc, hx x]

/-- Source: Stacks Project, Tag 04JM, direct proof of lemma-global-sections-point,
and Tag 03QW, section-galois-action-stalks.
(blueprint: lem-exc-field-equivariant-germs-one-point).

Proof: A nonempty one-point etale K-scheme is the spectrum of a finite separable
extension of K: apply etale_fibre_discrete_separable_points to its fibre over the
unique point of Spec K, identify that fibre with the original scheme, and use its
unique open singleton. Choose a lift and embed its residue field as a finite
intermediate field L of Ks. Let A be the subfield of Omega algebraic over K.
It is algebraically closed: a root in Omega of a polynomial over A is algebraic
also over K, hence lies in A. Every geometric lift on an etale K-scheme factors
uniquely through Spec A, because its residue field is finite separable over K.
These factorizations identify the pointed-neighbourhood categories, stalk colimits,
and germ maps for A and Omega. Every K-automorphism of Ks extends to A, then to
Omega: fix a transcendence basis over A and extend across the algebraic closure
of the resulting rational-function field. Every stalk element has a representative,
so the assumed germ formula identifies rho with the canonical Galois action from
fieldSections_stalkInvariants, under this stalk identification.
For g fixing L choose such an extension; it fixes the chosen lift. Covariance
of f says its value there is invariant under L.fixingSubgroup. The surjectivity
of the invariant-section bijection gives a section with that germ. Every other
lift corresponds to an embedding L into Ks, which extends to a K-automorphism
of Ks and then to Omega. Apply covariance of f and the germ formula to show
that the same section has the prescribed germ at every lift. Transport the
section back across the one-point scheme isomorphism. No gluing over distinct
components is asserted or used in this lemma. -/
/- Source: Stacks Project, Tag 04JM.
The invariant-section reconstruction
for the selected geometric lift of a one-point etale scheme.
(blueprint: lem-exc-field-equivariant-germs-one-point-selected-lift).
The proof chooses the finite separable residue field of the unique point, applies
`fieldSections_stalkInvariants`, and transports the resulting invariant section
across the pointed isomorphism. -/
theorem onePoint_selected_lift_section
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (x₀ : p.fiber.obj X) (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left),
          f x' = ρ g (f x)) →
        ∃ z : F.obj.obj (op X),
          p.toPresheafFiber X x₀ F.obj z = f x₀ := by sorry

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Tags 02GL and 03QW.
(blueprint: lem-exc-field-equivariant-germs-one-point-propagation).

Proof: The residue-field point of the reduced one-point etale scheme X is an
isomorphism; its residue field L is separable over K. The two lifts x₀ and x
therefore give K-embeddings of L into Ω. Every separable embedding into Ω
factors through the specified Ks: the embedding of Ks into the relative
separable closure of K in Ω is an isomorphism between separable closures.
Normality of Ks/K extends the isomorphism between the images of the two
L-embeddings to g in Gal(Ks/K). Extend g to τ on Ω using
exists_algEquiv_extending_separableClosure; this theorem handles transcendental
Ω by a transcendence basis. Transport through the residue-field isomorphism
to obtain x.left = Spec(τ) ≫ x₀.left. The germ-action hypothesis identifies
the germ at x with ρ g applied to the germ at x₀. Substitute the given equality
at x₀, then apply covariance of f to identify the result with f x. -/
theorem onePoint_propagate_from_selected_lift
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (x₀ : p.fiber.obj X) (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left),
          f x' = ρ g (f x)) →
        ∀ (z : F.obj.obj (op X)),
          p.toPresheafFiber X x₀ F.obj z = f x₀ →
          ∀ x : p.fiber.obj X,
            p.toPresheafFiber X x F.obj z = f x := by
  dsimp only
  intro x₀ ρ hρ f hf z hz x
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  obtain ⟨g, τ, hτ, hx⟩ := onePoint_lifts_transitive K Ks Ω X x₀ x
  calc
    _ = ρ g (p.toPresheafFiber X x₀ F.obj z) := (hρ g τ hτ X x₀ x hx z).symm
    _ = ρ g (f x₀) := congrArg (ρ g) hz
    _ = f x := (hf g τ hτ x₀ x hx).symm

set_option linter.unusedVariables false in
theorem field_equivariant_germ_family_section_onePoint
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left),
          f x' = ρ g (f x)) →
        ∃ z : F.obj.obj (op X), ∀ x : p.fiber.obj X,
          p.toPresheafFiber X x F.obj z = f x  := by
  classical
  dsimp
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  intro ρ hρ f hf
  have hnon : Nonempty (p.fiber.obj X) := by
    let y : X.left := Classical.choice (inferInstance : Nonempty X.left)
    obtain ⟨l, hl, hy⟩ := exists_fac_of_etale_of_isSepClosed X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) y (Subsingleton.elim (α := Spec (.of K)) _ _)
    exact ⟨Over.homMk l hl⟩
  let x₀ : p.fiber.obj X := Classical.choice hnon
  obtain ⟨z, hz⟩ := onePoint_selected_lift_section K Ks Ω F X x₀ ρ hρ f hf
  refine ⟨z, ?_⟩
  intro x
  exact onePoint_propagate_from_selected_lift K Ks Ω F X x₀ ρ hρ f hf z
    (hz) x

end AlgebraicGeometry.Scheme
