/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Exact.Basic
import Sheaf.AlgebraicGeometry.Cohomology.CohomologyMayerVietorisExtPresentation
/-! # Mayer--Vietoris naturality before scalar extension
Source: Stacks Project, Tags 01EB and 02KH.
(blueprint: lem-pc-cohomology-mayer-vietoris-inverse-image)
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
private noncomputable def extTransport
    {T : Type u} [CommRing T]
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {P Q F : C} (ρ : T →+* End F)
    {A B : Type u} [AddCommGroup A] [AddCommGroup B] [Module T A] [Module T B]
    {n k m : ℕ} (α : CategoryTheory.Abelian.Ext P Q k) (h : k + n = m)
    (e : A ≃+ CategoryTheory.Abelian.Ext Q F n) (e' : B ≃+ CategoryTheory.Abelian.Ext P F m)
    (he : ∀ a x, e (a • x) = (e x).comp (CategoryTheory.Abelian.Ext.mk₀ (ρ a)) (add_zero n))
    (he' : ∀ a x, e' (a • x) = (e' x).comp (CategoryTheory.Abelian.Ext.mk₀ (ρ a)) (add_zero m)) :
    A →ₗ[T] B where
  __ := e'.symm.toAddMonoidHom.comp ((α.precomp F h).comp e.toAddMonoidHom)
  map_smul' a x := by
    apply e'.injective
    change e' (e'.symm (α.comp (e (a • x)) h)) =
      e' (a • e'.symm (α.comp (e x) h))
    rw [e'.apply_symm_apply, he, he', e'.apply_symm_apply]
    exact (CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero α (e x)
      (CategoryTheory.Abelian.Ext.mk₀ (ρ a)) h).symm
private lemma extTransport_apply
    {T : Type u} [CommRing T]
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {P Q F : C} (ρ : T →+* End F)
    {A B : Type u} [AddCommGroup A] [AddCommGroup B] [Module T A] [Module T B]
    {n k m : ℕ} (α : CategoryTheory.Abelian.Ext P Q k) (h : k + n = m)
    (e : A ≃+ CategoryTheory.Abelian.Ext Q F n) (e' : B ≃+ CategoryTheory.Abelian.Ext P F m)
    (he : ∀ a x, e (a • x) = (e x).comp (CategoryTheory.Abelian.Ext.mk₀ (ρ a)) (add_zero n))
    (he' : ∀ a x, e' (a • x) =
      (e' x).comp (CategoryTheory.Abelian.Ext.mk₀ (ρ a)) (add_zero m)) (x : A) :
    extTransport ρ α h e e' he he' x = e'.symm (α.comp (e x) h) := rfl
private lemma transport_exact
    {A B C D E F : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    (eA : A ≃+ D) (eB : B ≃+ E) (eC : C ≃+ F)
    (f : D →+ E) (g : E →+ F) (h : Function.Exact f g) :
    Function.Exact (fun x ↦ eB.symm (f (eA x))) (fun x ↦ eC.symm (g (eB x))) := by
  intro x
  change eC.symm (g (eB x)) = 0 ↔ ∃ y, eB.symm (f (eA y)) = x
  rw [eC.symm.map_eq_zero_iff, h]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨eA.symm y, ?_⟩
    simp only [eA.apply_symm_apply, hy, eB.symm_apply_apply]
  · rintro ⟨y, hy⟩
    refine ⟨eA y, ?_⟩
    apply eB.symm.injective
    simpa only [eB.symm_apply_apply] using hy
private theorem extRow_exact
    {T : Type u} [CommRing T]
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {K : ShortComplex C} (hK : K.ShortExact) {F : C} {ρ : T →+* End F}
    {A B I : ℕ → Type u}
    [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (I n)]
    [∀ n, Module T (A n)] [∀ n, Module T (B n)] [∀ n, Module T (I n)]
    (E : H.ExtRowPresentation T K F ρ A B I) :
    let r := fun n ↦ extTransport ρ (CategoryTheory.Abelian.Ext.mk₀ K.g) (zero_add n)
      (E.eX n) (E.eP n) (E.scalarX n) (E.scalarP n)
    let d := fun n ↦ extTransport ρ (CategoryTheory.Abelian.Ext.mk₀ K.f) (zero_add n)
      (E.eP n) (E.eI n) (E.scalarP n) (E.scalarI n)
    let δ := fun n ↦ extTransport ρ hK.extClass (by omega : 1 + n = n + 1)
      (E.eI n) (E.eX (n + 1)) (E.scalarI n) (E.scalarX (n + 1))
    Function.Injective (r 0) ∧
      ∀ n, Function.Exact (r n) (d n) ∧ Function.Exact (d n) (δ n) ∧
        Function.Exact (δ n) (r (n + 1)) := by
  refine ⟨?_, ?_⟩
  · have := hK.epi_g
    exact (E.eP 0).symm.injective.comp
      ((CategoryTheory.Abelian.Ext.precomp_mk₀_injective_of_epi F K.g).comp (E.eX 0).injective)
  · intro n
    refine ⟨?_, ?_, ?_⟩
    · exact transport_exact (E.eX n) (E.eP n) (E.eI n) _ _
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂' hK F n))
    · exact transport_exact (E.eP n) (E.eI n) (E.eX (n + 1)) _ _
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁' hK F n (n + 1) (by omega)))
    · exact transport_exact (E.eI n) (E.eX (n + 1)) (E.eP (n + 1)) _ _
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃' hK F n (n + 1) (by omega)))
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Ext transport elaboration unfolds large categorical terms.
/-- The original and pulled-back Mayer--Vietoris sequences are compatible with
`H.baseChangeLinear`, before tensoring. Neither flatness nor quasi-coherence is needed.

Source: Stacks Project, Tag 01EB, cohomology-lemma-mayer-vietoris, and Tag 02KH,
coherent-lemma-flat-base-change-cohomology, Mayer--Vietoris alternative.
(blueprint: lem-pc-cohomology-mayer-vietoris-inverse-image)

Proof: Form the Mayer--Vietoris sequences for M and its pullback using Tag 01EB.
Restriction and connecting maps commute with scalar endomorphisms of M by
naturality, giving R-linear maps in the original sequence and S-linear maps in
the pulled-back sequence. The inverse-image opens cover the pullback scheme;
the cartesian open-subscheme isomorphisms and pullback composition isomorphisms
identify their restricted cohomology with the displayed B terms. Exact inverse
image on abelian sheaves transports the Mayer--Vietoris short exact sequence of
free abelian sheaves to that for the inverse-image cover: inverse image of the
free sheaf represented by W is the free sheaf represented by its preimage,
since both represent sections of pushforward on W under the adjunction and
the free-sheaf universal property. These identifications commute with inclusions.
Applying Ext to this
short exact sequence gives the original cohomology sequence. The constant-sheaf
comparison and adjoint coefficient map used in H.baseChangeLinear induce a
morphism to the pulled-back sequence. Ext functoriality gives the restriction
and difference squares. Each connecting homomorphism is Yoneda composition with
the short exact sequence class; exact inverse image preserves that class and
Yoneda composition, giving the boundary square. The free-sheaf identifications
for the union and individual opens identify these vertical maps with precisely
H.baseChangeLinear. The initial injections and exactness of the two rows come
from their Mayer--Vietoris sequences. No tensor product or flatness is used. -/
theorem H.baseChangeLinear_mayerVietoris
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let A := fun (W : X.Opens) (n : ℕ) ↦
      HOver (W.ι ≫ f) ((pullback W.ι).obj M) n
    let B := fun (W : X.Opens) (n : ℕ) ↦
      HOver (baseChangeSnd (S := S) (W.ι ≫ f))
        (baseChangedModule (S := S) (W.ι ≫ f) ((pullback W.ι).obj M)) n
    let AX := fun n : ℕ ↦ HOver f M n
    let BX := fun n : ℕ ↦
      HOver (baseChangeSnd (S := S) f) (baseChangedModule (S := S) f M) n
    let β := fun (W : X.Opens) (n : ℕ) ↦
      H.baseChangeLinear (S := S) (W.ι ≫ f) ((pullback W.ι).obj M) n
    let βX := fun n : ℕ ↦ H.baseChangeLinear (S := S) f M n
    ∃ (r : ∀ n : ℕ, AX n →ₗ[R] A U n × A V n)
      (d : ∀ n : ℕ, A U n × A V n →ₗ[R] A (U ⊓ V) n)
      (δ : ∀ n : ℕ, A (U ⊓ V) n →ₗ[R] AX (n + 1))
      (r' : ∀ n : ℕ, BX n →ₗ[S] B U n × B V n)
      (d' : ∀ n : ℕ, B U n × B V n →ₗ[S] B (U ⊓ V) n)
      (δ' : ∀ n : ℕ, B (U ⊓ V) n →ₗ[S] BX (n + 1)),
      Function.Injective (r 0) ∧ Function.Injective (r' 0) ∧
      (∀ n : ℕ, Function.Exact (r n) (d n) ∧
        Function.Exact (d n) (δ n) ∧ Function.Exact (δ n) (r (n + 1))) ∧
      (∀ n : ℕ, Function.Exact (r' n) (d' n) ∧
        Function.Exact (d' n) (δ' n) ∧ Function.Exact (δ' n) (r' (n + 1))) ∧
      (∀ (n : ℕ) (x : AX n), r' n (βX n x) =
        (β U n (r n x).1, β V n (r n x).2)) ∧
      (∀ (n : ℕ) (x : A U n × A V n),
        d' n (β U n x.1, β V n x.2) = β (U ⊓ V) n (d n x)) ∧
      (∀ (n : ℕ) (x : A (U ⊓ V) n),
        δ' n (β (U ⊓ V) n x) = βX (n + 1) (δ n x)) := by
  classical
  dsimp only
  obtain ⟨K, hK, E, E', hx, hp, hi⟩ :=
    H.exists_mayerVietoris_extPresentation (S := S) f M U V hcover
  let G := invImage (baseChangeFst (S := S) f)
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let N := (SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
    (baseChangedModule (S := S) f M)
  let ρ := (scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
  let τ := (scalarRep (baseChangedModule (S := S) f M)).comp
    (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
  let hK' := hK.map_of_exact G
  let r := fun n ↦ extTransport ρ (CategoryTheory.Abelian.Ext.mk₀ K.g) (zero_add n)
    (E.eX n) (E.eP n) (E.scalarX n) (E.scalarP n)
  let d := fun n ↦ extTransport ρ (CategoryTheory.Abelian.Ext.mk₀ K.f) (zero_add n)
    (E.eP n) (E.eI n) (E.scalarP n) (E.scalarI n)
  let δ := fun n ↦ extTransport ρ hK.extClass (by omega : 1 + n = n + 1)
    (E.eI n) (E.eX (n + 1)) (E.scalarI n) (E.scalarX (n + 1))
  let r' := fun n ↦ extTransport τ (CategoryTheory.Abelian.Ext.mk₀ (K.map G).g) (zero_add n)
    (E'.eX n) (E'.eP n) (E'.scalarX n) (E'.scalarP n)
  let d' := fun n ↦ extTransport τ (CategoryTheory.Abelian.Ext.mk₀ (K.map G).f) (zero_add n)
    (E'.eP n) (E'.eI n) (E'.scalarP n) (E'.scalarI n)
  let δ' := fun n ↦ extTransport τ hK'.extClass (by omega : 1 + n = n + 1)
    (E'.eI n) (E'.eX (n + 1)) (E'.scalarI n) (E'.scalarX (n + 1))
  obtain ⟨hr, he⟩ := extRow_exact hK E
  obtain ⟨hr', he'⟩ := extRow_exact hK' E'
  refine ⟨r, d, δ, r', d', δ', hr, hr', he, he', ?_, ?_, ?_⟩
  · intro n x
    apply (E'.eP n).injective
    rw [extTransport_apply, (E'.eP n).apply_symm_apply]
    change (CategoryTheory.Abelian.Ext.mk₀ (G.map K.g)).comp
        (E'.eX n (H.baseChangeLinear (S := S) f M n x)) (zero_add n) = _
    rw [hx, hp]
    rw [extTransport_apply, (E.eP n).apply_symm_apply]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
      CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀,
      CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
  · intro n x
    apply (E'.eI n).injective
    rw [extTransport_apply, (E'.eI n).apply_symm_apply]
    change (CategoryTheory.Abelian.Ext.mk₀ (G.map K.f)).comp
        (E'.eP n _) (zero_add n) = _
    rw [hp, hi]
    rw [extTransport_apply, (E.eI n).apply_symm_apply]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
      CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀,
      CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
  · intro n x
    apply (E'.eX (n + 1)).injective
    rw [extTransport_apply, (E'.eX (n + 1)).apply_symm_apply]
    change hK'.extClass.comp (E'.eI n _) (by omega : 1 + n = n + 1) = _
    rw [hi, hx]
    rw [extTransport_apply, (E.eX (n + 1)).apply_symm_apply]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
      CategoryTheory.Abelian.Ext.mapExactFunctor_extClass,
      CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
end AlgebraicGeometry.Scheme.Modules
