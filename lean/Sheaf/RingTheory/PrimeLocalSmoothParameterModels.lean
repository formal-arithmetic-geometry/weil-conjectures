module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Data.ZMod.Basic
public import Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.PrimeFieldParameterRegularMap
import Sheaf.RingTheory.SmoothParameterQuotientDiagram
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.PopescuSmoothing
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Data.Fintype.EquivFin

/-! # Smooth models preserving a complete regular local ring's parameters

Source: Stacks Project, Algebra, Tags 032A and 0C0S; More on Algebra,
Tags 07DY and 0H7U; Smoothing Ring Maps, Tag 07GC; Categories, Tag 0032
(blueprint: lem-per-prime-local-smooth-parameter-models).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- Restrict a polynomial algebra to its coefficient algebra, retaining its carrier. -/
private noncomputable def restrictParameterBase (k : Type u) [CommRing k] (d : ℕ) :
    CommAlgCat.{u} (MvPolynomial (Fin d) k) ⥤ CommAlgCat.{u} k where
  obj A :=
    letI : Algebra k A := Algebra.compHom A (algebraMap k (MvPolynomial (Fin d) k))
    CommAlgCat.of k A
  map {A B} f := by
    letI : Algebra k A := Algebra.compHom A (algebraMap k (MvPolynomial (Fin d) k))
    letI : Algebra k B := Algebra.compHom B (algebraMap k (MvPolynomial (Fin d) k))
    exact CommAlgCat.ofHom
      { toRingHom := f.hom.toRingHom
        commutes' r := f.hom.commutes (algebraMap k (MvPolynomial (Fin d) k) r) }


namespace IsLocalRing

/-- Simultaneous smooth models with parameters and their normalized residue quotients.
The quotient algebras `D.obj a` are identified with the actual parameter quotients by
algebra equivalences taking the quotient projection to `q.app a`. Thus naturality of
`q` forces precisely the induced quotient transition maps, without choices of maps.
The two `IsColimit` assertions specify the canonical ring colimit isomorphisms, and
the last commuting square identifies their quotient arrow with `residue B`.

Source: Stacks Project, Algebra, Tags 032A and 0C0S; More on Algebra, Tags 07DY,
07PS, 07PV, 0H7U and 07C0; Smoothing Ring Maps, Tag 07GC; Categories, Tag 0032
(blueprint: lem-per-prime-local-smooth-parameter-models).

Proof:
1. Cohen's coefficient-ring theorem gives a coefficient field in the equicharacteristic
complete local ring B. Choose d generators of its maximal ideal. The coefficient
coordinate theorem identifies B with the power series ring on these generators over
its residue field F. Successive variable quotients show that this is a regular sequence.
2. Localize P = k₀[T₁,...,T_d] at the origin. Evaluation extends to this localization
because polynomials with nonzero constant coefficient evaluate to units. The origin
localization is regular local of dimension d; the regular-sequence flatness criterion
makes its local map to B flat, with closed fibre F.
3. The prime field is a complete local G-ring, hence P is a G-ring. Its localized
completion map is regular. F is geometrically regular over the perfect prime field:
finite purely inseparable extensions of that field are trivial.
4. Apply the local closed-fibre regularity criterion and then the maximal-local
criterion to obtain regularity of P → B.
5. Popescu gives a small filtered diagram of smooth P-algebras with colimit B.
Directed cofinal reindexing preserves this cocone and its universal property.
6. Replace a directed preorder J by the poset J × ℕ, ordered by equality or by
strict increase of the second coordinate and weak increase of the first. Compatible
cocones are unchanged, because any two copies of a stage map identically to a later copy.
7. Quotient the stages by the variables. Smooth base change makes these quotients
smooth over k₀. Maps to F make them nonzero. Smooth ascent of regularity gives regular
Noetherian rings for both the stages and the quotients.
8. Flatness of smooth P-algebras preserves injective multiplication on each prefix
quotient of the polynomial variables. The final quotient is nonzero, so each stage
sequence is regular. P-linearity preserves these sequences under transitions, and their
quotient projections are regular closed immersions of constant codimension d.
9. A compatible family of maps from the stage quotients is a family of maps from the
stages killing the parameters, hence a unique map from B killing its maximal ideal,
hence a unique map from F. This proves the second colimit with its displayed normalization;
affine spectra identify the limiting immersion with Spec F → Spec B.
10. Every prime invertible in B already has its inverse in k₀, hence in every stage.
For d = 0 the parameter lists are empty, B = F, and the quotient arrows are isomorphisms.
-/
theorem exists_prime_local_smooth_parameter_models
    (k₀ B : Type u) [Field k₀] [CommRing B] [Algebra k₀ B]
    (hprime : Nonempty (k₀ ≃+* ℚ) ∨
      ∃ p : ℕ, p.Prime ∧ Nonempty (k₀ ≃+* ZMod p))
    [IsRegularLocalRing B] [IsAdicComplete (maximalIdeal B) B] :
    ∃ (d : ℕ), ringKrullDim B = (d : WithBot ℕ∞) ∧
    ∃ (t : Fin d → B), Ideal.span (Set.range t) = maximalIdeal B ∧
      RingTheory.Sequence.IsRegular B (List.ofFn t) ∧
    ∃ (I : Type u) (_ : PartialOrder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (C : I ⥤ CommAlgCat.{u} k₀)
      (τ : (Functor.const I).obj (CommAlgCat.of k₀ (MvPolynomial (Fin d) k₀)) ⟶ C)
      (β : C ⟶ (Functor.const I).obj (CommAlgCat.of k₀ B)),
      (∀ a : I, (β.app a).hom.comp (τ.app a).hom = MvPolynomial.aeval t) ∧
      (∀ a : I, Smooth (Spec.map (CommRingCat.ofHom (τ.app a).hom.toRingHom))) ∧
      (∀ a : I, Nontrivial (C.obj a) ∧ IsRegularRing (C.obj a) ∧
        RingTheory.Sequence.IsRegular (C.obj a)
          (List.ofFn fun i : Fin d ↦ (τ.app a).hom (MvPolynomial.X i))) ∧
      (∀ (ℓ : ℕ), ℓ.Prime → IsUnit (ℓ : B) → ∀ a : I, IsUnit (ℓ : C.obj a)) ∧
      Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} k₀) CommRingCat.{u}).mapCocone
        { pt := CommAlgCat.of k₀ B, ι := β })) ∧
    ∃ (D : I ⥤ CommAlgCat.{u} k₀) (q : C ⟶ D)
      (γ : D ⟶ (Functor.const I).obj (CommAlgCat.of k₀ (ResidueField B))),
      (∀ a : I, ∃ e :
          (C.obj a ⧸ Ideal.span (Set.range fun i : Fin d ↦
            (τ.app a).hom (MvPolynomial.X i))) ≃ₐ[k₀] D.obj a,
        ∀ x : C.obj a,
          e (Ideal.Quotient.mk (Ideal.span (Set.range fun i : Fin d ↦
            (τ.app a).hom (MvPolynomial.X i))) x) = (q.app a).hom x) ∧
      (∀ a : I, Nontrivial (D.obj a) ∧ IsRegularRing (D.obj a) ∧
        Smooth (Spec.map (CommRingCat.ofHom (algebraMap k₀ (D.obj a)))) ∧
        IsRegularClosedImmersionWithCodimension
          (Spec.map (CommRingCat.ofHom (q.app a).hom.toRingHom)) (fun _ ↦ d)) ∧
      Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} k₀) CommRingCat.{u}).mapCocone
        { pt := CommAlgCat.of k₀ (ResidueField B), ι := γ })) ∧
      (∀ a : I, (γ.app a).hom.toRingHom.comp (q.app a).hom.toRingHom =
        (residue B).comp (β.app a).hom.toRingHom) := by
  classical
  let d := (maximalIdeal B).spanFinrank
  have hdim : ringKrullDim B = (d : WithBot ℕ∞) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  obtain ⟨s, hs, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal B).fg_of_isNoetherianRing
  let e : s ≃ Fin d := s.equivFinOfCardEq hs
  let t : Fin d → B := fun i ↦ (e.symm i : B)
  have hrange : Set.range t = (s : Set B) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [t]⟩
  have hgen : Ideal.span (Set.range t) = maximalIdeal B := by
    rw [hrange]
    exact hspan
  have hparams : IsRegularSystemOfParameters (List.ofFn t) := by
    constructor
    · simpa [Set.range] using hgen
    · simpa using hdim.symm
  have hregular := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    B d hdim (List.ofFn t) hparams).1
  let P := MvPolynomial (Fin d) k₀
  let φ : P →ₐ[k₀] B := MvPolynomial.aeval t
  let : Algebra P B := φ.toRingHom.toAlgebra
  have hφ : (algebraMap P B).IsRegular :=
    prime_field_parameter_map_isRegular k₀ B hprime d hdim t hgen
  obtain ⟨J, hJ, hfilt, E, hE, η, ⟨hc⟩⟩ := RingHom.popescu_smoothing hφ
  let : SmallCategory J := hJ
  let : IsFiltered J := hfilt
  obtain ⟨I, hI, hdir, hne, F, hfinal⟩ := IsFiltered.exists_directed J
  let : PartialOrder I := hI
  let : IsDirected I (· ≤ ·) := hdir
  let : Nonempty I := hne
  let : F.Final := hfinal
  let C := F ⋙ E ⋙ restrictParameterBase k₀ d
  let τ : (Functor.const I).obj (CommAlgCat.of k₀ P) ⟶ C :=
    { app a := by
        letI : Algebra k₀ (E.obj (F.obj a)) :=
          Algebra.compHom _ (algebraMap k₀ P)
        exact CommAlgCat.ofHom
          { toRingHom := algebraMap P (E.obj (F.obj a))
            commutes' _ := rfl }
      naturality a b f := by
        ext x
        exact ((E.map (F.map f)).hom.commutes x).symm }
  let β : C ⟶ (Functor.const I).obj (CommAlgCat.of k₀ B) :=
    { app a := by
        letI : Algebra k₀ (E.obj (F.obj a)) :=
          Algebra.compHom _ (algebraMap k₀ P)
        exact CommAlgCat.ofHom
          { toRingHom := (η.app (F.obj a)).hom.toRingHom
            commutes' r := by
              change (η.app (F.obj a)).hom
                (algebraMap P (E.obj (F.obj a)) (algebraMap k₀ P r)) = algebraMap k₀ B r
              rw [(η.app (F.obj a)).hom.commutes]
              exact φ.commutes r }
      naturality a b f := by
        ext x
        exact congrArg (fun g ↦ g.hom x) (η.naturality (F.map f)) }
  have hcompat (a : I) : (β.app a).hom.comp (τ.app a).hom = MvPolynomial.aeval t := by
    ext x
    exact (η.app (F.obj a)).hom.commutes x
  have hsmooth (a : I) :
      Smooth (Spec.map (CommRingCat.ofHom (τ.app a).hom.toRingHom)) := hE (F.obj a)
  have hcolim : Nonempty (IsColimit
      ((forget₂ (CommAlgCat.{u} k₀) CommRingCat.{u}).mapCocone
        { pt := CommAlgCat.of k₀ B, ι := β })) :=
    ⟨(Functor.Final.isColimitWhiskerEquiv F _).symm hc⟩
  obtain ⟨hstage, D, q, γ, hquot, hD, hDcolim, hsq⟩ :=
    smooth_parameter_quotient_diagram k₀ B d t hgen I C τ β hcompat hsmooth hcolim
  refine ⟨d, hdim, t, hgen, hregular, I, hI, hdir, hne, C, τ, β,
    hcompat, hsmooth, hstage, ?_, hcolim, D, q, γ, hquot, hD, hDcolim, hsq⟩
  intro ℓ _ hunit a
  have hnezero : (ℓ : k₀) ≠ 0 := by
    intro hzero
    have : (ℓ : B) = 0 := by
      have hz := congrArg (algebraMap k₀ B) hzero
      simpa using hz
    exact hunit.ne_zero this
  simpa using (isUnit_iff_ne_zero.mpr hnezero).map (algebraMap k₀ (C.obj a))

end IsLocalRing
