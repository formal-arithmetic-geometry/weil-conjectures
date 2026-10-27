module

public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.MvPolynomial.Basic
import Sheaf.AlgebraicGeometry.MonoidPrimeMinimalNeighborhood
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Smallest affine monoscheme neighborhoods and smooth realization charts

Source: ILO, Travaux de Gabber, VIII Remarks 3.1.4(iii), 3.1.10(ii),
3.1.16(i) and Lemma 3.2.12(i), pp.98--100,104
(blueprint: lem-trf-monoscheme-smooth-local-charts).

The five statements are the clauses of this node. Monoids use multiplicative notation:
`1` encodes the additive zero, and products encode sums. The Laurent polynomial algebra
in finitely many variables is the additive monoid algebra on `Fin t → ℤ`, with polynomial
coefficients. Section monoids in the charts are identified with stalks by the canonical germ.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Monoscheme

/-- A smallest open neighborhood is terminal in the opposite neighborhood category,
so its map into the stalk colimit is an isomorphism. -/
private theorem germ_bijective_of_smallest {X : TopCat.{u}}
    (F : TopCat.Presheaf CommMonCat.{u} X) (U : Opens X) (x : X) (hx : x ∈ U)
    (hU : ∀ V : Opens X, x ∈ V → U ≤ V) :
    Function.Bijective (FineFan.germ F U x hx) := by
  let : Limits.HasColimit (FineFan.stalkDiagram F x) := by
    unfold FineFan.stalkDiagram
    infer_instance
  have ht : CategoryTheory.Limits.IsTerminal (op (⟨U, hx⟩ : OpenNhds x)) :=
    CategoryTheory.Limits.IsTerminal.ofUniqueHom
      (fun V ↦ (homOfLE (hU V.unop.1 V.unop.2)).op)
      (fun _ _ ↦ Subsingleton.elim _ _)
  have : IsIso (FineFan.germ F U x hx) :=
    CategoryTheory.Limits.isIso_ι_of_isTerminal ht (FineFan.stalkDiagram F x)
  exact ConcreteCategory.bijective_of_isIso _

/-- Taking a germ after pulling back and restricting a section agrees with the
canonical stalk map. -/
private theorem sectionMap_germ {N M : Fine.{u}} (f : Hom N M)
    (U : AffineOpens N) (V : AffineOpens M)
    (h : U.1 ≤ (Opens.map f.map.hom.base).obj V.1) (y : N.space)
    (hy : y ∈ U.1) (hx : f.map.hom.base y ∈ V.1)
    (s : M.space.presheaf.obj (op V.1)) :
    FineFan.germ N.space.presheaf U.1 y hy (f.sectionMap U V h s) =
      FineFan.stalkMap f.map y
        (FineFan.germ M.space.presheaf V.1 (f.map.hom.base y) hx s) := by
  have hr : N.space.presheaf.map (homOfLE h).op ≫
      FineFan.germ N.space.presheaf U.1 y hy =
        FineFan.germ N.space.presheaf ((Opens.map f.map.hom.base).obj V.1) y hx :=
    Limits.colimit.w (FineFan.stalkDiagram N.space.presheaf y)
      (homOfLE h : (⟨U.1, hy⟩ : OpenNhds y) ⟶ ⟨_, hx⟩).op
  have hg : FineFan.germ M.space.presheaf V.1 (f.map.hom.base y) hx ≫
      FineFan.stalkMap f.map y = f.map.hom.c.app (op V.1) ≫
        FineFan.germ N.space.presheaf ((Opens.map f.map.hom.base).obj V.1) y hx := by
    simp only [FineFan.germ, FineFan.stalkMap, Limits.colim_obj, Limits.colim_map,
      OpenNhds.inclusionMapIso_inv, NatTrans.op_id, Limits.ι_colimMap_assoc,
      Functor.comp_obj, Functor.op_obj, OpenNhds.inclusion_obj,
      TopCat.Presheaf.pushforward_obj_obj, Functor.whiskerLeft_app, OpenNhds.map_obj,
      Functor.whiskerRight_app, NatTrans.id_app]
    rw [N.space.presheaf.map_id, Category.id_comp]
    exact congrArg (fun g ↦ f.map.hom.c.app (op V.1) ≫ g)
      (Limits.colimit.ι_pre (FineFan.stalkDiagram N.space.presheaf y)
        (OpenNhds.map f.map.hom.base y).op (op ⟨V.1, hx⟩))
  have hh : f.sectionMap U V h ≫ FineFan.germ N.space.presheaf U.1 y hy =
      FineFan.germ M.space.presheaf V.1 (f.map.hom.base y) hx ≫
        FineFan.stalkMap f.map y := by
    change (f.map.hom.c.app (op V.1) ≫ N.space.presheaf.map (homOfLE h).op) ≫ _ = _
    rw [Category.assoc, hr, hg]
  exact ConcreteCategory.congr_hom hh s

/-- A proper monoid ideal contains no unit. -/
private theorem unit_not_mem_prime {P : Type u} [CommMonoid P]
    (p : FineFan.MonoidPrime P) {a : P} (ha : IsUnit a) : a ∉ p.carrier := by
  rcases ha with ⟨a, rfl⟩
  intro h
  have h1 : (1 : P) ∈ p.carrier := by
    simpa using p.toSubMulAction.smul_mem (↑a⁻¹) h
  apply p.proper
  apply Set.eq_univ_of_forall
  intro b
  simpa using p.toSubMulAction.smul_mem b h1

/-- The nonunits form the closed point of a monoid spectrum, and every point
specializes to it. This uses neither finite generation nor integrality. -/
private theorem monoid_spectrum_closed_point (P : Type u) [CommMonoid P] :
    ∃ m : FineFan.MonoidPrime P, ∀ q : FineFan.MonoidPrime P, Specializes q m := by
  classical
  let m : FineFan.MonoidPrime P :=
    { carrier := {a | ¬ IsUnit a}
      smul_mem' := fun a b hb hab ↦ hb (isUnit_of_mul_isUnit_right hab)
      proper := fun h ↦ ((Set.ext_iff.mp h (1 : P)).mpr (Set.mem_univ 1)) isUnit_one
      complement_mul := fun a b ha hb ↦ not_not.mpr
        ((not_not.mp ha).mul (not_not.mp hb)) }
  refine ⟨m, fun q ↦ specializes_iff_forall_open.mpr ?_⟩
  intro O hO
  change TopologicalSpace.GenerateOpen _ O at hO
  induction hO with
  | basic O hO =>
      obtain ⟨a, rfl⟩ := hO
      exact fun ha ↦ unit_not_mem_prime q (not_not.mp ha)
  | univ => exact fun _ ↦ Set.mem_univ _
  | inter O T _ _ ihO ihT => exact fun h ↦ ⟨ihO h.1, ihT h.2⟩
  | sUnion S _ ih =>
      rintro ⟨O, hOS, hm⟩
      exact ⟨O, hOS, ih O hOS hm⟩

/-- Every affine monoid open has a point whose smallest neighborhood is that open. -/
private theorem affineOpen_eq_smallest (N : Fine.{u})
    (U : ∀ _y : N.space, AffineOpens N) (hy : ∀ y : N.space, y ∈ (U y).1)
    (hU : ∀ (y : N.space) (W : Opens N.space), y ∈ W → (U y).1 ≤ W)
    (V : AffineOpens N) : ∃ y : N.space, U y = V := by
  obtain ⟨P, _, ⟨e⟩⟩ := V.2
  obtain ⟨m, hm⟩ := monoid_spectrum_closed_point P
  let E := TopCat.homeoOfIso
    ((SheafedSpace.forgetToPresheafedSpace ⋙ PresheafedSpace.forget CommMonCat).mapIso e)
  let y : N.space := (E.symm m).1
  refine ⟨y, Subtype.ext (le_antisymm (hU y V.1 (E.symm m).2) ?_)⟩
  intro z hz
  have hspec := (hm (E ⟨z, hz⟩)).map E.symm.continuous
  have hloc : Specializes (⟨z, hz⟩ : V.1) (E.symm m) := by
    simpa using hspec
  exact (hloc.map continuous_subtype_val).mem_open (U y).1.isOpen (hy y)

/-- The smallest neighborhood is affine, consists of generalizations, and its canonical
section-to-stalk homomorphism is an isomorphism.
Source: ILO VIII 3.1.4(iii), 3.1.10(ii), pp.98--100
(blueprint: lem-trf-monoscheme-smooth-local-charts).
Proof: choose an affine chart and a finite generating set. The product of generators
outside the prime defines the intersection of all principal neighborhoods, by
[lem-trf-monoid-prime-minimal-neighborhood]. Its points are precisely primes contained
in the given prime, hence generalizations. Intersecting any ambient neighborhood with
the chosen chart proves minimality in the whole space. The ordinary monoid sheaf has
localized sections on this principal open. The affine identification is also the ordinary
smallest-stalk-chart clause of [lem-trf-fine-monoid-local-smooth-charts]. Every germ
restricts to the smallest neighborhood, and equality of germs becomes equality there,
so the canonical germ homomorphism is bijective. -/
theorem exists_smallest_affine_neighborhood (M : Fine.{u}) (x : M.space) :
    ∃ U : AffineOpens M, ∃ hx : x ∈ U.1,
      (∀ V : Opens M.space, x ∈ V → U.1 ≤ V) ∧
      (∀ z : M.space, z ∈ U.1 ↔ Specializes z x) ∧
      Function.Bijective (FineFan.germ M.space.presheaf U.1 x hx) := by
  sorry

/-- On a smallest neighborhood every covering sieve contains the identity. -/
private theorem covering_id_of_smallest {X : Type u} [TopologicalSpace X]
    (U : Opens X) (x : X) (hx : x ∈ U)
    (hU : ∀ V : Opens X, x ∈ V → U ≤ V)
    (S : Sieve U) (hS : S ∈ Opens.grothendieckTopology X U) : S (𝟙 U) := by
  obtain ⟨V, i, hi, hxV⟩ := hS x hx
  have he : V = U := le_antisymm i.le (hU V hxV)
  subst V
  simpa only [Subsingleton.elim i (𝟙 U)] using hi

/-- Sheafification preserves sections on a smallest neighborhood. -/
private theorem sheafification_bijective_of_smallest {X : Type u} [TopologicalSpace X]
    (F : (Opens X)ᵒᵖ ⥤ CommMonCat.{u}) (U : Opens X) (x : X) (hx : x ∈ U)
    (hU : ∀ V : Opens X, x ∈ V → U ≤ V) :
    Function.Bijective ((toSheafify (Opens.grothendieckTopology X) F).app (op U)) := by
  let J := Opens.grothendieckTopology X
  let η := toSheafify J F
  constructor
  · intro a b hab
    have hS := CategoryTheory.Presheaf.equalizerSieve_mem J η a b hab
    have hi := covering_id_of_smallest U x hx hU _ hS
    change F.map (𝟙 U).op a = F.map (𝟙 U).op b at hi
    rw [op_id, F.map_id] at hi
    exact hi
  · intro b
    have hS := CategoryTheory.Presheaf.imageSieve_mem J η b
    have hi := covering_id_of_smallest U x hx hU _ hS
    change ∃ a, η.app (op U) a = (sheafify J F).map (𝟙 U).op b at hi
    rw [op_id, (sheafify J F).map_id] at hi
    exact hi

/-- Evaluation identifies compatible fraction families on a smallest open with its
closed-point localization. -/
private noncomputable def sectionsEquivOfSmallest {P : Type u} [CommMonoid P]
    (U : Opens (FineFan.MonoidPrime P)) (p : FineFan.MonoidPrime P) (hp : p ∈ U)
    (hU : ∀ V : Opens (FineFan.MonoidPrime P), p ∈ V → U ≤ V) :
    FineFan.spectrumSections U ≃*
      Algebra.faceLocalization P (Submonoid.closure {q : P | q ∉ p.carrier}) where
  toFun s := ⟨s.val ⟨p, hp⟩, s.property.1 ⟨p, hp⟩⟩
  invFun s := ⟨fun _ ↦ s.val, ⟨fun q ↦ by
    obtain ⟨a, b, hab⟩ := s.property
    refine ⟨a, ⟨b.val, ?_⟩, hab⟩
    apply Submonoid.closure_mono ?_ b.property
    intro c hc
    exact hU (FineFan.basicOpen c) hc q.property,
    fun _ _ ↦ rfl⟩⟩
  left_inv s := by
    apply Subtype.ext
    funext q
    exact s.property.2 _ _
  right_inv s := rfl
  map_mul' _ _ := rfl

/-- The finite-generator formula in any affine chart, including the empty product.
The last isomorphism fixes numerator sections, so it is the canonical localization map.
Source: ILO VIII 3.1.2--3.1.4(iii), pp.98--99
(blueprint: lem-trf-monoscheme-smooth-local-charts).
Proof: use [lem-trf-monoid-prime-minimal-neighborhood] for the selected product a.
A prime lies in D(a) exactly when it avoids every generator outside p, equivalently
when it is contained in p. Thus D(a) is the smallest neighborhood. Inverting a inverts
each selected generator, and every element outside p is generated by them, so the
localization inside the group completion is P-(P\p). The ordinary spectrum sheaf
identifies sections on D(a) with this localization and sends every numerator to itself.
Transporting this formula through any affine-chart isomorphism gives the stated
formula for the smallest neighborhood inside that chart. -/
theorem affine_smallest_neighborhood_formula (P : Type u) [CommMonoid P]
    (_hP : FineFan.IsFine P) (n : ℕ) (e : Fin n → P)
    (_he : Submonoid.closure (Set.range e) = ⊤) (p : FineFan.MonoidPrime P)
    (a : P)
    (_ha : a = ∏ i : Fin n, @ite P (e i ∈ p.carrier) (Classical.propDecidable _) 1 (e i)) :
    p ∈ FineFan.basicOpen a ∧
      (∀ V : Opens (FineFan.MonoidPrime P), p ∈ V → FineFan.basicOpen a ≤ V) ∧
      Algebra.faceLocalization P (Submonoid.powers a) =
        Algebra.faceLocalization P (Submonoid.closure {q : P | q ∉ p.carrier}) ∧
      ∃ E : ((affine P).presheaf.obj (op (FineFan.basicOpen a))) ≃*
          Algebra.faceLocalization P (Submonoid.closure {q : P | q ∉ p.carrier}),
        ∀ q : P,
          (E ((affine P).presheaf.map (homOfLE le_top).op (affineSection P q)) :
            Algebra.GrothendieckGroup P) = Algebra.GrothendieckGroup.of q := by
  classical
  have ha : a = (Finset.univ.filter (fun i : Fin n ↦ e i ∉ p.carrier)).prod e := by
    rw [_ha, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : e i ∈ p.carrier <;> simp [hi]
  have H := FineFan.monoidPrime_minimal_neighborhood P _hP n e _he p a ha
  have hp := H.2.2.2.2.2.2.1
  have hU := H.2.2.2.2.2.2.2.1
  have hloc := H.2.2.2.2.2.2.2.2.1
  refine ⟨hp, hU, hloc, ?_⟩
  let η := toSheafify (Opens.grothendieckTopology (FineFan.MonoidPrime P))
    (FineFan.spectrumPresheaf P)
  let Eη := MulEquiv.ofBijective (η.app (op (FineFan.basicOpen a))).hom
    (sheafification_bijective_of_smallest (FineFan.spectrumPresheaf P) _ p hp hU)
  let E₀ := sectionsEquivOfSmallest (FineFan.basicOpen a) p hp hU
  refine ⟨Eη.symm.trans E₀, ?_⟩
  intro q
  have hn := ConcreteCategory.congr_hom (η.naturality (homOfLE
    (show FineFan.basicOpen a ≤ ⊤ from le_top)).op) (FineFan.numerator P q)
  change ((E₀ (Eη.symm ((affine P).presheaf.map (homOfLE le_top).op
    (affineSection P q)))) : Algebra.GrothendieckGroup P) = _
  have hn' : (affine P).presheaf.map (homOfLE le_top).op (affineSection P q) =
      Eη ((FineFan.spectrumPresheaf P).map (homOfLE le_top).op
        (FineFan.numerator P q)) := hn.symm
  rw [hn', Eη.symm_apply_apply]
  rfl

/-- Every morphism restricts to smallest neighborhoods, with the canonical stalk map
as its section map. A smooth restriction has the required finite product chart.
Source: ILO VIII 3.1.6, 3.1.10(ii), 3.1.13--3.1.16(i), pp.99--100
(blueprint: lem-trf-monoscheme-smooth-local-charts).
Proof: the inverse image of the smallest target neighborhood contains y, so the smallest
source neighborhood lies in it. Restrict the sheaf morphism to obtain the displayed
morphism; its square with the open inclusions commutes. Taking germs of a pulled-back
section is the stalk homomorphism applied to its germ, by the definition of stalkMap.
On each smallest neighborhood the germ is an isomorphism: that neighborhood is a
terminal object of the opposite neighborhood category defining the stalk. The definition
of f.IsSmooth supplies the product splitting of the stalk map directly. Compose it
with the target germ equivalence and the inverse source germ equivalence. Germ
naturality identifies this product inclusion with the displayed section map. This
argument uses neither torsion-freeness nor a separate affine product-chart theorem. -/
theorem restrict_smallest_neighborhoods {N M : Fine.{u}} (f : Hom N M) (y : N.space)
    (U : AffineOpens N) (V : AffineOpens M) (hy : y ∈ U.1)
    (hx : f.map.hom.base y ∈ V.1)
    (_hU : ∀ W : Opens N.space, y ∈ W → U.1 ≤ W)
    (_hV : ∀ W : Opens M.space, f.map.hom.base y ∈ W → V.1 ≤ W) :
    ∃ h : U.1 ≤ (Opens.map f.map.hom.base).obj V.1,
      (∃ g : N.space.restrict U.1.isOpenEmbedding ⟶ M.space.restrict V.1.isOpenEmbedding,
        g ≫ M.space.ofRestrict V.1.isOpenEmbedding =
          N.space.ofRestrict U.1.isOpenEmbedding ≫ f.map) ∧
      (∀ s : M.space.presheaf.obj (op V.1),
        FineFan.germ N.space.presheaf U.1 y hy (f.sectionMap U V h s) =
          FineFan.stalkMap f.map y (FineFan.germ M.space.presheaf V.1
            (f.map.hom.base y) hx s)) ∧
      (f.IsSmooth → ∃ r t : ℕ,
        ∃ e : (M.space.presheaf.obj (op V.1) ×
            Multiplicative (Fin r → ℕ) × Multiplicative (Fin t → ℤ)) ≃*
              N.space.presheaf.obj (op U.1),
          ∀ p : M.space.presheaf.obj (op V.1), e (p, 1, 1) = f.sectionMap U V h p) := by
  classical
  have h : U.1 ≤ (Opens.map f.map.hom.base).obj V.1 := _hU _ hx
  refine ⟨h, ?_, sectionMap_germ f U V h y hy hx, ?_⟩
  · let i := M.space.ofRestrict V.1.isOpenEmbedding
    let j := N.space.ofRestrict U.1.isOpenEmbedding ≫ f.map
    have hr : Set.range j.hom.base ⊆ Set.range i.hom.base := by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨f.map.hom.base z.1, h z.2⟩, rfl⟩
    refine ⟨InducedCategory.homMk
      (PresheafedSpace.IsOpenImmersion.lift i.hom j.hom hr), ?_⟩
    exact InducedCategory.hom_ext
      (PresheafedSpace.IsOpenImmersion.lift_fac i.hom j.hom hr)
  · intro hf
    obtain ⟨r, t, e, he⟩ := hf y
    let eV := MulEquiv.ofBijective (FineFan.germ M.space.presheaf V.1
      (f.map.hom.base y) hx).hom
      (germ_bijective_of_smallest M.space.presheaf V.1 _ hx _hV)
    let eU := MulEquiv.ofBijective (FineFan.germ N.space.presheaf U.1 y hy).hom
      (germ_bijective_of_smallest N.space.presheaf U.1 y hy _hU)
    refine ⟨r, t, ((eV.prodCongr (MulEquiv.refl _)).trans e).trans eU.symm, ?_⟩
    intro p
    apply eU.injective
    change eU (eU.symm (e (eV p, 1, 1))) = eU (f.sectionMap U V h p)
    rw [eU.apply_symm_apply]
    exact (he (eV p)).trans (sectionMap_germ f U V h y hy hx p).symm

/-- Convert a multiplicative basis vector back to additive notation. -/
private theorem toMultiplicative_symm_single (R A G : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] [AddMonoid G] (g : G) (a : A) :
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv R A G).symm
      (MonoidAlgebra.single (Multiplicative.ofAdd g) a) =
        AddMonoidAlgebra.single g a := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv R A G).injective
  simp

/-- A Laurent variable is a principal localization of a polynomial variable. -/
private theorem smooth_laurent_one (A : Type*) [CommRing A] :
    Algebra.Smooth A (AddMonoidAlgebra A ℤ) := by
  have : Algebra.Smooth A (Polynomial A) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth (Polynomial A) (AddMonoidAlgebra A ℤ) :=
    Algebra.Smooth.of_isLocalization_Away Polynomial.X
  have : IsScalarTower A (Polynomial A) (AddMonoidAlgebra A ℤ) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro a
      exact (Polynomial.toLaurent_C a).symm)
  exact Algebra.Smooth.comp A (Polynomial A) (AddMonoidAlgebra A ℤ)

/-- A finite Laurent algebra is smooth, by adjoining one invertible variable at a time. -/
private theorem smooth_laurent (A : Type*) [CommRing A] (t : ℕ) :
    Algebra.Smooth A (AddMonoidAlgebra A (Fin t → ℤ)) := by
  induction t with
  | zero =>
      have : Algebra.Smooth A A := ⟨inferInstance, inferInstance⟩
      exact Algebra.Smooth.of_equiv (AddMonoidAlgebra.uniqueAlgEquiv A (Fin 0 → ℤ)).symm
  | succ t ih =>
      let B := AddMonoidAlgebra A (Fin t → ℤ)
      have : Algebra.Smooth A B := ih
      have : Algebra.Smooth B (AddMonoidAlgebra B ℤ) := smooth_laurent_one B
      have : Algebra.Smooth A (AddMonoidAlgebra B ℤ) :=
        Algebra.Smooth.comp A B (AddMonoidAlgebra B ℤ)
      let d : (Fin (t + 1) → ℤ) ≃+ (ℤ × (Fin t → ℤ)) :=
        { toEquiv := (Fin.consEquiv (fun _ : Fin (t + 1) ↦ ℤ)).symm
          map_add' := fun _ _ ↦ rfl }
      let E : AddMonoidAlgebra A (Fin (t + 1) → ℤ) ≃ₐ[A]
          AddMonoidAlgebra B ℤ :=
        (AddMonoidAlgebra.domCongr A A d).trans (AddMonoidAlgebra.curryAlgEquiv A)
      exact Algebra.Smooth.of_equiv E.symm

/-- On a smooth product chart, realization is the polynomial/Laurent coefficient
inclusion and its associated affine scheme morphism is smooth.
Source: ILO VIII 3.1.16(i), Lemma 3.2.12(i), pp.100,104
(blueprint: lem-trf-monoscheme-smooth-local-charts).
Proof: the monoid-algebra basis identifies e^(p,α,β) with e^p x^α y^β. Addition of
exponents proves multiplicativity, and the inverse bijection on bases gives an algebra
isomorphism. The chart map sends e^p to that same constant coefficient, giving the
second displayed formula. The Laurent algebra is the localization of the polynomial
algebra in r+t variables at the product of its last t variables (at 1 if t=0).
By [lem-weil-pbc-principal-localization-open-immersion] its Spec is an open subscheme
of affine (r+t)-space. Apply [sbc-lem-affine-space-smooth] and
[lem-pc-open-immersion-smooth-composition] to obtain smoothness of the composite.
This is the realized chart map by [def-trf-monoscheme-toric-realization]. The basis
calculation and the localization argument allow torsion in P and both ranks zero. -/
theorem realized_smallest_product_chart (k : Type u) [Field k] {N M : Fine.{u}}
    (f : Hom N M) (U : AffineOpens N) (V : AffineOpens M)
    (h : U.1 ≤ (Opens.map f.map.hom.base).obj V.1) (r t : ℕ)
    (e : (M.space.presheaf.obj (op V.1) ×
        Multiplicative (Fin r → ℕ) × Multiplicative (Fin t → ℤ)) ≃*
          N.space.presheaf.obj (op U.1))
    (_he : ∀ p : M.space.presheaf.obj (op V.1), e (p, 1, 1) = f.sectionMap U V h p) :
    (∃ E : MonoidAlgebra k (N.space.presheaf.obj (op U.1)) ≃ₐ[k]
        AddMonoidAlgebra (MvPolynomial (Fin r)
          (MonoidAlgebra k (M.space.presheaf.obj (op V.1)))) (Fin t → ℤ),
      (∀ (p : M.space.presheaf.obj (op V.1)) (α : Fin r → ℕ) (β : Fin t → ℤ) (a : k),
        E (MonoidAlgebra.single (e (p, Multiplicative.ofAdd α, Multiplicative.ofAdd β)) a) =
          AddMonoidAlgebra.single β
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α)
              (MonoidAlgebra.single p a))) ∧
      (∀ a : MonoidAlgebra k (M.space.presheaf.obj (op V.1)),
        E (MonoidAlgebra.mapDomainRingHom k (f.sectionMap U V h).hom a) =
          AddMonoidAlgebra.single 0 (MvPolynomial.C a))) ∧
      Smooth (Spec.map ((monoidAlgebra k).map (f.sectionMap U V h))) := by
  classical
  let P := M.space.presheaf.obj (op V.1)
  let B := Multiplicative (Fin r → ℕ)
  let C := Multiplicative (Fin t → ℤ)
  let d : (P × B × C) ≃* (C × (B × P)) :=
    { toFun := fun z ↦ (z.2.2, z.2.1, z.1)
      invFun := fun z ↦ (z.2.2, z.2.1, z.1)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  let eb : B ≃* Multiplicative (Fin r →₀ ℕ) :=
    Finsupp.addEquivFunOnFinite.symm.toMultiplicative
  let ep : MonoidAlgebra k (B × P) ≃ₐ[k] MvPolynomial (Fin r) (MonoidAlgebra k P) :=
    (MonoidAlgebra.curryAlgEquiv k).trans
      ((MonoidAlgebra.domCongr k (MonoidAlgebra k P) eb).trans
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv k _ _).symm)
  let E : MonoidAlgebra k (N.space.presheaf.obj (op U.1)) ≃ₐ[k]
      AddMonoidAlgebra (MvPolynomial (Fin r) (MonoidAlgebra k P)) (Fin t → ℤ) :=
    (MonoidAlgebra.domCongr k k (e.symm.trans d)).trans
      ((MonoidAlgebra.curryAlgEquiv k).trans
        ((MonoidAlgebra.mapAlgEquiv k C ep).trans
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv k _ _).symm))
  have hE (p : P) (α : Fin r → ℕ) (β : Fin t → ℤ) (a : k) :
      E (MonoidAlgebra.single (e (p, Multiplicative.ofAdd α, Multiplicative.ofAdd β)) a) =
        AddMonoidAlgebra.single β
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α)
            (MonoidAlgebra.single p a)) := by
    have heb : eb (Multiplicative.ofAdd α) =
        Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm α) := rfl
    have hep : ep (MonoidAlgebra.single (Multiplicative.ofAdd α, p) a) =
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α)
          (MonoidAlgebra.single p a) := by
      simp only [ep, AlgEquiv.trans_apply, MonoidAlgebra.curryAlgEquiv_single,
        MonoidAlgebra.domCongr_single, heb, toMultiplicative_symm_single]
      rfl
    have hmap (m : C) (v : MonoidAlgebra k (B × P)) :
        MonoidAlgebra.mapAlgEquiv k C ep (MonoidAlgebra.single m v) =
          MonoidAlgebra.single m (ep v) :=
      MonoidAlgebra.mapAlgHom_single ep.toAlgHom m v
    simp only [E, AlgEquiv.trans_apply, MonoidAlgebra.domCongr_single,
      MulEquiv.trans_apply, e.symm_apply_apply]
    change (AddMonoidAlgebra.toMultiplicativeAlgEquiv k
      (MvPolynomial (Fin r) (MonoidAlgebra k P)) (Fin t → ℤ)).symm
        (MonoidAlgebra.mapAlgEquiv k C ep ((MonoidAlgebra.curryAlgEquiv k)
          (MonoidAlgebra.single
            (Multiplicative.ofAdd β, Multiplicative.ofAdd α, p) a))) = _
    rw [MonoidAlgebra.curryAlgEquiv_single, hmap, toMultiplicative_symm_single, hep]
  have hcoeff (a : MonoidAlgebra k P) :
      E (MonoidAlgebra.mapDomainRingHom k (f.sectionMap U V h).hom a) =
        AddMonoidAlgebra.single 0 (MvPolynomial.C a) := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | single p a =>
        simp only [MonoidAlgebra.mapDomainRingHom_apply,
          MonoidAlgebra.mapDomain_single]
        rw [← _he p]
        have hzero : Finsupp.equivFunOnFinite.symm (0 : Fin r → ℕ) = 0 := by
          ext i
          rfl
        simpa only [hzero, MvPolynomial.C_apply, ofAdd_zero] using
          hE p 0 0 a
    | add a b ha hb => simp only [map_add, ha, hb, AddMonoidAlgebra.single_add]
  refine ⟨⟨E, hE, hcoeff⟩, ?_⟩
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  have hpoly : Algebra.Smooth (MonoidAlgebra k P)
      (MvPolynomial (Fin r) (MonoidAlgebra k P)) := ⟨inferInstance, inferInstance⟩
  have hLaurent := smooth_laurent (MvPolynomial (Fin r) (MonoidAlgebra k P)) t
  have hinc : (algebraMap (MonoidAlgebra k P)
      (AddMonoidAlgebra (MvPolynomial (Fin r) (MonoidAlgebra k P))
        (Fin t → ℤ))).Smooth := by
    apply RingHom.smooth_algebraMap.mpr
    exact Algebra.Smooth.comp (MonoidAlgebra k P)
      (MvPolynomial (Fin r) (MonoidAlgebra k P)) _
  have heq : MonoidAlgebra.mapDomainRingHom k (f.sectionMap U V h).hom =
      E.symm.toRingHom.comp (algebraMap (MonoidAlgebra k P)
        (AddMonoidAlgebra (MvPolynomial (Fin r) (MonoidAlgebra k P))
          (Fin t → ℤ))) := by
    apply RingHom.ext
    intro a
    apply E.injective
    change E ((MonoidAlgebra.mapDomainRingHom k (f.sectionMap U V h).hom) a) =
      E (E.symm (algebraMap (MonoidAlgebra k P) _ a))
    rw [E.apply_symm_apply, hcoeff]
    rfl
  change (MonoidAlgebra.mapDomainRingHom k (f.sectionMap U V h).hom).Smooth
  rw [heq]
  exact hinc.comp (RingHom.Smooth.of_bijective E.symm.bijective)

/-- The realizations of all smallest neighborhoods cover the whole realization,
including the empty monoscheme.
Source: ILO VIII 3.1.4(i), 3.1.10(ii), 3.2.2, pp.98--100,103
(blueprint: lem-trf-monoscheme-smooth-local-charts).
Proof: the neighborhoods contain their indexing points and cover N. More explicitly,
in any original affine chart Spec Q the prime Q\Qˣ contains every prime of Q.
Its generalizations fill that entire chart. By minimality, the smallest neighborhood
of this point is exactly the chart, also in N. Thus every original affine chart occurs
in the family. Their realized charts cover the gluing defining k[N]. If N is empty,
the realization is the empty gluing and the asserted covering is vacuous. -/
theorem smallest_neighborhood_realizations_cover (k : Type u) [Field k] (N : Fine.{u})
    (U : ∀ _y : N.space, AffineOpens N) (_hy : ∀ y : N.space, y ∈ (U y).1)
    (_hU : ∀ (y : N.space) (W : Opens N.space), y ∈ W → (U y).1 ≤ W) :
    ∀ z : realization k N, ∃ y : N.space,
      ∃ q : (realizationDiagram k N).obj (U y), realizationι k N (U y) q = z := by
  let : ∀ {V W : AffineOpens N} (g : V ⟶ W),
      IsOpenImmersion ((realizationDiagram k N).map g) := realizationDiagram_open k N
  let := realizationDiagram_locallyDirected k N
  intro z
  obtain ⟨V, q, hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (realizationDiagram k N) z
  obtain ⟨y, hyV⟩ := affineOpen_eq_smallest N U _hy _hU V
  subst V
  exact ⟨y, q, hq⟩

end AlgebraicGeometry.Monoscheme
