module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Mathlib.RingTheory.Localization.Basic

/-!
# Integral realization of fine monoschemes

Source: ILO VIII 3.2.1--3.2.2 and 3.3.3--3.3.5
(blueprint: def-per-integral-monoscheme-realization).

The scheme is the open colimit of the actual integer monoid algebras. All chosen
maps and identifications are uniquely characterized by their monomial formulas.
Multiplicative monoids encode the additive notation of the source.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Monoscheme

/-- Integer monoid algebras and their monomial maps. Source: ILO VIII 3.2.2
(blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralMonoidAlgebra : CommMonCat.{u} ⥤ CommRingCat.{u} where
  obj P := .of (MonoidAlgebra ℤ P)
  map f := CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ f.hom)
  map_id P := by
    apply CommRingCat.hom_ext
    exact MonoidAlgebra.mapDomainRingHom_id
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact MonoidAlgebra.mapDomainRingHom_comp g.hom f.hom

/-- The integer monomial localization diagram on the recorded affine opens.
Source: ILO VIII 3.2.2 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralDiagram (M : Fine.{u}) : AffineOpens M ⥤ Scheme.{u} :=
  (affineSections M ⋙ integralMonoidAlgebra).rightOp ⋙ Scheme.Spec

/-- The open-gluing obligations for the integer diagram. Source: ILO VIII 3.2.2
(blueprint: def-per-integral-monoscheme-realization).
Proof: an affine subopen is a monoid localization. Its integer monoid algebra is
localization at the same monomials, hence its Spec is open. Common principal
refinements cover intersections, giving the locally directed condition. The empty
diagram also satisfies it. No coefficient-field hypothesis is used. -/
theorem integralDiagram_gluing (M : Fine.{u}) :
    (∀ {U V : AffineOpens M} (f : U ⟶ V),
      IsOpenImmersion ((integralDiagram M).map f)) ∧
    (integralDiagram M ⋙ Scheme.forget).IsLocallyDirected := by
  sorry

/-- The integral realization, constructed by the canonical open colimit.
Source: ILO VIII 3.2.2 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralRealization (M : Fine.{u}) : Scheme.{u} :=
  letI : ∀ {U V : AffineOpens M} (f : U ⟶ V),
      IsOpenImmersion ((integralDiagram M).map f) := (integralDiagram_gluing M).1
  letI := (integralDiagram_gluing M).2
  colimit (integralDiagram M)

/-- The canonical integer chart injection. Source: ILO VIII 3.2.2
(blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralι (M : Fine.{u}) (U : AffineOpens M) :
    (integralDiagram M).obj U ⟶ integralRealization M :=
  letI : ∀ {U V : AffineOpens M} (f : U ⟶ V),
      IsOpenImmersion ((integralDiagram M).map f) := (integralDiagram_gluing M).1
  letI := (integralDiagram_gluing M).2
  colimit.ι (integralDiagram M) U

/-- Monomial characterization of the induced map. Source: ILO VIII 3.2.2
(blueprint: def-per-integral-monoscheme-realization). -/
def IsIntegralMap {N M : Fine.{u}} (f : N.space ⟶ M.space)
    (g : integralRealization N ⟶ integralRealization M) : Prop :=
  ∀ (U : AffineOpens N) (V : AffineOpens M)
    (h : U.1 ≤ (Opens.map f.hom.base).obj V.1),
    integralι N U ≫ g = Spec.map (integralMonoidAlgebra.map
      (f.hom.c.app (op V.1) ≫ N.space.presheaf.map (homOfLE h).op)) ≫ integralι M V

/-- Existence and uniqueness of the monomial map. Source: ILO VIII 3.2.2
(blueprint: def-per-integral-monoscheme-realization).
Proof: refine source affine opens inside inverse images of target affine opens,
use the integer monoid algebra of the section homomorphism, and glue. Naturality
makes the maps agree on common refinements. The chart cover proves uniqueness. -/
theorem existsUnique_integralMap {N M : Fine.{u}} (f : N.space ⟶ M.space) :
    ∃! g, IsIntegralMap f g := by
  sorry

/-- The uniquely determined realization map. Source: ILO VIII 3.2.2
(blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralMap {N M : Fine.{u}} (f : N.space ⟶ M.space) :
    integralRealization N ⟶ integralRealization M :=
  Classical.choose (existsUnique_integralMap f).exists

/-- The section map from the base monoid to a chart. Source: ILO VIII 3.3.3
(blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralBaseSections {P : Type u} [CommMonoid P] {M : Fine.{u}}
    (f : M.space ⟶ affine P) (U : AffineOpens M) :
    P →* M.space.presheaf.obj (op U.1) :=
  (M.space.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom.comp
    ((f.hom.c.app (op ⊤)).hom.comp (affineSection P))

/-- The affine-base map is fixed on every integer monoid-algebra chart.
Source: ILO VIII 3.3.3 (blueprint: def-per-integral-monoscheme-realization).
Proof: the displayed ring maps are compatible with restrictions since f is a
sheaf morphism. They form a cocone into Spec Z[P]. Descent in the defining open
colimit gives the map, and the same colimit property proves uniqueness. -/
theorem existsUnique_integralToAffine {P : Type u} [CommMonoid P] {M : Fine.{u}}
    (f : M.space ⟶ affine P) : ∃! g : integralRealization M ⟶ Spec (.of (MonoidAlgebra ℤ P)),
      ∀ U : AffineOpens M, integralι M U ≫ g =
        Spec.map (CommRingCat.ofHom
          (MonoidAlgebra.mapDomainRingHom ℤ (integralBaseSections f U))) := by
  sorry

/-- The canonical map to Spec Z[P]. Source: ILO VIII 3.3.3
(blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralToAffine {P : Type u} [CommMonoid P] {M : Fine.{u}}
    (f : M.space ⟶ affine P) : integralRealization M ⟶ Spec (.of (MonoidAlgebra ℤ P)) :=
  Classical.choose (existsUnique_integralToAffine f).exists

/-- The affine model is fine with its single top chart. Source: ILO VIII 3.1.9
(blueprint: def-per-integral-monoscheme-realization).
Proof: take the top open, its restrict-top isomorphism and the given fine monoid;
this single open contains every point. -/
theorem integralAffine_finiteCover (P : Type u) [CommMonoid P] (hP : FineFan.IsFine P) :
    ∃ n : ℕ, ∃ c : Fin n → Chart (affine P),
      ∀ x : affine P, ∃ i : Fin n, x ∈ (c i).openSet := by
  sorry

/-- The actual affine monoscheme with its one-chart cover.
Source: ILO VIII 3.1.9 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralAffine (P : Type u) [CommMonoid P] (hP : FineFan.IsFine P) :
    Fine.{u} where
  space := affine P
  finiteCover := integralAffine_finiteCover P hP

/-- The affine realization is canonically its integer monoid spectrum.
Source: ILO VIII 3.2.2 (blueprint: def-per-integral-monoscheme-realization).
Proof: P maps isomorphically to the global sections of its affine monoid spectrum.
The top chart is final in the open diagram. The specified projection is therefore
an isomorphism, with inverse given by its top chart injection. -/
theorem integralAffine_isIso (P : Type u) [CommMonoid P] (hP : FineFan.IsFine P) :
    IsIso (integralToAffine (M := integralAffine P hP) (𝟙 (affine P))) := by
  sorry

/-- The canonical embedding of a chart with specified monoid.
Source: ILO VIII 3.2.2 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralChartι {M : Fine.{u}} {Q : Type u} [CommMonoid Q]
    (hQ : FineFan.IsFine Q) (c : AffineOpen M.space Q) :
    Spec (.of (MonoidAlgebra ℤ Q)) ⟶ integralRealization M :=
  letI := integralAffine_isIso Q hQ
  inv (integralToAffine (M := integralAffine Q hQ) (𝟙 (affine Q))) ≫
    integralMap (N := integralAffine Q hQ) c.inclusion

/-- The actual finite composition of the tower's monoidal-space maps.
Source: ILO VIII 3.1.22 (blueprint: def-per-integral-monoscheme-realization). -/
def Tower.integralSpaceToZero {n : ℕ} (T : Tower.{u} n) (i : Fin (n + 1)) :
    (T.level i).space ⟶ (T.level 0).space :=
  Fin.induction (𝟙 _) (fun j g ↦ (T.arrow j).map ≫ g) i

/-- The monoidal-space map to the given initial affine monoid spectrum.
Source: ILO VIII 3.1.22 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def Tower.integralSpaceToBase {n : ℕ} (T : Tower.{u} n) {P : Type u} [CommMonoid P]
    (e : (T.level 0).space ≅ affine P) (i : Fin (n + 1)) :
    (T.level i).space ⟶ affine P :=
  Fin.induction e.hom (fun j g ↦ (T.arrow j).map ≫ g) i

/-- Arbitrary chart base change, as the scheme fibre product.
Source: ILO VIII 3.3.5 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralBaseChange {P : Type u} [CommMonoid P] (A : Type u) [CommRing A]
    (α : P →* A) {M : Fine.{u}} (f : M.space ⟶ affine P) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (MonoidAlgebra.lift ℤ A P α).toRingHom))
    (integralToAffine f)

/-- Projection of the actual base change to Spec A. Source: ILO VIII 3.3.5
(blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralBaseProjection {P : Type u} [CommMonoid P]
    (A : Type u) [CommRing A] (α : P →* A) {M : Fine.{u}} (f : M.space ⟶ affine P) :
    integralBaseChange A α f ⟶ Spec (.of A) :=
  pullback.fst _ _

/-- The transition is uniquely fixed by its two fibre-product projections.
Source: ILO VIII 3.3.5 (blueprint: def-per-integral-monoscheme-realization).
Proof: the monomial characterizations give commutation with the maps to Spec Z[P].
Compose the source projection with the integral realization of b. The pullback
universal property gives the unique arrow with these two components. -/
theorem existsUnique_integralBaseMap {P : Type u} [CommMonoid P]
    (A : Type u) [CommRing A] (α : P →* A) {N M : Fine.{u}}
    (b : N.space ⟶ M.space) (f : M.space ⟶ affine P) :
    ∃! g : integralBaseChange A α (b ≫ f) ⟶ integralBaseChange A α f,
      g ≫ integralBaseProjection A α f = integralBaseProjection A α (b ≫ f) ∧
      g ≫ pullback.snd _ _ = pullback.snd _ _ ≫ integralMap b := by
  sorry

/-- The canonical transition after arbitrary base change. Source: ILO VIII 3.3.5
(blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralBaseMap {P : Type u} [CommMonoid P]
    (A : Type u) [CommRing A] (α : P →* A) {N M : Fine.{u}}
    (b : N.space ⟶ M.space) (f : M.space ⟶ affine P) :
    integralBaseChange A α (b ≫ f) ⟶ integralBaseChange A α f :=
  Classical.choose (existsUnique_integralBaseMap A α b f).exists

/-- The right tensor factor map, with the recorded chart actions.
Source: ILO VIII 3.3.5 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralTensorRight {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (A : Type u) [CommRing A] (α : P →* A) (i : P →* Q) :
    MonoidAlgebra ℤ Q →+* logIdealTensorRing A α i := by
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ i).toAlgebra
  exact Algebra.TensorProduct.includeRight.toRingHom

/-- The localization Q[T⁻¹] inside its ambient group, retaining all units.
Source: ILO VIII 3.1.4 (blueprint: def-per-integral-monoscheme-realization). -/
def integralLocalizedMonoid {G : Type u} [CommGroup G] (Q : Submonoid G)
    (T : Submonoid Q) : Submonoid G :=
  Submonoid.closure ((Q : Set G) ∪ {g | ∃ t : T, g = (t.1.1)⁻¹})

/-- The actual inclusion of Q in Q[T⁻¹]. Source: ILO VIII 3.1.4
(blueprint: def-per-integral-monoscheme-realization). -/
def integralLocalizationInclusion {G : Type u} [CommGroup G] (Q : Submonoid G)
    (T : Submonoid Q) : Q →* integralLocalizedMonoid Q T :=
  Q.subtype.codRestrict _ (fun q ↦ Submonoid.subset_closure (Or.inl q.2))

/-- The chart in the ambient group contains the original monoid via its canonical map.
Source: ILO VIII 3.1.21 (blueprint: def-per-integral-monoscheme-realization). -/
def integralChartInclusion {P : Type u} [CommMonoid P]
    (Q : Submonoid (Algebra.GrothendieckGroup P))
    (h : ∀ p : P, Algebra.GrothendieckGroup.of p ∈ Q) : P →* Q :=
  (Algebra.GrothendieckGroup.of (M := P)).codRestrict Q h

/-- An fs monoid chart inside the original group, over its specified base monoid.
The inclusion and group-generation fields express P ⊆ Q ⊆ G and Qᵍᵖ = G.
Source: ILO VIII 3.1.21, 3.2.2 (blueprint: def-per-integral-monoscheme-realization). -/
structure IntegralToricChart {P : Type u} [CommMonoid P] {M : Fine.{u}}
    (f : M.space ⟶ affine P) where
  monoid : Submonoid (Algebra.GrothendieckGroup P)
  containsBase : ∀ p : P, Algebra.GrothendieckGroup.of p ∈ monoid
  fine : FineFan.IsFine monoid
  saturated : monoid.PowSaturated
  groupCompletion : Subgroup.closure (monoid : Set (Algebra.GrothendieckGroup P)) = ⊤
  chart : AffineOpen M.space monoid
  overBase : IsAffineMap (integralChartInclusion monoid containsBase) (chart.inclusion ≫ f)

/-- The tensor chart arrow is uniquely determined by the two prescribed projections.
Source: ILO VIII 3.3.5 (blueprint: def-per-integral-monoscheme-realization).
Proof: the affine monoid-map characterization identifies the composite to Spec Z[P]
with the Spec map of Z[P] → Z[Q]. The two tensor-factor inclusions therefore give
compatible maps to Spec A and Z[M]. The scheme pullback property gives the unique arrow. -/
theorem existsUnique_integralTensorChart {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (A : Type u) [CommRing A] (α : P →* A) {M : Fine.{u}}
    (f : M.space ⟶ affine P) (hQ : FineFan.IsFine Q) (c : AffineOpen M.space Q)
    (i : P →* Q) (hc : IsAffineMap i (c.inclusion ≫ f)) :
    ∃! g : Spec (.of (logIdealTensorRing A α i)) ⟶ integralBaseChange A α f,
      g ≫ integralBaseProjection A α f = Spec.map (CommRingCat.ofHom (logIdealTensorBase A α i)) ∧
      g ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (integralTensorRight A α i)) ≫
        integralChartι hQ c := by
  sorry

/-- The tensor chart map with its specified monomial normalization.
Source: ILO VIII 3.3.5 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralTensorChart {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (A : Type u) [CommRing A] (α : P →* A) {M : Fine.{u}}
    (f : M.space ⟶ affine P) (hQ : FineFan.IsFine Q) (c : AffineOpen M.space Q)
    (i : P →* Q) (hc : IsAffineMap i (c.inclusion ≫ f)) :
    Spec (.of (logIdealTensorRing A α i)) ⟶ integralBaseChange A α f :=
  Classical.choose (existsUnique_integralTensorChart A α f hQ c i hc).exists

/-- The chart inclusion after base change. Source: ILO VIII 3.3.5
(blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def IntegralToricChart.baseChangeι {P : Type u} [CommMonoid P]
    {M : Fine.{u}} {f : M.space ⟶ affine P} (C : IntegralToricChart f)
    (A : Type u) [CommRing A] (α : P →* A) :
    Spec (.of (logIdealTensorRing A α (integralChartInclusion C.monoid C.containsBase))) ⟶
      integralBaseChange A α f :=
  integralTensorChart A α f C.fine C.chart
    (integralChartInclusion C.monoid C.containsBase) C.overBase

/-- A monoid fraction q/t in the specified localization within the ambient group.
Source: ILO VIII 3.1.4 (blueprint: def-per-integral-monoscheme-realization). -/
def integralMonoidFraction {G : Type u} [CommGroup G] (Q : Submonoid G)
    (T : Submonoid Q) (q : Q) (t : T) : integralLocalizedMonoid Q T :=
  integralLocalizationInclusion Q T q *
    ⟨t.1.1⁻¹, Submonoid.subset_closure (Or.inr ⟨t, rfl⟩)⟩

/-- The denominators in the tensor chart are the indicated monomials.
Source: ILO VIII 3.3.5 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralTensorDenominators {P Q : Type u}
    [CommMonoid P] [CommMonoid Q] (A : Type u) [CommRing A] (α : P →* A)
    (i : P →* Q) (T : Submonoid Q) : Submonoid (logIdealTensorRing A α i) :=
  T.map (logIdealTensorMonomial A α i)

/-- The literal fraction (a ⊗ z^q)/(1 ⊗ z^t), without any injectivity assumption.
Source: ILO VIII 3.3.5 (blueprint: def-per-integral-monoscheme-realization). -/
noncomputable def integralTensorFraction {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (A : Type u) [CommRing A] (α : P →* A) (i : P →* Q) (T : Submonoid Q)
    (a : A) (q : Q) (t : T) : Localization (integralTensorDenominators A α i T) :=
  Localization.mk (logIdealTensorBase A α i a * logIdealTensorMonomial A α i q)
    ⟨logIdealTensorMonomial A α i t.1, ⟨t.1, t.2, rfl⟩⟩

end AlgebraicGeometry.Monoscheme
