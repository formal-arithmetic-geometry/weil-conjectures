module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Quotient, normalizer and fixed-point interfaces for split flags

Source: Milne, Algebraic Groups (2017), Definition 5.20, Proposition 21.1, p.424,
and Section 21h, p.446 (blueprint: def-sfb-split-flag-functors).

The coequalizer is the right-coset presheaf. Its universal arrow to the represented
sheaf is exactly sheafification. The fixed-point predicate uses all further algebra
extensions and all local representatives; thus it does not assume that a quotient
point has a rational lift. No action or normalizer representative is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.SplitFlag

/-- A represented fppf sheafification of the right-coset presheaf, with its quotient map.
Restriction from test schemes to affine test algebras gives the same fppf sheafification.
Representable functors are fppf sheaves by subcanonicity.
Source: Milne, Definition 5.20, pp.104--105
(blueprint: def-sfb-split-flag-functors). -/
def IsCosetQuotient {F : Type u} [Field F] {B H : Grp (Over (Spec (.of F)))}
    (i : B ⟶ H) {Q : Over (Spec (.of F))} (q : H.X ⟶ Q) : Prop :=
  ∃ ηq : coequalizer (yoneda.map (fst H.X B.X))
      (yoneda.map (fst H.X B.X * (snd H.X B.X ≫ i.hom.hom))) ⟶ yoneda.obj Q,
    coequalizer.π _ _ ≫ ηq = yoneda.map q ∧
    ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
      Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηq ≫ f)

/-- Universal normalization: conjugation preserves the torus image after every algebra map.
There is no reducedness or field assumption on either test algebra.
Source: Milne, Proposition 21.1, p.424
(blueprint: def-sfb-split-flag-functors). -/
def Normalizes {F : Type u} [Field F] {T H : Grp (Over (Spec (.of F)))}
    (i : T ⟶ H) {A : Type u} [CommRing A] [Algebra F A]
    (g : (algSpec (.of F)).obj (.op (CommAlgCat.of F A)) ⟶ H.X) : Prop :=
  ∀ (A' : Type u) [CommRing A'] [Algebra F A'] (f : A →ₐ[F] A'),
    Set.range (fun t : (algSpec (.of F)).obj (.op (CommAlgCat.of F A')) ⟶ T.X ↦
      ((algSpec (.of F)).map (CommAlgCat.ofHom f).op ≫ g) * (t ≫ i.hom.hom) *
        ((algSpec (.of F)).map (CommAlgCat.ofHom f).op ≫ g)⁻¹) =
      Set.range (fun t : (algSpec (.of F)).obj (.op (CommAlgCat.of F A')) ⟶ T.X ↦ t ≫ i.hom.hom)

/-- Scheme-theoretic torus-fixed quotient points. Test every extension and every lift of
its restriction: left multiplication by every torus point preserves that lift's coset.
Local existence of lifts for a coset sheaf makes this equivalent to the universal
fixed-point condition for its canonical left action, including for nonreduced algebras.
Source: Milne, Section 21h, paragraph before Proposition 21.70, p.446
(blueprint: def-sfb-split-flag-functors). -/
def IsFixed {F : Type u} [Field F] {T H : Grp (Over (Spec (.of F)))}
    (i : T ⟶ H) {Q : Over (Spec (.of F))} (q : H.X ⟶ Q)
    {A : Type u} [CommRing A] [Algebra F A]
    (x : (algSpec (.of F)).obj (.op (CommAlgCat.of F A)) ⟶ Q) : Prop :=
  ∀ (A' : Type u) [CommRing A'] [Algebra F A'] (f : A →ₐ[F] A')
    (g : (algSpec (.of F)).obj (.op (CommAlgCat.of F A')) ⟶ H.X),
    g ≫ q = (algSpec (.of F)).map (CommAlgCat.ofHom f).op ≫ x →
    ∀ t : (algSpec (.of F)).obj (.op (CommAlgCat.of F A')) ⟶ T.X,
      ((t ≫ i.hom.hom) * g) ≫ q = g ≫ q

/-- A closed immersion representing the entire fixed subfunctor, on all test algebras.
Existence and uniqueness of the factor through E identify its functor with the fixed functor.
Source: Milne, Section 21h, p.446 (blueprint: def-sfb-split-flag-functors). -/
def RepresentsFixed {F : Type u} [Field F] {T H : Grp (Over (Spec (.of F)))}
    (i : T ⟶ H) {Q E : Over (Spec (.of F))} (q : H.X ⟶ Q) (e : E ⟶ Q) : Prop :=
  IsClosedImmersion e.left ∧
    ∀ (A : Type u) [CommRing A] [Algebra F A]
      (x : (algSpec (.of F)).obj (.op (CommAlgCat.of F A)) ⟶ Q),
      IsFixed i q x ↔ ∃! y : (algSpec (.of F)).obj (.op (CommAlgCat.of F A)) ⟶ E, y ≫ e = x

/-- Scalar extension of a rational point via the canonical unit comparison for pullback.
Source: Milne, Chapter 21, p.424 (blueprint: def-sfb-split-flag-functors). -/
def extendPoint {F L : Type u} [Field F] [Field L] [Algebra F L]
    {X : Over (Spec (.of F))} (x : 𝟙_ (Over (Spec (.of F))) ⟶ X) :
    𝟙_ (Over (Spec (.of L))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj X :=
  (Functor.Monoidal.εIso
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L))))).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map x

end AlgebraicGeometry.SplitFlag
