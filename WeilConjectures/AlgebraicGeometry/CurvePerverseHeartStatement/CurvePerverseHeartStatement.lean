/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPerverseSubcategories
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# The support-defined perverse heart on a smooth curve

Source: latest blueprint, `thm-a1-curve-perverse-heart`, clauses (1)–(5) and
proof Steps 0–6. The actual support/cosupport predicates are compared with the
punctual descriptions; they are not replaced by those descriptions.
(blueprint: thm-a1-curve-perverse-heart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CurvePerverseHeartStatement

section General

variable {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
  (Q : ObjectProperty (DerivedCategory A))
  (le ge : ℤ → ObjectProperty Q.FullSubcategory)
  (leZero geZero : ObjectProperty Q.FullSubcategory) (punctual : ObjectProperty A)

/-- Absence of nonzero punctual constructible subsheaves.
Source: clause (1) (blueprint: thm-a1-curve-perverse-heart). -/
def NoPunctualSubobject (F : A) : Prop :=
  ∀ (G : A) (i : G ⟶ F), Mono i → punctual G → IsZero G

/-- The recorded heart as a property of ambient complexes, retaining the
bounded-constructible membership witness.
Source: clauses (2)–(4) (blueprint: thm-a1-curve-perverse-heart). -/
def InHeart (K : DerivedCategory A) : Prop :=
  ∃ hK : Q K, leZero ⟨K, hK⟩ ∧ geZero ⟨K, hK⟩

/-- The canonical ordinary truncation sequence, represented in the actual heart.
The two comparison isomorphisms identify its maps with τ^{<0}P → P → τ^{≥0}P;
the last two isomorphisms identify its endpoints with H⁻¹P[1] and H⁰P[0].
Source: clause (5), Step 6 (blueprint: thm-a1-curve-perverse-heart). -/
def TruncationExactness : Prop :=
  ∀ P : (leZero ⊓ geZero).FullSubcategory,
    ∃ (B C : (leZero ⊓ geZero).FullSubcategory) (f : B ⟶ P) (g : P ⟶ C)
      (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact ∧
      ∃ (b : B.obj.obj ≅ (DerivedCategory.TStructure.t.truncLT 0).obj P.obj.obj)
        (c : C.obj.obj ≅ (DerivedCategory.TStructure.t.truncGE 0).obj P.obj.obj),
        f.hom.hom = b.hom ≫ (DerivedCategory.TStructure.t.truncLTι 0).app P.obj.obj ∧
        g.hom.hom ≫ c.hom = (DerivedCategory.TStructure.t.truncGEπ 0).app P.obj.obj ∧
        Nonempty (B.obj.obj ≅ (shiftFunctor _ (1 : ℤ)).obj
          ((DerivedCategory.singleFunctor A 0).obj
            ((DerivedCategory.homologyFunctor A (-1)).obj P.obj.obj))) ∧
        Nonempty (C.obj.obj ≅ (DerivedCategory.singleFunctor A 0).obj
          ((DerivedCategory.homologyFunctor A 0).obj P.obj.obj))

/-- Every short exact heart sequence comes from its distinguished triangle, and
its six ordinary cohomology terms are exact. The five arrows are the four induced
cohomology maps and the canonical connecting map of that triangle. Mono/epi at
the ends express the two zero endpoints in the displayed sequence.
Source: clause (5), Step 6 (blueprint: thm-a1-curve-perverse-heart). -/
def SixTermExactness : Prop :=
  ∀ S : ShortComplex (leZero ⊓ geZero).FullSubcategory, S.ShortExact →
    ∃ δ : S.X₃.obj.obj ⟶ (shiftFunctor _ (1 : ℤ)).obj S.X₁.obj.obj,
      let T := Triangle.mk S.f.hom.hom S.g.hom.hom δ
      T ∈ distTriang _ ∧
      (ComposableArrows.mk₅
        ((DerivedCategory.homologyFunctor A (-1)).map S.f.hom.hom)
        ((DerivedCategory.homologyFunctor A (-1)).map S.g.hom.hom)
        (DerivedCategory.HomologySequence.δ T (-1) 0)
        ((DerivedCategory.homologyFunctor A 0).map S.f.hom.hom)
        ((DerivedCategory.homologyFunctor A 0).map S.g.hom.hom)).Exact ∧
      Mono ((DerivedCategory.homologyFunctor A (-1)).map S.f.hom.hom) ∧
      Epi ((DerivedCategory.homologyFunctor A 0).map S.g.hom.hom)

/-- Clauses (1), (2), (3), and (5), for specified support/cosupport classes.
The triangulation is the inherited one on the full subcategory, and the heart
has its inherited morphisms. No replacement t-structure or arbitrary arrows are supplied.
Source: clauses (1)–(5) (blueprint: thm-a1-curve-perverse-heart). -/
def Assertions : Prop :=
  (∀ K : Q.FullSubcategory,
    (leZero K ↔ (∀ a : ℤ, 0 < a →
      IsZero ((DerivedCategory.homologyFunctor A a).obj K.obj)) ∧
      punctual ((DerivedCategory.homologyFunctor A 0).obj K.obj)) ∧
    (geZero K ↔ (∀ a : ℤ, a < -1 →
      IsZero ((DerivedCategory.homologyFunctor A a).obj K.obj)) ∧
      NoPunctualSubobject punctual ((DerivedCategory.homologyFunctor A (-1)).obj K.obj))) ∧
  (Exists fun [_hTri : Q.IsTriangulated] ↦
    ∃ t : TStructure Q.FullSubcategory,
      (∀ K n, t.le n K ↔ le n K) ∧ (∀ K n, t.ge n K ↔ ge n K) ∧
      (∀ K, t.le 0 K ↔ leZero K) ∧ (∀ K, t.ge 0 K ↔ geZero K) ∧ t.bounded = ⊤) ∧
  Nonempty (Abelian (leZero ⊓ geZero).FullSubcategory) ∧
  (∀ K : Q.FullSubcategory,
    (leZero K ∧ geZero K) ↔
      (∀ a : ℤ, a ≠ -1 → a ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor A a).obj K.obj)) ∧
      punctual ((DerivedCategory.homologyFunctor A 0).obj K.obj) ∧
      NoPunctualSubobject punctual ((DerivedCategory.homologyFunctor A (-1)).obj K.obj)) ∧
  TruncationExactness Q leZero geZero ∧ SixTermExactness Q leZero geZero

end General

/-- Actual sheaves of modules over the pulled-back condensed coefficient ring.
Source: ambient sheaves (blueprint: thm-a1-curve-perverse-heart). -/
abbrev Modules (ell : ℕ) [Fact ell.Prime] (C : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ell) C)

/-- A constructible sheaf supported on finitely many closed points. Empty support
is allowed. The support is the recorded geometric-stalk support.
Source: opening definition (blueprint: thm-a1-curve-perverse-heart). -/
def Punctual (ell : ℕ) [Fact ell.Prime] (C : Scheme.{u}) : ObjectProperty (Modules ell C) :=
  fun F ↦ IsConstructibleModuleObject
    (condensedRingObj (Profinite.padicAlgClRingObj ell) C) F ∧
    (condensedModuleSupport (condensedRingObj (Profinite.padicAlgClRingObj ell) C) F).Finite ∧
    ∀ x ∈ condensedModuleSupport
      (condensedRingObj (Profinite.padicAlgClRingObj ell) C) F, IsClosed ({x} : Set C)

section Geometric

variable (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k] [Invertible (ell : k)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- All five geometric clauses, on the landed any-field perverse subcategories.
The basic objects use ordinary module direct image, not derived direct image.
Source: clauses (1)–(5) (blueprint: thm-a1-curve-perverse-heart). -/
def GeometricAssertions : Prop :=
  Assertions (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (CondensedPerverseLE ell X) (CondensedPerverseGE ell X)
    (CondensedPerverseLEZero ell X) (CondensedPerverseGEZero ell X) (Punctual ell X.left) ∧
  (∀ (U : Scheme.{u}) (j : U ⟶ X.left), IsOpenImmersion j → DenseRange j →
    ∀ M : Modules ell U, IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M →
      InHeart (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
        (CondensedPerverseLEZero ell X) (CondensedPerverseGEZero ell X)
        ((shiftFunctor _ (1 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell) j).obj M)))) ∧
  (∀ (x : X.left), IsClosed ({x} : Set X.left) →
    ∀ E : Modules ell (Spec (X.left.residueField x)),
      IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ell)
        (Spec (X.left.residueField x))) E →
      InHeart (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
        (CondensedPerverseLEZero ell X) (CondensedPerverseGEZero ell X)
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell)
            (X.left.fromSpecResidueField x)).obj E)))

end Geometric

section Weil

open WeilConjectures

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  [Invertible (ell : D.k)]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

-- These local instances only unfold the recorded geometric fibre to its pullback.
local instance : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
local instance : QuasiCompact (D.geometricFiber X₀).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
local instance : IsSeparated (D.geometricFiber X₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The degree-zero Weil support class uses the recorded geometric support class.
Source: Weil convention (blueprint: thm-a1-curve-perverse-heart). -/
def WeilLEZero : ObjectProperty
    (condensedWeilComplex (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius X₀).hom) :=
  fun K ↦ CondensedPerverseLEZero ell (D.geometricFiber X₀)
    ((condensedWeilForget (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom).obj K)

/-- The degree-zero Weil cosupport class uses the recorded geometric cosupport class.
Source: Weil convention (blueprint: thm-a1-curve-perverse-heart). -/
def WeilGEZero : ObjectProperty
    (condensedWeilComplex (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius X₀).hom) :=
  fun K ↦ CondensedPerverseGEZero ell (D.geometricFiber X₀)
    ((condensedWeilForget (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom).obj K)

/-- The perverse classes on actual derived Weil complexes are tested after the
canonical exact forgetful functor, on the geometric fibre.
Source: Weil convention (blueprint: thm-a1-curve-perverse-heart). -/
def WeilLE (n : ℤ) : ObjectProperty
    (condensedWeilComplex (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius X₀).hom) :=
  fun K ↦ CondensedPerverseLE ell (D.geometricFiber X₀) n
    ((condensedWeilForget (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom).obj K)

/-- The Weil cosupport class, on the same exact geometric forgetful functor.
Source: Weil convention (blueprint: thm-a1-curve-perverse-heart). -/
def WeilGE (n : ℤ) : ObjectProperty
    (condensedWeilComplex (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius X₀).hom) :=
  fun K ↦ CondensedPerverseGE ell (D.geometricFiber X₀) n
    ((condensedWeilForget (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom).obj K)

/-- Punctual Weil sheaves are tested on their underlying geometric sheaves.
Source: Weil convention (blueprint: thm-a1-curve-perverse-heart). -/
def WeilPunctual : ObjectProperty
    (condensedWeilModules (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius X₀).hom) :=
  fun M ↦ Punctual ell (D.geometricFiber X₀).left M.carrier

/-- All five clauses for actual Weil complexes, together with the two basic-object
families. Closed-point direct images carry their canonical Weil structure.
Source: clauses (1)–(5), Weil convention (blueprint: thm-a1-curve-perverse-heart). -/
def WeilAssertions : Prop :=
  let Q := condensedWeilComplexProperty (Profinite.padicAlgClRingObj ell)
    (D.geometricFrobenius X₀).hom
  Assertions Q (WeilLE D ell X₀) (WeilGE D ell X₀)
    (WeilLEZero D ell X₀) (WeilGEZero D ell X₀) (WeilPunctual D ell X₀) ∧
  (∀ (x : X₀.left) (hx : IsClosed ({x} : Set X₀.left)),
    letI : IsClosedImmersion (X₀.left.fromSpecResidueField x) :=
      (AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion).mp hx
    let Z₀ := Over.mk (X₀.left.fromSpecResidueField x ≫ X₀.hom)
    letI : LocallyOfFiniteType Z₀.hom := inferInstanceAs
      (LocallyOfFiniteType (X₀.left.fromSpecResidueField x ≫ X₀.hom))
    letI : QuasiCompact Z₀.hom := inferInstanceAs
      (QuasiCompact (X₀.left.fromSpecResidueField x ≫ X₀.hom))
    let i₀ : Z₀ ⟶ X₀ := Over.homMk (X₀.left.fromSpecResidueField x)
    ∀ E : NativeL2.WeilModule D ell Z₀,
      IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ell)
        (D.geometricFiber Z₀).left) E.carrier →
        InHeart Q (WeilLEZero D ell X₀) (WeilGEZero D ell X₀)
          ((DerivedCategory.singleFunctor _ 0).obj (NativeL2.middleWeilImage D ell i₀ E))) ∧
  (∀ (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom]
    [QuasiCompact U₀.hom] (j₀ : U₀ ⟶ X₀), IsOpenImmersion j₀.left → DenseRange j₀.left →
    ∀ M : NativeL2.WeilModule D ell U₀,
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier →
      InHeart Q (WeilLEZero D ell X₀) (WeilGEZero D ell X₀)
        ((shiftFunctor _ (1 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj
          (NativeL2.middleWeilImage D ell j₀ M))))
end Weil

/-- The complete geometric curve theorem, on the actual support/cosupport classes.
Source: latest blueprint, thm-a1-curve-perverse-heart, proof Steps 0–6.
Proof: (0) Descend coefficients to a finite extension and use lattices and finite
locally constant reductions: a lisse sheaf has no punctual subsheaf. The kernel
of F → j_*j^*F is its maximal punctual subsheaf and the quotient has none.
(1) In dimension one the support inequalities are exactly positive-degree
vanishing and punctual H⁰. (2) Smooth purity gives ω_U = Ω(1)[2] and ω_Z = Ω;
lisse tensor duality computes dual cohomology on U and finite closed Z.
(3) Localization and closed-costalk duality identify cosupport with vanishing
below -1 and absence of the punctual radical in H⁻¹. (4) These formulas imply
shift stability and orthogonality. The fibre of τ^{≤0}K → (H⁰K/F_p)[0] and the
octahedron give the perverse truncation triangle. Standard amplitude [a,b]
gives perverse bounds [a,b+1], hence boundedness and the abelian heart; its
intersection gives the heart description. (5) The punctual radical computation
puts j_*N[1] and i_*E[0] in the heart. (6) The ordinary truncation triangle has
all three vertices in the heart, giving the specified short exact sequence.
Conversely a short exact heart sequence gives a distinguished triangle; its
ordinary cohomology sequence has the stated six terms and zero endpoints.
(blueprint: thm-a1-curve-perverse-heart). -/
theorem curve_perverse_heart_statement (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [PerfectField k] [Invertible (ell : k)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [Smooth X.hom] (_hPure : Scheme.IsPureDimension X.left 1) :
    GeometricAssertions ell X := by
  sorry

/-- The same five clauses for Weil complexes over a finite field.
Source: latest blueprint, thm-a1-curve-perverse-heart, Steps 0–6 and Weil convention.
Proof: perform Steps 0–6 in the preceding theorem equivariantly. Frobenius
preserves the support and cosupport classes and all ordinary truncations.
The punctual radical, its quotient, and the fibre used in Step 4 carry their
canonical Weil isomorphisms. Thus the bounded t-structure and its abelian heart
are defined on actual derived Weil modules. Ordinary direct images carry the
Frobenius base-change mate, giving Step 5. The truncation maps and the connecting
map in Step 6 are maps of Weil sheaves; exact forgetting gives the displayed
six-term sequence with its Weil structures.
(blueprint: thm-a1-curve-perverse-heart). -/
theorem weil_curve_perverse_heart_statement (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] [Invertible (ell : D.k)]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] [Smooth X₀.hom] (_hPure : Scheme.IsPureDimension X₀.left 1) :
    WeilAssertions D ell X₀ := by
  sorry

end AlgebraicGeometry.ProEtale.CurvePerverseHeartStatement
