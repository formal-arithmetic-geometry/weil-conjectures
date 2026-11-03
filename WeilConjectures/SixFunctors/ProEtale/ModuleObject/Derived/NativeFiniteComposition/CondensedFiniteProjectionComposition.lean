/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteProjectionComposition.CondensedFiniteCompositorGeometry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteProjectionComposition.CondensedFiniteForwardProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteComposition.CondensedFiniteCompositionCoordinates

/-! # Finite projection composition and inverse-compositor associativity

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, coherence sentence; and
sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md, pentagon paragraph.
(blueprint: lem-sf-finite-projection-composition-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeFiniteComposition

open CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The component of common-refinement transport, with the graph common refinement.
Source: thm-sf-comp-composition, compactification independence
(blueprint: lem-sf-finite-projection-composition-transport). -/
def change {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (K : D Λ X) : (F Λ c).obj K ⟶ (F Λ d).obj K :=
  (refinement Λ (Compactification.infFst c d)).app K ≫
    CondensedOpenProper.comparisonInverse
      ((refinement Λ (Compactification.infSnd c d)).app K)

/-- Restriction of the proper image of the source open, followed by the inverse open unit.
Source: thm-sf-comp-composition, tower normalization
(blueprint: lem-sf-finite-projection-composition-transport). -/
def towerRestriction {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (M : D Λ T.cf.Z) :
    (P Λ T.cg.i).obj ((R Λ T.p).obj ((J Λ T.q).obj M)) ⟶ (R Λ T.cf.g).obj M :=
  (baseChangeMap Λ T.isPullback.flip.toCommSq).app ((J Λ T.q).obj M) ≫
    (R Λ T.cf.g).map
      (CondensedOpenProper.comparisonInverse ((oa Λ T.q).unit.app M))

/-- The proper/open interchange is the open-adjunction transpose of inverse restriction.
Source: thm-sf-comp-composition, the specified tower arrow
(blueprint: lem-sf-finite-projection-composition-transport). -/
def towerInterchange {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (M : D Λ T.cf.Z) :
    (J Λ T.cg.i).obj ((R Λ T.cf.g).obj M) ⟶ (R Λ T.p).obj ((J Λ T.q).obj M) :=
  ((oa Λ T.cg.i).homEquiv _ _).symm
    (CondensedOpenProper.comparisonInverse (towerRestriction Λ T M))

/-- The forward tower compositor: proper/open interchange, open composition, then proper
composition and equality transport. Source: thm-sf-comp-composition, tower construction
(blueprint: lem-sf-finite-projection-composition-transport). -/
def tower {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (K : D Λ X) :
    (F Λ T.cg).obj ((F Λ T.cf).obj K) ⟶ (F Λ T.cfg).obj K :=
  (R Λ T.cg.g).map
      (towerInterchange Λ T ((J Λ T.cf.i).obj K) ≫
        (R Λ T.p).map
          ((jComp Λ T.cf.i T.q).hom.app K ≫ (jCongr Λ T.i_q).hom.app K)) ≫
    (rightDerivedLowerStarComp Λ T.p T.cg.g).hom.app ((J Λ T.cfg.i).obj K) ≫
    (eqToIso (congrArg (R Λ) T.p_g)).hom.app ((J Λ T.cfg.i).obj K)

/-- The canonical forward compositor in arbitrary supplied compactifications. The auxiliary
triangle is constructed geometrically from the supplied compactifications of g and gf.
Its components are transported by the prescribed common-refinement maps.
Source: thm-sf-comp-composition, construction and choice independence
(blueprint: lem-sf-finite-projection-composition-transport). -/
def forward {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (K : D Λ X) : (F Λ d).obj ((F Λ c).obj K) ⟶ (F Λ e).obj K :=
  let T := Compactification.Triangle.ofRestrict d (e.ofComp d)
  (F Λ d).map (change Λ c T.cf K) ≫ tower Λ T K ≫ change Λ T.cfg e K

/-- Sigma is the inverse of the specified forward compositor, on its finite etale-origin
inputs. The total inverse extends the formula to ambient objects without making an
invertibility assertion there. Source: thm-sf-comp-composition, inverse compositor
(blueprint: lem-sf-finite-projection-composition-transport). -/
def inverse {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (K : D Λ X) : (F Λ e).obj K ⟶ (F Λ d).obj ((F Λ c).obj K) :=
  CondensedOpenProper.comparisonInverse (forward Λ c d e K)

end AlgebraicGeometry.ProEtale.CondensedRing.NativeFiniteComposition

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteProjectionComposition

open CompactificationReindexing

/-- The actual positive-level quotient, regarded as a discrete condensed ring.
Source: the finite coefficient convention of fix-prop-projection-formula
(blueprint: lem-sf-finite-projection-composition-transport). -/
abbrev coefficient (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :=
  cartesianFinitePointRing (Padic.coefficientExtensionRing ell E n)

private theorem comparisonInverse_eq_inv
    {C : Type*} [Category C] [HasZeroMorphisms C] {A B : C}
    (f : A ⟶ B) [IsIso f] :
    AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper.comparisonInverse f =
      inv f := by
  classical
  exact dif_pos (inferInstance : IsIso f)

private theorem inverse_composition_square
    {C : Type*} [Category C] {A B D E Q : C}
    (a : A ⟶ B) (b : D ⟶ E) [IsIso a] [IsIso b]
    (e : Q ≅ D) (p : A ⟶ Q) (q : B ⟶ E)
    (h : p ≫ e.hom ≫ b = a ≫ q) :
    inv a ≫ p = q ≫ inv b ≫ e.inv := by
  apply (cancel_mono (e.hom ≫ b)).1
  calc
    (inv a ≫ p) ≫ (e.hom ≫ b) = inv a ≫ (p ≫ e.hom ≫ b) := by
      simp only [Category.assoc]
    _ = inv a ≫ (a ≫ q) := by rw [h]
    _ = q := by simp
    _ = (q ≫ inv b ≫ e.inv) ≫ (e.hom ≫ b) := by simp

private theorem inverse_pentagon
    {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ D) (d : D ⟶ E)
    [IsIso a] [IsIso b] [IsIso c] [IsIso d]
    (h : a ≫ b = c ≫ d) : inv b ≫ inv a = inv d ≫ inv c := by
  have he : asIso a ≪≫ asIso b = asIso c ≪≫ asIso d := Iso.ext h
  exact congrArg Iso.inv he

/-- The projection composition square and the inverse-compositor pentagon, in the ambient
ordinary derived categories of modules over the pulled-back finite condensed ring.
Source: fix-prop-projection-formula.proof.md, coherence sentence, and
prop-sf-pf-coherence.proof.md, pentagon paragraph
(blueprint: lem-sf-finite-projection-composition-transport).

Proof:
1. The forward geometry theorem gives preservation of bounded constructibility,
invertibility of each specified forward compositor, and their forward associativity.
The forward projection theorem gives bounded constructibility of the tensor input
and the forward projection square, with no Tor assumption on K.
2. Let a be the forward compositor at K tensored with L, let b be the compositor at
K tensor P_fg L, and let e be F_g F_f applied to K tensor chi inverse. The forward
square is p followed by e.hom and b equals a followed by q. Cancel e.hom followed by
b; the result is inv a followed by p equals q followed by inv b and e.inv. Functors
and tensor whiskering preserve inverses. On these objects the total inverses in the
statement are categorical inverses, proving its first clause.
3. Preservation puts F_f K in the domain of the other two forward compositors.
Invert the equality of the two composites in forward associativity. Inversion
reverses the two factors, and functors preserve inverses, giving the stated inverse
pentagon with exactly the same copied final compactification. No projection component
is inverted in either argument. -/
theorem finite_projection_composition
    (B : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ B.p) (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (_hn : 1 ≤ n) :
    (∀ {X Y Z : SepFinType B.k} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
      (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cfg : Compactification (f.hom.left ≫ g.hom.left))
      (K : D (coefficient ell E n) X.obj.left)
      (_hK : boundedConstructible (condensedRingObj (coefficient ell E n) X.obj.left) K)
      (L : CondensedConstructibleFiniteTor (coefficient ell E n) Z.obj.left),
      (NativeFiniteComposition.inverse (coefficient ell E n) cf cg cfg K ▷ L.obj) ≫
          pf (coefficient ell E n) cg ((F (coefficient ell E n) cf).obj K) L.obj ≫
          (F (coefficient ell E n) cg).map
            (pf (coefficient ell E n) cf K ((P (coefficient ell E n) g.hom.left).obj L.obj)) =
        pf (coefficient ell E n) cfg K L.obj ≫
          NativeFiniteComposition.inverse (coefficient ell E n) cf cg cfg
            (K ⊗ (P (coefficient ell E n) (f.hom.left ≫ g.hom.left)).obj L.obj) ≫
          (F (coefficient ell E n) cg).map ((F (coefficient ell E n) cf).map
            (K ◁ (leftDerivedUpperStarComp (coefficient ell E n)
              f.hom.left g.hom.left).hom.app L.obj))) ∧
    (∀ {X Y Z W : SepFinType B.k} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
      [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
      (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (ch : Compactification h.hom.left)
      (cfg : Compactification (f.hom.left ≫ g.hom.left))
      (cgh : Compactification (g.hom.left ≫ h.hom.left))
      (cfgh : Compactification ((f.hom.left ≫ g.hom.left) ≫ h.hom.left))
      (K : D (coefficient ell E n) X.obj.left)
      (_hK : boundedConstructible (condensedRingObj (coefficient ell E n) X.obj.left) K),
      NativeFiniteComposition.inverse (coefficient ell E n) cfg ch cfgh K ≫
          (F (coefficient ell E n) ch).map
            (NativeFiniteComposition.inverse (coefficient ell E n) cf cg cfg K) =
        NativeFiniteComposition.inverse (coefficient ell E n) cf cgh
            (cfgh.copy (Category.assoc f.hom.left g.hom.left h.hom.left).symm) K ≫
          NativeFiniteComposition.inverse (coefficient ell E n) cg ch cgh
            ((F (coefficient ell E n) cf).obj K)) := by
  classical
  obtain ⟨hpres, hiso, hassoc⟩ := finite_compositor_geometry B ell _hell E n _hn
  constructor
  · intro X Y Z f g _ _ _ _ _ _ cf cg cfg K hK L
    obtain ⟨hT, hforward⟩ := finite_forward_projection B ell _hell E n _hn
      f g cf cg cfg K hK L
    let := hiso f g cf cg cfg K hK
    let := hiso f g cf cg cfg
      (K ⊗ (P (coefficient ell E n) (f.hom.left ≫ g.hom.left)).obj L.obj) hT
    let e := (F (coefficient ell E n) cg).mapIso
      ((F (coefficient ell E n) cf).mapIso
        (whiskerLeftIso K
          ((leftDerivedUpperStarComp (coefficient ell E n)
            f.hom.left g.hom.left).app L.obj).symm))
    have he := inverse_composition_square
      (NativeFiniteComposition.forward (coefficient ell E n) cf cg cfg K ▷ L.obj)
      (NativeFiniteComposition.forward (coefficient ell E n) cf cg cfg
        (K ⊗ (P (coefficient ell E n) (f.hom.left ≫ g.hom.left)).obj L.obj))
      e
      (pf (coefficient ell E n) cg ((F (coefficient ell E n) cf).obj K) L.obj ≫
        (F (coefficient ell E n) cg).map
          (pf (coefficient ell E n) cf K ((P (coefficient ell E n) g.hom.left).obj L.obj)))
      (pf (coefficient ell E n) cfg K L.obj)
      (by simpa only [e, Functor.mapIso_hom, whiskerLeftIso_hom,
        Iso.symm_hom, Iso.app_inv, Category.assoc] using hforward)
    simpa only [NativeFiniteComposition.inverse, comparisonInverse_eq_inv,
      inv_whiskerRight, e, Functor.mapIso_inv, whiskerLeftIso_inv,
      Iso.symm_inv, Iso.app_hom, Category.assoc] using he
  · intro X Y Z W f g h _ _ _ _ _ _ _ _ _ cf cg ch cfg cgh cfgh K hK
    let : IsSeparated (f ≫ g).hom.left := by
      change IsSeparated (f.hom.left ≫ g.hom.left)
      infer_instance
    let : LocallyOfFiniteType (f ≫ g).hom.left := by
      change LocallyOfFiniteType (f.hom.left ≫ g.hom.left)
      infer_instance
    let : QuasiCompact (f ≫ g).hom.left := by
      change QuasiCompact (f.hom.left ≫ g.hom.left)
      infer_instance
    let : IsSeparated (g ≫ h).hom.left := by
      change IsSeparated (g.hom.left ≫ h.hom.left)
      infer_instance
    let : LocallyOfFiniteType (g ≫ h).hom.left := by
      change LocallyOfFiniteType (g.hom.left ≫ h.hom.left)
      infer_instance
    let : QuasiCompact (g ≫ h).hom.left := by
      change QuasiCompact (g.hom.left ≫ h.hom.left)
      infer_instance
    let := hiso f g cf cg cfg K hK
    let := hiso (f ≫ g) h cfg ch cfgh K hK
    let := hiso g h cg ch cgh ((F (coefficient ell E n) cf).obj K)
      (hpres f cf K hK)
    let := hiso f (g ≫ h) cf cgh
      (cfgh.copy (Category.assoc f.hom.left g.hom.left h.hom.left).symm) K hK
    have he := inverse_pentagon
      ((F (coefficient ell E n) ch).map
        (NativeFiniteComposition.forward (coefficient ell E n) cf cg cfg K))
      (NativeFiniteComposition.forward (coefficient ell E n) cfg ch cfgh K)
      (NativeFiniteComposition.forward (coefficient ell E n) cg ch cgh
        ((F (coefficient ell E n) cf).obj K))
      (NativeFiniteComposition.forward (coefficient ell E n) cf cgh
        (cfgh.copy (Category.assoc f.hom.left g.hom.left h.hom.left).symm) K)
      (hassoc f g h cf cg ch cfg cgh cfgh K hK)
    simpa only [NativeFiniteComposition.inverse, comparisonInverse_eq_inv,
      ← Functor.map_inv] using he

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteProjectionComposition
