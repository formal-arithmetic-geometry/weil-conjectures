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

/-- The projection composition square and the inverse-compositor pentagon, in the ambient
ordinary derived categories of modules over the pulled-back finite condensed ring.
Source: fix-prop-projection-formula.proof.md, coherence sentence, and
prop-sf-pf-coherence.proof.md, pentagon paragraph
(blueprint: lem-sf-finite-projection-composition-transport).

Proof plan:
1. Choose bounded constructible etale origins M,N of K,L. Finite Noetherian coefficient
comparison preserves the Tor interval of N, as does pullback. A bounded flat model of N
makes M tensor P(N) bounded. F_f(M) tensor P_g(N) is bounded below, since open extension
is exact and proper derived direct image preserves the lower bound.
2. The counit-normalized proper comparison commutes with the proper projection map by
ringed exchange/tensor coherence. The canonical open comparison commutes with the open
tensor map. Compose the equations and use naturality at the open tensor map. This
identifies the specified proper-then-open projection under site comparison.
3. Apply the etale shriek/tensor composition equation. Conjugate by tensor symmetries
since that equation places the factors in the other order. Pullback compositors respect
these symmetries and their compositions.
4. First use a compatible compactification tower. The unbounded etale compositor restricts
to the bounded-below one. Apply site comparison, substitute the projection equation and
the binary compositor normalization, and cancel internal comparisons. Pullback comparison
coherence identifies chi. Cancel the endpoint isomorphisms and conjugate by the origin
isomorphisms. Inverting alpha gives the first displayed equality. Common proper
refinements transport it to all supplied compactifications, since both projections and
compositors respect the normalized refinement maps.
5. Invert canonical compositor associativity. Functors preserve inverses and inverses
reverse composites. The copied final compactification inserts exactly Category.assoc.
This proves the second equality. K is never required to have finite Tor amplitude, and
no projection component is inverted. -/
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
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteProjectionComposition
