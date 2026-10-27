module

public import Sheaf.AlgebraicGeometry.StrictBirationalLaw
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Sheaf.AlgebraicGeometry.StrictLawTranslationEmbedding

/-!
# Completion of a strict birational law defined on a dense open square

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §5.3 Lemma 8, pp.127--128,
using the translation functor of §5.2 Lemma 4
(blueprint: lem-sfb-strict-law-complete-square-group).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

noncomputable section

/-- A strict birational law defined on a relatively dense open square completes uniquely to
an `S`-group scheme structure on the same scheme.
Source: BLR, §5.3 Lemma 8 (blueprint: lem-sfb-strict-law-complete-square-group).

Proof plan:
1. The graph-chart lemma (lem-sfb-strict-law-graph-charts) supplies rational left division
   `d(a,c)`. The faithful translation map (lem-sfb-strict-law-translation-embedding) sends
   products to composition and division to inverse composition, before any group structure
   on `Z` has been constructed.
2. Over `(b,c)`, choose the open set of auxiliary `a` where `n(b,a)` and `d(a,c)` lie in `U`.
   Birationality of graph charts in both variables makes this open surjective over `Z²`.
   The morphism `n(n(b,a),d(a,c))` agrees with `n(b,c)` by translation injectivity.
   Flat detection (lem-sfb-relative-rational-flat-regularity) extends multiplication to `Z²`.
3. On the similarly surjective open where `d(b,a)` and `d(a,c)` exist, their now globally
   defined product represents `d(b,c)`. Flat detection extends division to all of `Z²`.
   The graph projections are now surjective, so the translation identities hold on arbitrary
   test schemes, including nonreduced ones.
4. Choose the given section `z₀`. Set `e=d(z₀,z₀)` and `i(x)=d(x,e)`. Faithful translations
   prove associativity, both unit laws and both inverse laws. Universal points turn these
   into the scheme-morphism diagrams encoded by `GrpObj`.
5. Flat regularity gives uniqueness of global multiplication with this rational law.
   For fixed multiplication, the elementary group identities give uniqueness of the unit
   and inverse, hence uniqueness of the entire `GrpObj` structure.
-/
theorem RelativeBirational.StrictLaw.existsUnique_group_of_complete_square
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsStrictlyHenselianLocalRing A]
    (hA : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (Z : Over (Spec (CommRingCat.of A)))
    [Smooth Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (hfibres : ∀ s : Spec (CommRingCat.of A), Nonempty (Z.hom.fiber s))
    (n : RelativeBirational.StrictLaw Z)
    (hsection : Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ Z))
    (U : Z.left.Opens) (hU : RelativeBirational.FibrewiseDense Z.hom U)
    (square : RelativeBirational.PartialMap (RelativeBirational.square Z) Z)
    (hsquare : square.domain =
      (pullback.fst Z.hom Z.hom ⁻¹ᵁ U) ⊓ (pullback.snd Z.hom Z.hom ⁻¹ᵁ U))
    (hn : n.mul.Agrees square) :
    ∃! G : GrpObj Z,
      ∃ (H : (RelativeBirational.square Z).left.Opens),
        RelativeBirational.FibrewiseDense (RelativeBirational.square Z).hom H ∧
          ∃ hH : H ≤ n.mul.domain,
            (RelativeBirational.square Z).left.homOfLE hH ≫ n.mul.hom =
              H.ι ≫ (@MonObj.mul _ _ _ Z G.toMonObj).left := by
  sorry

end

end AlgebraicGeometry
