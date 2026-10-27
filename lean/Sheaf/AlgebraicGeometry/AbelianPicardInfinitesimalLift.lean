module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareData
public import Sheaf.AlgebraicGeometry.RigidifiedLines

import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality

/-! # Infinitesimal lifting of algebraically trivial rigidified lines

Source: Milne, Abelian Varieties, I Section 8, printed pp.36--37 (field Picard
variety and identity normalization); the relative lifting assertion and its
cohomological proof are the agent-stated extension recorded in the DAG.
Mumford--Fogarty--Kirwan, GIT, Proposition 6.7 remains a wanted reference.
(blueprint: lem-sfb-abelian-picard-infinitesimal-lift).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

open Poincare

/-- The actual pointed family over a parameter scheme after the base change `B → S`.
Composition in `Over` views the parameter as an `S`-scheme; the family and its section
are the existing sheaf fibre product and pulled-back identity section.
Source: Milne I Section 8, identity normalization; the DAG's relative lifting problem
(blueprint: lem-sfb-abelian-picard-infinitesimal-lift). -/
def picardInfinitesimalFamily {S : Scheme.{u}} (A : AlgebraicSpace S)
    (g : CommutativeSpaceGroup A) (B : Over S) (T : Over B.left) :
    Pointed (schemeSpace ((Over.map B.hom).obj T)) :=
  (pointedGroup A g).baseChange
    (groupSpaceProjection (schemeSpace ((Over.map B.hom).obj T)))

/-- The canonical map of parameter families, given by the identity on `A` and the
specified parameter map. The structural equality uses terminality of the represented
base, not a chosen comparison morphism.
Source: Milne I Section 8; sheaf fibre products in the DAG's relative lifting problem
(blueprint: lem-sfb-abelian-picard-infinitesimal-lift). -/
def picardInfinitesimalFamilyMap {S : Scheme.{u}} (A : AlgebraicSpace S)
    (g : CommutativeSpaceGroup A) (B : Over S) {U T : Over B.left} (a : U ⟶ T) :
    (picardInfinitesimalFamily A g B U).X ⟶ (picardInfinitesimalFamily A g B T).X :=
  pair
    (fst (groupSpaceProjection A)
      (groupSpaceProjection (schemeSpace ((Over.map B.hom).obj U))))
    (snd (groupSpaceProjection A)
      (groupSpaceProjection (schemeSpace ((Over.map B.hom).obj U))) ≫
        groupSchemeMap ((Over.map B.hom).map a))
    (baseMap_eq _ _)

/-- Algebraically trivial rigidified lines lift etale locally across any square-zero
closed immersion of affine parameters, also after every locally Noetherian base change.
A line is an object of the existing rigidified-line groupoid; its algebraic triviality
is tested through the existing equivalence with the small affine etale ringed model.
The overlap is the actual pullback `T₀ ×_T U j` in the scheme over-category. The two
section-square equalities below supply the canonical rigidification pullbacks; an
isomorphism in their common groupoid is precisely a rigidification-preserving line
isomorphism. Only existence is asserted.

Source: Milne, Abelian Varieties, I Section 8, printed pp.36--37 (normalization);
relative lifting input: the agent-stated extension in the DAG, with MFK GIT
Proposition 6.7 still wanted
(blueprint: lem-sfb-abelian-picard-infinitesimal-lift).

Proof plan:
1. By lem-sfb-stack-chartwise-smooth-etale-calculus, the parameter families are smooth
and flat. Flat tensoring identifies their square-zero ideals with O tensor I, also
on the two-factor product.
2. By lem-sfb-space-picard-obstruction-natural, M₀ has an obstruction o in H² of that
ideal. The identity m* M₀ = p₁* M₀ tensor p₂* M₀ from
lem-sfb-algebraically-trivial-line-multiplicativity and naturality of the obstruction
give m* o = p₁* o + p₂* o with the canonical coefficient maps.
3. The affine-parameter, arbitrary-coefficient assertion of
lem-sfb-abelian-h2-reduced-coproduct-injective gives o = 0, including for non-Noetherian
parameters. Exactness of lem-sfb-space-picard-obstruction-natural gives a line lift L
and an isomorphism on the closed fibre.
4. Put P = e* L and replace L by L tensor f* P⁻¹. Evaluation rigidifies this line.
If u : P|T₀ ≅ O is induced by the specified closed-fibre rigidification, tensoring
the original restriction isomorphism with f₀*((u⁻¹) dual) preserves rigidifications:
at the identity it sends p tensor lambda to u(p) lambda(u⁻¹(1)) = lambda(p).
5. Every geometric point kills I, so the lift has the same geometric fibres as M₀
and remains algebraically trivial. The singleton identity cover suffices. Under
B → S, properness and finite presentation persist by lem-sfb-space-flat-proper-fp-locality,
and smoothness by lem-sfb-stack-chartwise-smooth-etale-calculus. The geometric fibres
are the original abelian geometric fibres. Repeat steps 1--4 over B. The arbitrary
locally Noetherian B in the statement includes the identity base change.
-/
theorem exists_etale_rigidifiedLine_infinitesimalLift {S : Scheme.{u}}
    [IsLocallyNoetherian S] (A : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (hA : IsAbelianFamily (groupSpaceProjection A)) :
    ∀ (B : Over S) [IsLocallyNoetherian B.left] (T₀ T : Over B.left)
      [IsAffine T₀.left] [IsAffine T.left] (i : T₀ ⟶ T) [IsClosedImmersion i.left],
      i.left.ker ^ 2 = ⊥ →
      ∀ M₀ : RigidifiedLines (picardInfinitesimalFamily A g B T₀).e,
        FibrewiseTrivial (picardInfinitesimalFamily A g B T₀).p
          ((picardInfinitesimalFamily A g B T₀).X.smallModuleRestriction.obj
            ((rigidifiedLineForget (picardInfinitesimalFamily A g B T₀).e).obj M₀)) →
        ∃ (J : Type u) (U : J → Over B.left) (p : ∀ j : J, U j ⟶ T),
          (∀ j : J, Etale (p j).left) ∧
          (∀ x : T.left, ∃ (j : J) (y : (U j).left), (p j).left.base y = x) ∧
          ∀ j : J, ∃ M : RigidifiedLines (picardInfinitesimalFamily A g B (U j)).e,
            FibrewiseTrivial (picardInfinitesimalFamily A g B (U j)).p
              ((picardInfinitesimalFamily A g B (U j)).X.smallModuleRestriction.obj
                ((rigidifiedLineForget (picardInfinitesimalFamily A g B (U j)).e).obj M)) ∧
            ∃ wU : groupSchemeMap ((Over.map B.hom).map (Limits.pullback.snd i (p j))) ≫
                  (picardInfinitesimalFamily A g B (U j)).e =
                (picardInfinitesimalFamily A g B (Limits.pullback i (p j))).e ≫
                  picardInfinitesimalFamilyMap A g B (Limits.pullback.snd i (p j)),
            ∃ w₀ : groupSchemeMap ((Over.map B.hom).map (Limits.pullback.fst i (p j))) ≫
                  (picardInfinitesimalFamily A g B T₀).e =
                (picardInfinitesimalFamily A g B (Limits.pullback i (p j))).e ≫
                  picardInfinitesimalFamilyMap A g B (Limits.pullback.fst i (p j)),
              Nonempty
                (((rigidifiedLinePullback
                    (picardInfinitesimalFamily A g B (U j)).e
                    (picardInfinitesimalFamily A g B (Limits.pullback i (p j))).e
                    (groupSchemeMap ((Over.map B.hom).map (Limits.pullback.snd i (p j))))
                    (picardInfinitesimalFamilyMap A g B (Limits.pullback.snd i (p j))) wU).obj M) ≅
                  ((rigidifiedLinePullback
                    (picardInfinitesimalFamily A g B T₀).e
                    (picardInfinitesimalFamily A g B (Limits.pullback i (p j))).e
                    (groupSchemeMap ((Over.map B.hom).map (Limits.pullback.fst i (p j))))
                    (picardInfinitesimalFamilyMap A g B (Limits.pullback.fst i (p j)))
                    w₀).obj M₀)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
