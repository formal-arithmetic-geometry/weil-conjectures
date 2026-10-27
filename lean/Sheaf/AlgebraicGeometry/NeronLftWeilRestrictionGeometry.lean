/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatAffineBasis
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Compactness.Compact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Geometry of the Weil restriction of a Néron lft-model

Source: BLR, Néron Models, 7.6 Theorem 4 and Proposition 5, pp. 194–197;
10.1 after Definition 1 and proof of Proposition 4, pp. 290–291
(blueprint: lem-sfb-neron-lft-weil-restriction-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- Pull back the universal evaluation map along an arbitrary change of base. The two
pullback-composition comparisons identify the source, and the final arrow is the pullback
of evaluation. Thus this is the specified base-change map, with no choice of a bijection.
Source: BLR 7.6, base-change formula, p. 192
(blueprint: lem-sfb-neron-lft-weil-restriction-geometry). -/
noncomputable def weilRestrictionEvaluationBaseChange
    {S S' T : Scheme.{u}} (p : S' ⟶ S) (t : T ⟶ S)
    {W : Over S} {M : Over S'} (ev : (Over.pullback p).obj W ⟶ M) :
    (Over.pullback (pullback.snd p t)).obj ((Over.pullback t).obj W) ⟶
      (Over.pullback (pullback.fst p t)).obj M :=
  (Over.pullbackComp (pullback.snd p t) t).inv.app W ≫
    (eqToIso (congrArg (fun f => (Over.pullback f).obj W)
      (pullback.condition (f := p) (g := t)).symm)).hom ≫
    (Over.pullbackComp (pullback.fst p t) p).hom.app W ≫
    (Over.pullback (pullback.fst p t)).map ev

/-- Generic evaluation is obtained from the original evaluation, the scalar-tower
commutative square, pullback pasting and the specified generic-fibre isomorphism.
Source: BLR 7.6, base-change formula, p. 192
(blueprint: lem-sfb-neron-lft-weil-restriction-geometry). -/
noncomputable def weilRestrictionGenericEvaluation
    (D D' E E' : Type u) [CommRing D] [CommRing D'] [CommRing E] [CommRing E']
    [Algebra D D'] [Algebra D E] [Algebra D' E'] [Algebra E E'] [Algebra D E']
    [IsScalarTower D D' E'] [IsScalarTower D E E']
    {W : Over (Spec (.of D))} {M : Over (Spec (.of D'))}
    {V : Over (Spec (.of E'))}
    (ev : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D D')))).obj W ⟶ M)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D' E')))).obj M ≅ V) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap E E')))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj W) ⟶ V :=
  (Over.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap E E')))
    (Spec.map (CommRingCat.ofHom (algebraMap D E)))).inv.app W ≫
    (eqToIso (congrArg (fun f => (Over.pullback f).obj W)
      ((Spec.map_comp (CommRingCat.ofHom (algebraMap D E))
        (CommRingCat.ofHom (algebraMap E E'))).symm.trans
        ((congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (fun x =>
          (IsScalarTower.algebraMap_apply D E E' x).symm.trans
            (IsScalarTower.algebraMap_apply D D' E' x))))).trans
          (Spec.map_comp (CommRingCat.ofHom (algebraMap D D'))
            (CommRingCat.ofHom (algebraMap D' E'))))))).hom ≫
    (Over.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap D' E')))
      (Spec.map (CommRingCat.ofHom (algebraMap D D')))).hom.app W ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D' E')))).map ev ≫ e.hom

/-- The union, in the total space, of the geometric identity components. A geometric
fibre uses the algebraic closure of the residue field, and the image is taken through the
first projection of the actual scheme pullback.
Source: BLR 10.1, after Definition 1, p. 290
(blueprint: lem-sfb-neron-lft-weil-restriction-geometry). -/
def neronGeometricNeutralSet {S : Scheme.{u}} (W : Grp (Over S)) : Set W.X.left :=
  {x | ∃ s : S, ∃ z :
      ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
        S.fromSpecResidueField s)).obj W.X).left,
    z ∈ connectedComponent (GrpObj.onePoint
      ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
        S.fromSpecResidueField s)).obj W.X)) ∧
    (pullback.fst W.X.hom (Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
      S.fromSpecResidueField s)) z = x}

/-- The Weil restriction exists as a smooth separated commutative group scheme. Its
universal evaluation gives the restriction bijections, and its canonical pullback gives
those bijections after every base change. The generic fibre represents the restriction of
the given generic group and is of finite type. The geometric neutral union is an open
subgroup of finite type.

Source: BLR 7.6 Theorem 4 and Proposition 5, pp. 194–197; 10.1 after Definition 1 and
proof of Proposition 4, pp. 290–291
(blueprint: lem-sfb-neron-lft-weil-restriction-geometry).

Proof:
1. Finite faithful flatness over the Noetherian Dedekind base makes Spec D' → Spec D
finite locally free, by the affine finite-flat basis and finite-free spectrum lemmas.
Localizing D' at D minus zero gives a finite-dimensional domain over E, hence the field E'.
Thus the generic base change of Spec D' is Spec E'.
2. The finite-set affine-neighbourhood lemma for Néron lft-models and the Weil restriction
representability criterion construct W. The geometric-properties lemma gives smoothness,
separatedness and local finite type.
3. Transport pointwise multiplication, identity and inversion through the natural
bijections. Yoneda produces their scheme morphisms and proves the commutative group laws.
Equivalently evaluation is a group homomorphism and its induced maps are bijective.
4. Pullback pasting identifies the two base-changed Hom functors. This gives the canonical
base-change evaluation above and its bijectivity. On the generic fibre the identification
with V gives its restriction functor; geometric-properties preservation gives finite type.
5. Apply the Néron mapping property of M to Y ×_S S', for Y smooth over S. The restriction
bijections and their generic versions show that W is a Néron lft-model of its generic fibre.
6. The neutral affine-product-chart lemma makes the geometric neutral union an open
subgroup and gives, locally on the base, a surjection U × U onto that subgroup with U affine.
7. Each such image is quasi-compact. Finitely many affine base neighbourhoods cover Spec D,
so the neutral subgroup is quasi-compact. It is open in a locally finite type scheme, hence
locally finite type; together these give finite type. -/
theorem exists_neronLft_weilRestriction_geometry
    (D D' E E' : Type u) [CommRing D] [CommRing D']
    [IsDedekindDomain D] [IsDedekindDomain D']
    (_dimD : ringKrullDim D = 1) (_dimD' : ringKrullDim D' = 1)
    [Algebra D D'] [Module.Finite D D'] [Module.FaithfullyFlat D D']
    [Field E] [Field E'] [Algebra D E] [IsFractionRing D E]
    [Algebra D' E'] [IsFractionRing D' E']
    [Algebra E E'] [Algebra D E'] [IsScalarTower D D' E'] [IsScalarTower D E E']
    (V : Grp (Over (Spec (.of E')))) [IsCommMonObj V.X]
    [Smooth V.X.hom] [IsSeparated V.X.hom]
    [LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]
    (M : Grp (Over (Spec (.of D'))))
    [Smooth M.X.hom] [IsSeparated M.X.hom]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D' E')))).obj M.X ≅ V.X)
    [IsMonHom e.hom]
    (_neron : ∀ Y : Over (Spec (.of D')), Smooth Y.hom →
      Function.Bijective (fun f : Y ⟶ M.X =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D' E')))).map f ≫ e.hom)) :
    ∃ W : Grp (Over (Spec (.of D))), IsCommMonObj W.X ∧
      Smooth W.X.hom ∧ IsSeparated W.X.hom ∧ LocallyOfFiniteType W.X.hom ∧
      ∃ ev : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D D')))).obj W.X ⟶ M.X,
        IsMonHom ev ∧
        (∀ X : Over (Spec (.of D)), Function.Bijective (fun f : X ⟶ W.X =>
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D D')))).map f ≫ ev)) ∧
        (∀ (T : Scheme.{u}) (t : T ⟶ Spec (.of D)) (X : Over T),
          Function.Bijective (fun f : X ⟶ (Over.pullback t).obj W.X =>
            (Over.pullback (pullback.snd
              (Spec.map (CommRingCat.ofHom (algebraMap D D'))) t)).map f ≫
            weilRestrictionEvaluationBaseChange
              (Spec.map (CommRingCat.ofHom (algebraMap D D'))) t ev)) ∧
        LocallyOfFiniteType
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj W.X).hom ∧
        QuasiCompact
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj W.X).hom ∧
        (∀ X : Over (Spec (.of E)), Function.Bijective (fun f : X ⟶
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj W.X =>
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap E E')))).map f ≫
          weilRestrictionGenericEvaluation D D' E E' ev e)) ∧
        ∃ (W₀ : Grp (Over (Spec (.of D)))) (i : W₀.X ⟶ W.X),
          IsMonHom i ∧ IsOpenImmersion i.left ∧
          Set.range i.left.base = neronGeometricNeutralSet W ∧
          LocallyOfFiniteType W₀.X.hom ∧ QuasiCompact W₀.X.hom := by
  sorry

end AlgebraicGeometry
