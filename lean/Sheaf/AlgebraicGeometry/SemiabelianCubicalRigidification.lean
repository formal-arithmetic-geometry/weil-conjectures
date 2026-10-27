/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.RelativePicardCubeFaceDetection
import Sheaf.AlgebraicGeometry.RelativeGroupUnitAxisFactorization

/-! # Canonical cubical structures on rigidified lines

Source: Moret-Bailly, Pinceaux de varietes abeliennes, I 2.6; cross-check:
Lan, revised thesis, Proposition 3.2.3.1, cases (1) and (2).
(blueprint: lem-sfb-semiabelian-cubical-rigidification)

The existence and uniqueness theorem supplies the canonical section. Its choice is
uniquely determined, and the remaining statements express the isomorphism, homomorphism,
and base-restriction clauses using the recorded termwise pullbacks.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
namespace CubicalRigidifiedLine

/-- A rigidified line has exactly one normalized symmetric cube section satisfying the
cocycle, for an abelian scheme or a group with semiabelian geometric fibres over a normal base.
The identity-slice normalization in `Compatible` is independent of the scale of `r`, since
its occurrences cancel in pairs in the eight-factor cube.

Source: Moret-Bailly I 2.6; Lan Proposition 3.2.3.1 (1), (2)
(blueprint: lem-sfb-semiabelian-cubical-rigidification).

Proof (steps 1--4 of the node):
1. Pair opposite signed factors on each identity face of Theta_3(L). Evaluation and r
   give agreeing face trivializations. Apply lem-sfb-relative-picard-cube-face-detection
   to the triple (G,G,G) to obtain a nowhere-vanishing section t.
2. Let f_i be its ratio to the prescribed face section, f_ij the common restrictions
   on double faces, and f_123 its restriction to the identity. Multiply t by
   f_1^-1 f_2^-1 f_3^-1 f_12 f_13 f_23 f_123^-1, pulled back by the coordinate projections.
   Restriction to each face cancels every factor, giving the prescribed normalization.
3. The ratio of any two normalized sections is a unit trivial on the identity axes.
   Apply lem-sfb-relative-group-unit-axis-factorization for n=3 to make it one.
   The proper alternative applies directly; in the other alternative a normal base is reduced.
4. Permuting the coordinates preserves the face normalization, hence the section by
   uniqueness. Expand the four Theta_3 factors in the cocycle and cancel equal line
   factors. The quotient is a unit on G^4 trivial on each identity axis. The same
   factorization for n=4 makes it one, proving the cocycle and existence. -/
theorem existsUnique_compatible {S : Scheme.{u}} (G : Over S) [CommGrpObj G]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom]
    [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (hbase : IsProper G.hom ∨
      ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) ∧
        HasSemiabelianGeometricFibres (Grp.mk G)))
    (L : G.left.Modules) (hL : L.IsInvertible)
    (r : (Scheme.Modules.tensorPullback (η[G]).left).obj L ≅ 𝟙_ S.Modules) :
    ∃! τ : 𝟙_ (CubicalLine.cube G).left.Modules ≅ CubicalLine.theta G L,
      CubicalLine.Compatible τ := by
  sorry

/-- The unique compatible cube section. Only the existence-and-uniqueness proof is postponed;
the choice theorem determines the section up to equality.
Source: Moret-Bailly I 2.6; Lan Proposition 3.2.3.1
(blueprint: lem-sfb-semiabelian-cubical-rigidification). -/
noncomputable def canonicalSection {S : Scheme.{u}} (G : Over S) [CommGrpObj G]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom]
    [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (hbase : IsProper G.hom ∨
      ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) ∧
        HasSemiabelianGeometricFibres (Grp.mk G)))
    (L : G.left.Modules) (hL : L.IsInvertible)
    (r : (Scheme.Modules.tensorPullback (η[G]).left).obj L ≅ 𝟙_ S.Modules) :
    𝟙_ (CubicalLine.cube G).left.Modules ≅ CubicalLine.theta G L :=
  Classical.choose (existsUnique_compatible G hbase L hL r).exists

/-- Equip the specified line and rigidification with their unique cubical structure.
Source: Moret-Bailly I 2.6; Lan Proposition 3.2.3.1
(blueprint: lem-sfb-semiabelian-cubical-rigidification). -/
noncomputable def canonical {S : Scheme.{u}} (G : Over S) [CommGrpObj G]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom]
    [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (hbase : IsProper G.hom ∨
      ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) ∧
        HasSemiabelianGeometricFibres (Grp.mk G)))
    (L : G.left.Modules) (hL : L.IsInvertible)
    (r : (Scheme.Modules.tensorPullback (η[G]).left).obj L ≅ 𝟙_ S.Modules) :
    CubicalRigidifiedLine G where
  line := L
  invertible := hL
  rigidification := r
  sectionIso := canonicalSection G hbase L hL r
  compatible := Classical.choose_spec (existsUnique_compatible G hbase L hL r).exists

/-- Every rigidification-preserving line isomorphism preserves the unique cube sections.
Source: Moret-Bailly I 2.6; Lan Proposition 3.2.3.1
(blueprint: lem-sfb-semiabelian-cubical-rigidification).
Proof (step 5): apply the eight-factor map to the first section. Evaluation on every
identity face commutes with the line isomorphism and the supplied rigidification equality.
The ratio to the second section is therefore an axis-trivial unit. Step 3, using
lem-sfb-relative-group-unit-axis-factorization for n=3, makes the ratio one. -/
theorem iso_preserves_cube {S : Scheme.{u}} (G : Over S) [CommGrpObj G]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom]
    [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (hbase : IsProper G.hom ∨
      ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) ∧
        HasSemiabelianGeometricFibres (Grp.mk G)))
    (L M : CubicalRigidifiedLine G) (f : L.line ≅ M.line)
    (hr : (Scheme.Modules.tensorPullback (η[G]).left).mapIso f ≪≫ M.rigidification =
      L.rigidification) :
    L.sectionIso ≪≫ (CubicalLine.thetaWord G).mapIso f = M.sectionIso := by
  sorry

/-- The canonical structure commutes with pullback by group-scheme homomorphisms when both
source and target satisfy the stated proper or normal-semiabelian alternatives.
Source: Moret-Bailly I 2.6; Lan Proposition 3.2.3.1
(blueprint: lem-sfb-semiabelian-cubical-rigidification).
Proof (step 6): pullback carries the partial sums and identity to the corresponding maps.
The canonical tensor pullback preserves evaluation, so the pulled-back section satisfies
normalization, symmetry and the cocycle, as expressed by CubicalLine.pullback_properties.
The existence-and-uniqueness assertion for the source group identifies this section
with its canonical section. The line and rigidification are the actual pullback data,
so their equality and proof irrelevance give the displayed equality of cubical lines.
Identity and iterated pullbacks follow by the same uniqueness and the normalized compositors. -/
theorem pullback_eq_canonical {S : Scheme.{u}} (G G' : Over S)
    [CommGrpObj G] [CommGrpObj G']
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom]
    [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    [Smooth G'.hom] [IsSeparated G'.hom] [LocallyOfFinitePresentation G'.hom]
    [QuasiCompact G'.hom] [GeometricallyConnected G'.hom]
    (hbase : IsProper G.hom ∨
      ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) ∧
        HasSemiabelianGeometricFibres (Grp.mk G)))
    (hbase' : IsProper G'.hom ∨
      ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) ∧
        HasSemiabelianGeometricFibres (Grp.mk G')))
    (h : G' ⟶ G) [IsMonHom h] (L : CubicalRigidifiedLine G) :
    L.pullback h = canonical G' hbase' (L.pullback h).line
      (L.pullback h).invertible (L.pullback h).rigidification := by
  sorry

/-- Restriction to a subscheme commutes with the canonical cubical structure whenever the
restricted group satisfies one of the two alternatives as well.
Source: Moret-Bailly I 2.6; Lan Proposition 3.2.3.1
(blueprint: lem-sfb-semiabelian-cubical-rigidification).
Proof (step 6): the fibre-product projection preserves all partial sums and the identity.
Termwise tensor pullback preserves the face pairings, permutation equality and cocycle
(CubicalLine.baseChange_preservesSums and CubicalLine.pullback_properties). Uniqueness for
the restricted group makes its canonical section equal to the pulled-back section;
the line and rigidification agree by construction. This includes the identity restriction
and iterated restrictions through the normalized tensor composition comparisons. -/
theorem baseChange_eq_canonical {S S' : Scheme.{u}} (g : S' ⟶ S) [IsImmersion g]
    (G : Over S) [CommGrpObj G]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom]
    [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    [Smooth (CubicalLine.baseChangedGroup g G).hom]
    [IsSeparated (CubicalLine.baseChangedGroup g G).hom]
    [LocallyOfFinitePresentation (CubicalLine.baseChangedGroup g G).hom]
    [QuasiCompact (CubicalLine.baseChangedGroup g G).hom]
    [GeometricallyConnected (CubicalLine.baseChangedGroup g G).hom]
    (hbase : IsProper G.hom ∨
      ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) ∧
        HasSemiabelianGeometricFibres (Grp.mk G)))
    (hbase' : IsProper (CubicalLine.baseChangedGroup g G).hom ∨
      ((∀ x : S', IsDomain (S'.presheaf.stalk x) ∧ IsIntegrallyClosed (S'.presheaf.stalk x)) ∧
        HasSemiabelianGeometricFibres (Grp.mk (CubicalLine.baseChangedGroup g G))))
    (L : CubicalRigidifiedLine G) :
    L.baseChange g = canonical (CubicalLine.baseChangedGroup g G) hbase'
      (L.baseChange g).line (L.baseChange g).invertible (L.baseChange g).rigidification := by
  sorry

end CubicalRigidifiedLine
end AlgebraicGeometry
