/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Homeomorph.Defs
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation

/-! # Algebraic-space pushouts along thickenings and affine maps

Source: Stacks Project, spaces-pushouts.tex, Tags 07VX, 07SY and 07W0
(blueprint: lem-sfb-space-affine-thickening-pushout).

The three statements give existence with a thickening inclusion, agreement with scheme
pushouts, and recovery of arbitrary compatible spaces. Cartesian squares express that the
canonical comparison maps are isomorphisms. The specified overlap is retained in the
pushout equation. No flatness, finite presentation, or finite nilpotence bound is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pushouts of an affine map and a thickening exist in algebraic spaces. The map from
`S` to the pushout is again a representable closed immersion and a homeomorphism on
point spaces, endowed with their existing atlas quotient topologies.
Source: Stacks, Tag 07VX (blueprint: lem-sfb-space-affine-thickening-pushout).

Proof: (1) Use lem-sfb-infinitesimal-pushout-affine-charts for scheme recovery.
(2) The scheme-colimit upgrade, scheme affine-thickening pushout, and scheme infinitesimal
etale-patching nodes imply that scheme pushouts also have algebraic-space targets.
(3) Choose an etale scheme atlas V of S. Its affine pullback U to T is a scheme.
Lift U to an etale scheme U+ over T+ using the space-thickening etale scheme equivalence.
The two thickenings identify point sets, so U+ is surjective. Form V+ = V amalg_U U+.
(4) Form the analogous scheme pushout R+ of the three atlas kernel relations.
Etale patching gives its two etale projections to V+, with the specified restrictions.
(5) Glue the identities and flips. The domain of composition is etale over V+; the etale
patching counit writes it as the pushout of the two composition domains. Glue composition
and verify source and target equations by uniqueness on both pieces.
(6) Field-valued points of a thickening factor uniquely through its closed restriction.
Thus the geometric relation is the original atlas kernel equivalence relation. The
unramified-geometric-equivalence-relation node makes R+ an equivalence relation; apply
lem-trf-etale-relation-quotient to form P = V+/R+.
(7) Descend the maps from S and T+ using lem-a1-etale-atlas-presentation. The cartesian
relation identifications give S times_P V+ = V and T+ times_P V+ = U+ by etale-local
lifting and uniqueness of sections.
(8) The space-closed-immersion-atlas-locality node descends the scheme closed immersion
V into V+. The homeomorphisms on atlas and relation point spaces identify their quotient
topologies, proving the thickening assertion.
(9) A compatible pair of maps to Q gives a unique map V+ to Q by (2). Its restrictions
agree on R+, so the quotient coequalizer gives the unique map P to Q. -/
theorem exists_affineThickeningPushout {B : Scheme.{u}}
    (T T' S : AlgebraicSpace B) (i : T ⟶ T') (a : T ⟶ S)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hiTop : IsHomeomorph (mapPoint i.hom.hom))
    (ha : IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom) :
    ∃ (P : AlgebraicSpace B) (j : S ⟶ P) (b : T' ⟶ P),
      IsPushout a i j b ∧
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) j.hom.hom ∧
      IsHomeomorph (mapPoint j.hom.hom) := by
  sorry

/-- For schemes, the pushout can be taken to be a scheme pushout, which is also a
pushout against all algebraic-space targets. Uniqueness identifies the two pushouts.
Source: Stacks, Tag 07SY (blueprint: lem-sfb-space-affine-thickening-pushout).

Proof: first obtain the scheme pushout from lem-sfb-scheme-affine-thickening-pushout.
Apply lem-sfb-scheme-colimit-upgrade-space-targets to the finite span.
The scheme-affine-thickening-pushout node makes the two inclusions jointly surjective,
since the inclusion from S is a homeomorphism. The etale patching counit in
lem-sfb-scheme-infinitesimal-etale-patching identifies every etale scheme over the pushout
with the pushout of its restrictions. Its equivalence also lifts every compatible etale
triple, including those with separated structure maps. These are precisely the colimit
upgrade hypotheses. This is step (2) of the node's proof and the scheme clause of (9). -/
theorem scheme_affineThickeningPushout {B : Scheme.{u}}
    (T T' S : Over B) (i : T ⟶ T') (a : T ⟶ S)
    [IsClosedImmersion i.left] (hi : IsHomeomorph i.left.base)
    [IsAffineHom a.left] :
    ∃ (P : Over B) (j : S ⟶ P) (b : T' ⟶ P),
      IsPushout a.left i.left j.left b.left ∧
      IsPushout
      (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map a) :
        schemeSpace T ⟶ schemeSpace S)
      (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map i) :
        schemeSpace T ⟶ schemeSpace T')
      (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map j) :
        schemeSpace S ⟶ schemeSpace P)
      (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map b) :
        schemeSpace T' ⟶ schemeSpace P) := by
  sorry

/-- Arbitrary compatible algebraic spaces are recovered from their pushout by the two
canonical comparison maps. The isomorphism `φ` is over `T`, as expressed by `hφ`.
The pushout equation on its overlap forces the recovered restrictions to agree by this
very `φ`. No flatness or local finite presentation is required.
Source: Stacks, Tag 07W0 (blueprint: lem-sfb-space-affine-thickening-pushout).

Proof: (10) For the specified X, Y and phi, the overlap maps to Y by a thickening and
to X by an affine map, by base change. Apply the existence construction (3)--(9) already
proved, and its universal property gives Z to P.
(11) Choose a scheme atlas X1 over X times_S V. Its overlap U1 is affine over X1.
Lift U1 to an etale scheme Y1 over Y times_T+ U+ by the space-thickening etale scheme
equivalence; surjectivity again follows on point sets. Use this precise atlas and lift
in the construction of Z. Their scheme pushout W1 is a surjective etale atlas of Z,
with X times_Z W1 = X1 and Y times_Z W1 = Y1. The induced maps W1 to V+ and P agree
by uniqueness on the two pieces.
(12) Pull the two comparison maps back along W1 to Z. The atlas cube identifies their
targets with W1 times_V+ V and W1 times_V+ U+. Scheme recovery from
lem-sfb-infinitesimal-pushout-affine-charts identifies these with X1 and Y1 by the
canonical comparisons. The local inverses glue uniquely by the algebraic-space sheaf
axiom, so both original comparisons are isomorphisms.
(13) Their defining inclusions into Z agree on the overlap after phi by the pushout
equation. Hence the recovered restrictions identify by the specified phi itself. -/
theorem affineThickeningPushout_recovery {B : Scheme.{u}}
    (T T' S P : AlgebraicSpace B) (i : T ⟶ T') (a : T ⟶ S)
    (j : S ⟶ P) (b : T' ⟶ P)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hiTop : IsHomeomorph (mapPoint i.hom.hom))
    (ha : IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom)
    (hp : IsPushout a i j b)
    (X Y : AlgebraicSpace B) (x : X ⟶ S) (y : Y ⟶ T')
    (φ : enlargedFibreProduct x a ≅ enlargedFibreProduct y i)
    (hφ : φ.hom.hom ≫ Limits.pullback.snd y.hom i.hom =
      Limits.pullback.snd x.hom a.hom) :
    ∃ (Z : AlgebraicSpace B) (u : X ⟶ Z) (v : Y ⟶ Z) (p : Z ⟶ P),
      IsPushout (enlargedFibreProductFst x a)
        (φ.hom ≫ enlargedFibreProductFst y i) u v ∧
      IsPullback u x p j ∧ IsPullback v y p b := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
