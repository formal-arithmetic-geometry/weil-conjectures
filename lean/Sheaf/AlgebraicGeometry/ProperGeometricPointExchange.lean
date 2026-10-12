module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero

/-!
# Proper exchange over a geometric point

Source: Stacks Project, Tags 0A3T and 0A3U.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Proper exchange for base change to an algebraically closed field.

Source: Stacks Project, Tags 0A3T and 0A3U, degree-zero stalk calculation.
(blueprint: lem-weil-pbc-proper-geometric-point-exchange).

Proof: forget the module structure and compute the stalk of the direct image as the
filtered colimit of sections on pointed affine etale neighbourhoods. Continuity of
sections identifies this colimit with sections on the strict-henselian base change.
Properness is preserved by base change. The henselian degree-zero comparison identifies
these sections with sections on the closed fibre. Its residue field is separably closed;
invariance of sections under extension of a separably closed field (Tag 0A3I) identifies
these with sections on the fibre over the given algebraically closed field. On the small
etale site of the spectrum of that field, sections at the terminal object compute the
unique geometric stalk. Expanding the unit-square-counit definition of exchange shows
that a section represented on a pointed neighbourhood is sent to its restriction on the
same fibre. Consequently the actual exchange map, rather than an unspecified comparison,
is bijective on that stalk. Conservativity gives the sheaf isomorphism; the forgetful
functor from modules reflects isomorphisms. This argument needs no torsion hypothesis.
It also applies to the empty fibre, whose section module is zero. -/
theorem isIso_baseChangeMap_app_of_isProper_geometricPoint
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsProper f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) := by sorry

end AlgebraicGeometry.Etale
