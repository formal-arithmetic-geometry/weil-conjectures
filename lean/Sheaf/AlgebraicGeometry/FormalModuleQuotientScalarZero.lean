module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.IdealModuleProductStalk

@[expose] public section

universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- A scalar from the nth power of the base ideal kills every section of F/J^nF.
Source: Stacks Project, Tag 02OC, construction of the comparison maps;
Modules, Tags 01AG and 01CB, stalks of products and quotients.
(blueprint: lem-weil-pbc-formal-module-quotient-scalar-zero).

Proof: At a point z, let K be the image of J_z in O_{X,z}. The germ of the
image of a base scalar in I lies in K by the definition of the extended ideal.
The ring map from A to O_{X,z} therefore sends I^n into K^n. Exactness of
stalks and compatibility with tensor products identify (F/J^nF)_z with
F_z/(K^n F_z), on which every element of K^n acts by zero. The germ of the
claimed scalar multiple is consequently zero at every point of U. A section
of a sheaf with all germs zero is zero, giving the result. When n = 0,
J^0 = O_X and the multiplication image is F, so the quotient itself is zero.
The argument also covers I = 0, the unit ideal, F = 0 and the empty scheme;
it uses no coherence, properness or Noetherian assumption. -/
theorem formalModuleQuotient_scalar_zero {A : Type v} [CommRing A]
    (I : Ideal A) {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (n : ℕ) (a : A) (ha : a ∈ I ^ n)
    (U : X.Opens) (t : (formalModuleQuotient J n F).val.obj (op U)) :
    (X.presheaf.map (homOfLE (le_top (a := U))).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom a) • t = 0 := by
  sorry

end AlgebraicGeometry
