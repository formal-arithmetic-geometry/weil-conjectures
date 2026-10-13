module

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.StrictPerfectStalkFiberData
import Sheaf.AlgebraicGeometry.BoundedFreeStalkModelSpread
import Sheaf.RingTheory.MinimalFreeModel

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Spread a minimal finite free model from the local ring of a strictly perfect
neighbourhood, using the already known finite residue cohomology and its bounded support.
Source: Stacks Project, More on Algebra, Tags 0BCD, 0BCC, 0BC7; Derived Categories of
Schemes, Tags 08EB and 09RE.
(blueprint: lem-sc-perfect-finite-free-residue-model-existence).

Proof:
1. Choose a complex G representing E using essential surjectivity of the derived
   localization. Take its stalk complex C. The exact stalk/fibre comparison
   strictPerfect_stalk_fiberData makes Q(C) pseudo-coherent and identifies the
   finite residue cohomology and its dimensions with the given fibre data.
2. Apply exists_unique_minimalFreeModel over O_X,x, with d i = derivedFiberBetti X E i x.
   The upper bound in hbound gives the required bounded-above rank support.
3. The resulting model F has terms isomorphic to O_X,x^(d i). For every i outside
   the two bounds in hbound, d i = 0. Its displayed free module is therefore a zero
   object, and transporting along the termwise isomorphism makes F.X i zero.
   Hence F is bounded, using precisely the bounds from hbound.
4. Apply spread_boundedFree_stalkModel to this given bounded stalk model, its ranks
   and its derived isomorphism with C. This supplies the affine neighbourhood and
   the bounded free sheaf complex with the required ranks and derived comparison. -/
theorem finiteFreeModel_of_fiberData
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P))
    (hfin : ∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x))
    (hbound : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → derivedFiberBetti X E i x = 0) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U)
          (ULift.{u} (Fin (derivedFiberBetti X E i x))))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj K) := by
  let R := X.presheaf.stalk x
  let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let G := DerivedCategory.Q.objPreimage E
  let eG : DerivedCategory.Q.obj G ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let C := ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj G
  obtain ⟨hC, hfinite, hd⟩ := strictPerfect_stalk_fiberData X E x G eG hlocal hfin
  obtain ⟨a, b, hbounds⟩ := hbound
  have hup : ∃ b : ℤ, ∀ i : ℤ, b < i → derivedFiberBetti X E i x = 0 :=
    ⟨b, fun i hi => hbounds i (Or.inr hi)⟩
  obtain ⟨F, _, ⟨eF⟩, hfree, _⟩ :=
    DerivedCategory.exists_unique_minimalFreeModel.{u, 0, u + 1}
      (DerivedCategory.Q.obj C) hC (fun i => derivedFiberBetti X E i x) hfinite hd hup
  have hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i) := by
    refine ⟨a, b, ?_⟩
    intro i hi
    obtain ⟨ei⟩ := hfree i
    rw [hbounds i hi] at ei
    exact (ModuleCat.isZero_of_subsingleton _).of_iso ei
  exact spread_boundedFree_stalkModel X E x G eG hlocal
    (fun i => derivedFiberBetti X E i x) F hbounded hfree eF

end
end AlgebraicGeometry.Scheme
