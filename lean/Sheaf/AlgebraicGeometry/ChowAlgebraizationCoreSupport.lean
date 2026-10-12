module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Proper support for the algebraization candidate. Source: Stacks Project, Theorem 088E,
support paragraphs (blueprint: new-chow-algebraization-core-support).
The support calculation in the compactification identifies the support of the candidate
with the proper closed support transported from the degree-zero pullback. -/
theorem chow_algebraization_candidate_support
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : Z.IdealSheafData)
    (hQ : Q = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (Y : Scheme.{u}) (q : Y ⟶ Z) [IsProper q]
    (F : CoherentModules Y)
    (hF : Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
      formalCompletionSystem (Q.comap q) F.obj)) :
    Scheme.Modules.HasSupportProperOver (q ≫ f) F.obj := by
  sorry

end AlgebraicGeometry
