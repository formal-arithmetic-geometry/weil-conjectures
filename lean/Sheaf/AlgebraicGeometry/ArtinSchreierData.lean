module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent
import Sheaf.RingTheory.LocalRing.ArtinSchreierKernel
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false

/-- The sectionwise data for the Artin--Schreier sequence.
Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lem-sc-as-sequence.md,
node `lem-sc-as-sequence` (blueprint: lem-sc-as-sequence).

This is the construction part of the Artin--Schreier argument: the sheaf, its
section identifications, the two maps, their zero composite, and the formulas
on sections. The exactness assertion is separated into the companion theorem.
(blueprint: lem-sc-as-sequence-data)

Proof: the source proof gives the corresponding construction or exactness portion.
The complementary portion is isolated in the companion theorem.
-/
theorem artinSchreier_data
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∃ (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (_ : G ≅ (sheafCompose C.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)))
      (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
      (wp : G ⟶ G) (iota : C.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0),
      (∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
        a V (G.obj.map g x) = g.unop.left.appTop (a U x)) ∧
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a U (wp.hom.app U x) = (a U x) ^ p - a U x) ∧
      (∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
        a U (iota.hom.app U
          ((toSheafify C.smallEtaleTopology
            ((Functor.const C.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
          (c.val : Γ(U.unop.left, ⊤))) := by
  sorry

end AlgebraicGeometry
