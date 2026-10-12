module

public import Sheaf.AlgebraicGeometry.ArtinSchreierData
import Sheaf.AlgebraicGeometry.ArtinSchreierExactComponents
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false

/-- Exactness of the sectionwise Artin--Schreier data.
Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lem-sc-as-sequence.md,
node `lem-sc-as-sequence` (blueprint: lem-sc-as-sequence).

This is the kernel and epimorphism part of the Artin--Schreier argument; the
construction and section formulas are supplied as hypotheses by `artinSchreier_data`.
(blueprint: lem-sc-as-sequence-exact)

Proof: the source proof gives the corresponding construction or exactness portion.
The complementary portion is isolated in the companion theorem.
-/
theorem artinSchreier_data_shortExact
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : G ≅ (sheafCompose C.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)))
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G) (iota : C.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0)
    (hrestr : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x)
    (hiota : ∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
      a U (iota.hom.app U
        ((toSheafify C.smallEtaleTopology
          ((Functor.const C.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤))) :
    ShortComplex.ShortExact (ShortComplex.mk iota wp hzero) := by
  obtain ⟨hex, hmono, hepi⟩ := artinSchreier_data_exact_components f p hp G hG a wp iota
    hzero hrestr hwp hiota
  exact ShortComplex.ShortExact.mk' hex hmono hepi

end AlgebraicGeometry
