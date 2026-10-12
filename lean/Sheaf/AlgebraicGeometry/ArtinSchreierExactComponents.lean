module

public import Sheaf.AlgebraicGeometry.ArtinSchreierData
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false

/-- The kernel, exactness, and epimorphism components of the Artin--Schreier sequence.
Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lem-sc-as-sequence.md.
For every etale section, the equation `x ^ p - x = 0` has precisely the constant
solutions coming from `ZMod p`; this identifies the kernel with the image of
`iota` and gives exactness. The Artin--Schreier polynomial is surjective on
the algebraically closed residue fields, and the section restriction formula
then lifts this to epimorphy of `wp`. The same constant-section calculation
shows that `iota` is monic. These three conclusions are returned as the
conjunction below. (blueprint: lem-sc-as-sequence-exact-components)
-/
theorem artinSchreier_data_exact_components
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
    (ShortComplex.mk iota wp hzero).Exact ∧
      Mono iota ∧ Epi wp := by
  sorry

end AlgebraicGeometry
