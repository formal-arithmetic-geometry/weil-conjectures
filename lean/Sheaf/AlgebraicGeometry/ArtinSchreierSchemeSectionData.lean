module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- Construction and section formulas for the Artin--Schreier maps, without exactness.
Source: Stacks Project, Tag 0A3J, opening sequence.
(blueprint: lem-sc-artin-schreier-scheme-section-data).

Proof: The pullback of the structure module along each étale U → X is canonically
its structure module. The tensor-pullback units and composition isomorphisms identify
restrictions with pullback of functions. Taking global sections and removing ULift
therefore gives natural additive equivalences a. The image of hp under U → X makes
p vanish in each section ring. The characteristic-p binomial identity makes
x ↦ x^p - x additive, and ring maps commute with it. Conjugating by a defines a
natural presheaf endomorphism, hence a sheaf morphism wp. The maps c ↦ c.val • 1
from ZMod p are additive (p = 0), commute with restrictions, and extend uniquely
from the constant presheaf through sheafification to iota. Their values satisfy
c^p = c, so the composite is zero on the sheafification unit. The universal
property of sheafification implies iota ≫ wp = 0. These constructions give all
three displayed formulas. No assertion about kernels or local preimages is used.
-/
theorem exists_artinSchreier_section_data (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) :
    let G := (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Modules.etaleTensorSectionsSheaf (Modules.unit X))
    ∃ (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
      (wp : G ⟶ G) (iota : X.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0),
      (∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
        a V (G.obj.map g x) = g.unop.left.appTop (a U x)) ∧
      (∀ (U : X.Etaleᵒᵖ) (x : G.obj.obj U),
        a U (wp.hom.app U x) = (a U x) ^ p - a U x) ∧
      (∀ (U : X.Etaleᵒᵖ) (c : ZMod p),
        a U (iota.hom.app U
          ((toSheafify X.smallEtaleTopology
            ((Functor.const X.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
          (c.val : Γ(U.unop.left, ⊤))) := by
  sorry

end AlgebraicGeometry.Scheme
