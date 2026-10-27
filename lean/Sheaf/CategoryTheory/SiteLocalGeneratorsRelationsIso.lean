module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.SheafPrecomposition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Local generators and relations for abelian inverse image

Source: `WeilConjectures/CategoryTheory/Sites/PullbackIsoOfLocallyGenerated.lean`,
`isIso_homEquiv_symm_of_locally_generated`, in its abelian-sheaf form
(blueprint: lem-sf-site-local-generators-relations-iso).

Site object and arrow universes are independent. Section groups lie in a universe
containing both sites, so their category lies in the next universe. In particular,
site objects in `Type (u + 1)` and arrows in `Type u` allow section groups in
`Type (u + 1)`, as required for the small pro-étale sites.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uD vD w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Local generators and local zero relations identify an adjoint inverse image.

Source: `WeilConjectures/CategoryTheory/Sites/PullbackIsoOfLocallyGenerated.lean`,
lines 52–71 and 244–284, specialized to abelian sheaves while assuming only preservation
of abelian sheaves by precomposition
(blueprint: lem-sf-site-local-generators-relations-iso).

Proof: fix an abelian sheaf H and a map ψ : F → P_* H. First, a zero relation in G
has zero image in H: apply the local relation hypothesis, naturality of ψ, and
separatedness of H (lem-weil-pbc-algebraic-sheaf-iff-underlying-sets).
Second, use V₁ × V₂ and its preserved product to lift two presentations to one
object; their difference is a zero relation. Thus equal presentations give equal
H-sections, also after restriction. Third, choose local presentations of s in G(U).
The proposed H-sections agree on intersections by the second step, so the sheaf
equalizer glues them uniquely. Fourth, pull back the presentation cover along
any map T → U: separatedness gives the formula for the glued section on every
presentation and independence of the choices. Fifth, refine two presentation
covers to their common cover; the preserved product and addition of the two
pulled-back F-sections show that the glued maps are additive. Their value at zero
is zero by cancellation. Sixth, apply the presentation formula after restriction
twice and use separatedness to obtain naturality, hence a sheaf morphism G → H.
Seventh, the identity presentation shows its composite with η is ψ; generation
and separatedness show uniqueness. Finally, the adjunction identifies this
bijection with precomposition by α : L F → G. At H = L F it gives β with α ≫ β = 𝟙;
at H = G injectivity gives β ≫ α = 𝟙. Thus α is an isomorphism.
-/
theorem isIso_homEquiv_symm_of_abelian_local_generators_relations
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (J : Precoverage C) (K : Precoverage D)
    (_hJ : J.IsSiteForCoverings) (_hK : K.IsSiteForCoverings)
    (P : C ⥤ D) [HasBinaryProducts C]
    [PreservesLimitsOfShape (Discrete WalkingPair) P]
    (hP : ∀ H : Sheaf K.toGrothendieck AddCommGrpCat.{max uC vC uD vD w},
      Presheaf.IsSheaf J.toGrothendieck (P.op ⋙ H.obj))
    (L : Sheaf J.toGrothendieck AddCommGrpCat.{max uC vC uD vD w} ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{max uC vC uD vD w})
    (adj : L ⊣ Sheaf.precompositionOfSheafPreservation P hP)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max uC vC uD vD w})
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{max uC vC uD vD w})
    (η : F ⟶ (Sheaf.precompositionOfSheafPreservation P hP).obj G)
    (_hgen : ∀ (U : D) (s : G.obj.obj (op U)),
      ∃ (I : Type (max uD vD)) (U' : I → D) (v : ∀ i, U' i ⟶ U),
        Presieve.ofArrows U' v ∈ K U ∧
        ∀ i, ∃ (V : C) (t : F.obj.obj (op V)) (φ : U' i ⟶ P.obj V),
          G.obj.map (v i).op s = G.obj.map φ.op (η.hom.app (op V) t))
    (_hrel : ∀ (V : C) (t : F.obj.obj (op V)) (U : D) (φ : U ⟶ P.obj V),
      G.obj.map φ.op (η.hom.app (op V) t) = 0 →
      ∃ (I : Type (max uD vD)) (U' : I → D) (v : ∀ i, U' i ⟶ U),
        Presieve.ofArrows U' v ∈ K U ∧
        ∀ i, ∃ (V' : C) (a : V' ⟶ V) (φ' : U' i ⟶ P.obj V'),
          F.obj.map a.op t = 0 ∧ φ' ≫ P.map a = v i ≫ φ) :
    IsIso ((adj.homEquiv F G).symm η) := by
  sorry

end CategoryTheory
