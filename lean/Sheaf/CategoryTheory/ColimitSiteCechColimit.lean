module

public import Sheaf.CategoryTheory.ColimitSites
public import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.CategoryTheory.ColimitSiteCechCoconeConstruction
import Sheaf.CategoryTheory.ColimitSiteFiniteProductSections
import Mathlib.Algebra.Homology.HomologicalComplexLimits

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Construct the stagewise complex diagram and its canonical colimit cocone.
Source: Stacks Project, Sites, Tags 09YM and 09YN; Cohomology on Sites, proof of 09YP.
(blueprint: lem-weil-pbc-colimit-of-sites-cech-complex-colimit-data).

Proof: for `a : Under i`, use `S.complex` with the stage presheaf pulled back along
`F.map a.hom`. For a map `b : a ⟶ a'`, apply `θ` at each chosen product, using the
under-category triangle and functor composition to identify the endpoints. Naturality
of `θ` commutes with the restriction along each face map; additivity commutes with
the signs and sums. Thus these degree maps are chain maps. `hθid` and `hθcomp`, applied
to each factor, give the diagram identity and composition laws. Take these as `D`,
with the identity identifications `eD`; their projections are exactly the first
specified arrow equations. Use `S.complex` of the restriction of `c.pt` as the cocone
point, with `eK` the identity. Its coprojections are the products of `β` followed by
the coprojections of `c`. Their naturality gives chain maps, and the compatibility
hypothesis for `H`, followed by cocone naturality of `c`, gives the cocone equations.
Their projections give exactly the second specified arrow equations.

For each chosen product `X = S.W p t`, apply the section formula of 09YN: the colimit
over arrows out of `i` of `(G a.right)(F.map a.hom X)` maps isomorphically to
`c.pt(V.ι.app i X)` by the units `β` and the coprojections of `c`. More explicitly,
09YM computes each inverse image by sections at later stages; insert this formula
into the sectionwise colimit of `H` and interchange the two filtered colimits. The
diagonal refinement is final, using filteredness, and gives the displayed stage
section diagram. Finite coverings permit computation of the sheaf colimit on
sections: filtered colimits commute with the finite sheaf equalizer diagrams.
The covering formula `hQ` and `hfinite` ensure the colimit site also has finite
coverings. This is the argument of 09YN, now with additive maps. In degree `p`, the
index set `Fin (p + 1) → T` is finite, so filtered colimits commute with its product
of abelian groups. Consequently the specified cocone in each degree is colimiting.
For any cocone of complexes, its degreewise mediating maps are unique. They commute
with the differentials because both composites agree after every coprojection;
hence they assemble to the unique mediating chain map. This proves `IsColimit K`.
For an empty covering all degrees are the zero group, and the same product argument
uses the empty product. Degree zero uses the given original objects `S.W_zero`.
-/
theorem colimitSite_cech_complex_colimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cat.{u, u}) (P : ∀ j, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange] [Q.HasPullbacks]
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    [∀ j, (V.ι.app j).toFunctor.IsContinuous (P j).toGrothendieck Q.toGrothendieck]
    (G : ∀ j, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (j k : J) (a : j ⟶ k),
      (G j).obj ⟶ (F.map a).toFunctor.op ⋙ (G k).obj)
    (hθid : ∀ (j : J) (X : F.obj j),
      Arrow.mk ((θ j j (𝟙 j)).app (op X)) = Arrow.mk (𝟙 ((G j).obj.obj (op X))))
    (hθcomp : ∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) (X : F.obj j),
      Arrow.mk ((θ j l (a ≫ b)).app (op X)) =
        Arrow.mk ((θ j k a).app (op X) ≫
          (θ k l b).app (op ((F.map a).toFunctor.obj X))))
    (H : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (E : ∀ j, H.obj j ≅
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (G j)) :
    let β := fun (j : J) (X : F.obj j) ↦
      (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).unit.app (G j)).hom.app (op X)) ≫
        (E j).inv.hom.app (op ((V.ι.app j).toFunctor.obj X))
    (∀ (j k : J) (a : j ⟶ k) (X : F.obj j),
      Arrow.mk (β j X ≫ (H.map a).hom.app (op ((V.ι.app j).toFunctor.obj X))) =
        Arrow.mk ((θ j k a).app (op X) ≫ β k ((F.map a).toFunctor.obj X))) →
    ∀ (c : Cocone H), IsColimit c →
    ∀ (i : J) {T : Type u} [Finite T] {U : F.obj i}
      (f : T → F.obj i) (hom : ∀ t, f t ⟶ U),
      Presieve.ofArrows f hom ∈ P i U →
    ∀ S : SiteCechComplex f hom,
      ∃ (D : Under i ⥤ CochainComplex AddCommGrpCat.{u} ℕ)
        (eD : ∀ a : Under i, D.obj a ≅
          S.complex ((F.map a.hom).toFunctor.op ⋙ (G a.right).obj))
        (K : Cocone D)
        (eK : K.pt ≅ S.complex ((V.ι.app i).toFunctor.op ⋙ c.pt.obj)),
        (∀ (a a' : Under i) (b : a ⟶ a') (p : ℕ) (t : Fin (p + 1) → T),
          Arrow.mk ((eD a).inv.f p ≫ (D.map b).f p ≫ (eD a').hom.f p ≫
            AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
          Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
            (fun t ↦ (G a.right).obj.obj
              (op ((F.map a.hom).toFunctor.obj (S.W p t)))) t) ≫
            (θ a.right a'.right b.right).app
              (op ((F.map a.hom).toFunctor.obj (S.W p t))))) ∧
        (∀ (a : Under i) (p : ℕ) (t : Fin (p + 1) → T),
          Arrow.mk ((eD a).inv.f p ≫ (K.ι.app a).f p ≫ eK.hom.f p ≫
            AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
          Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
            (fun t ↦ (G a.right).obj.obj
              (op ((F.map a.hom).toFunctor.obj (S.W p t)))) t) ≫
            β a.right ((F.map a.hom).toFunctor.obj (S.W p t)) ≫
            (c.ι.app a.right).hom.app
              (op ((V.ι.app a.right).toFunctor.obj
                ((F.map a.hom).toFunctor.obj (S.W p t)))))) ∧
        Nonempty (IsColimit K) := by
  intro β hβ c hc i T _ U f hom _ S
  obtain ⟨D, eD, K, eK, hD, hK⟩ :=
    colimitSite_cech_cocone_exists F P V Q G θ hθid hθcomp H E hβ c i f hom S
  refine ⟨D, eD, K, eK, hD, hK, ?_⟩
  have hp (p : ℕ) :
      Nonempty (IsColimit ((HomologicalComplex.eval _ (ComplexShape.up ℕ) p).mapCocone K)) := by
    exact colimitSite_finiteProduct_sections_isColimit F P hfinite hcover hpullback V
      hobjects harrows Q hQ G θ H E hβ c hc i (S.W p)
      (D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) p)
      (fun a ↦ (HomologicalComplex.eval _ (ComplexShape.up ℕ) p).mapIso (eD a))
      ((HomologicalComplex.eval _ (ComplexShape.up ℕ) p).mapCocone K)
      ((HomologicalComplex.eval _ (ComplexShape.up ℕ) p).mapIso eK)
      (fun a a' b t ↦ hD a a' b p t) (fun a t ↦ hK a p t)
  exact ⟨HomologicalComplex.isColimitOfEval D K (fun p ↦ Classical.choice (hp p))⟩

end CategoryTheory
