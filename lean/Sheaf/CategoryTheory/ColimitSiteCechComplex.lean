module

public import Sheaf.CategoryTheory.ColimitSites
public import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.CategoryTheory.ColimitSiteCechTransport
import Sheaf.CategoryTheory.ColimitSiteCechColimit

/-! # Čech complexes and filtered colimits of sites

Source: Stacks Project, Sites 09YL, 09YN, and Cohomology on Sites 09YP.
(blueprint: lem-weil-pbc-colimit-of-sites-cech-complex).

The filtered index category is the opposite of the source's cofiltered category.
The maps `θ` are the adjoints of the inverse-image transition maps. The diagram `H`
is the diagram of inverse images on the colimit site, with its maps specified by `hH`.
All equations involving strict cocone identities are expressed in the arrow category.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites 09YL, 09YN; Cohomology on Sites, proof of 09YP.
(blueprint: lem-weil-pbc-colimit-of-sites-cech-complex).

A finite covering and its chosen products transport to every subsequent stage and to
the colimit site. Its stagewise Čech complexes, with the adjoint section transition maps,
form a filtered diagram over `Under i`. The canonical section maps to the colimit sheaf
make its Čech complex a colimit of that diagram.

Here `θ` is the unit followed by the transition map under inverse-image adjunction;
its identity and composition laws are `hθid` and `hθcomp`. The isomorphisms `E` identify
`H` with the inverse-image sheaves, and `β` is precisely their adjunction unit. `hH`
characterizes the induced transition maps on these sheaves by adjunction. Thus none of
the maps of either diagram, nor any degreewise isomorphism, is assumed arbitrarily.
The complexes use `S` on the initial site with the pulled-back stage presheaf, which is
exactly the complex of the transported covering by the product identifications below.

Proof:
1. Continuity transports the covering and its binary fibre products (09YL). Induction
   transports the chosen iterated products and their projections, giving the first two
   clauses. Uniqueness in their universal properties also identifies the index maps.
2. Apply the section transitions of lem-weil-pbc-colimit-of-sites-sections to each chosen
   product. Naturality commutes with every face projection, hence with the alternating
   differential. The identity and composition laws hold factorwise, giving `D`.
3. In degree `p`, commute the filtered colimit with the finite product indexed by
   `Fin (p+1) → T`. Apply the section comparison (09YN) to each product. This identifies
   the degreewise canonical map with the sections of the colimit sheaf at that product.
4. Naturality again makes these maps commute with the differential, giving `K` with the
   stated coprojections. Every component is an isomorphism by step 3, so the comparison
   is an isomorphism of complexes, equivalently `K` is a colimit cocone.
-/
theorem colimitSite_cech_complex_isIso
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
      (∀ a : Under i,
        Presieve.ofArrows (fun t ↦ (F.map a.hom).toFunctor.obj (f t))
          (fun t ↦ (F.map a.hom).toFunctor.map (hom t)) ∈
            P a.right ((F.map a.hom).toFunctor.obj U) ∧
        ∃ Sa : SiteCechComplex (fun t ↦ (F.map a.hom).toFunctor.obj (f t))
            (fun t ↦ (F.map a.hom).toFunctor.map (hom t)),
          ∀ (p : ℕ) (t : Fin (p + 1) → T),
            ∃ e : (F.map a.hom).toFunctor.obj (S.W p t) ≅ Sa.W p t,
              ∀ k, e.hom ≫ Sa.pr p t k = (F.map a.hom).toFunctor.map (S.pr p t k)) ∧
      (Presieve.ofArrows (fun t ↦ (V.ι.app i).toFunctor.obj (f t))
          (fun t ↦ (V.ι.app i).toFunctor.map (hom t)) ∈
            Q ((V.ι.app i).toFunctor.obj U) ∧
        ∃ Sc : SiteCechComplex (fun t ↦ (V.ι.app i).toFunctor.obj (f t))
            (fun t ↦ (V.ι.app i).toFunctor.map (hom t)),
          ∀ (p : ℕ) (t : Fin (p + 1) → T),
            ∃ e : (V.ι.app i).toFunctor.obj (S.W p t) ≅ Sc.W p t,
              ∀ k, e.hom ≫ Sc.pr p t k = (V.ι.app i).toFunctor.map (S.pr p t k)) ∧
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
        Nonempty (IsColimit K) ∧
        ∀ (cD : Cocone D) (hcD : IsColimit cD), IsIso (hcD.desc K) := by
  dsimp
  intro hcompat c hc i T instT U f hom hcov S
  have ht := colimitSite_cech_complex_transport F P hfinite hcover hpullback V
    hobjects harrows Q hQ G θ hθid hθcomp H E hcompat c hc i f hom hcov S
  obtain ⟨D, eD, K, eK, hD, hK, hcolimit⟩ :=
    colimitSite_cech_complex_colimit F P hfinite hcover hpullback V
      hobjects harrows Q hQ G θ hθid hθcomp H E hcompat c hc i f hom hcov S
  refine ⟨ht.1, ht.2, D, eD, K, eK, hD, hK, hcolimit, ?_⟩
  intro cD hcD
  exact hcD.nonempty_isColimit_iff_isIso_desc.mp hcolimit

end CategoryTheory
