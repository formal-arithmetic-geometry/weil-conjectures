/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.IndFiniteEtaleLocalSystem
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import WeilConjectures.AlgebraicGeometry.AffineSectionsColimit
import Sheaf.CategoryTheory.SetSheafCoverDescent
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Calculus of set local systems

Source: ILO, Travaux de Gabber, Exposé XVII, 7.2.1–7.2.4 and the proof of 7.2.6,
pp. 301–303 (blueprint: lem-per-set-local-system-calculus).
The total-space equivalence below is characterized on sections, restrictions and maps;
its existential quantifier does not introduce an unspecified choice of total space.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Sectionwise description of a group-sheaf action, with its two action laws and
restriction compatibility. This is the action interface in ILO XVII 7.2.6
(blueprint: lem-per-set-local-system-calculus). -/
structure LocalSystemSheafAction {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1})
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) where
  smul : ∀ U : X.Etaleᵒᵖ, G.obj.obj U → F.obj.obj U → F.obj.obj U
  one_smul : ∀ (U : X.Etaleᵒᵖ) (s : F.obj.obj U), smul U 1 s = s
  mul_smul : ∀ (U : X.Etaleᵒᵖ) (g h : G.obj.obj U) (s : F.obj.obj U),
    smul U (g * h) s = smul U g (smul U h s)
  naturality : ∀ {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U)
    (s : F.obj.obj U), F.obj.map f (smul U g s) = smul V (G.obj.map f g) (F.obj.map f s)

/-- Regard an arrow into the étale object Y as an object of Y's small étale site.
Source: ILO XVII 7.2.6, slice-site identification
(blueprint: lem-per-set-local-system-calculus). -/
def localSystemLift {X Y : Scheme.{u}} (q : Y ⟶ X) [Etale q]
    {U : X.Etale} (a : U ⟶ Etale.mk q) : Y.Etale :=
  Etale.mk a.left

/-- Restriction of the lifted object along an arrow of the base site.
Source: ILO XVII 7.2.6, restrictions in the total-space formula
(blueprint: lem-per-set-local-system-calculus). -/
def localSystemLiftMap {X Y : Scheme.{u}} (q : Y ⟶ X) [Etale q]
    {U V : X.Etale} (b : V ⟶ U) (a : U ⟶ Etale.mk q) :
    localSystemLift q (b ≫ a) ⟶ localSystemLift q a :=
  MorphismProperty.Over.homMk b.left rfl

/-- The tautological section of h_Y attached to an object of Y's étale site.
Source: ILO XVII 7.2.6, the fibre p(t)=a
(blueprint: lem-per-set-local-system-calculus). -/
def localSystemLabel {X Y : Scheme.{u}} (q : Y ⟶ X) [Etale q] (V : Y.Etale) :
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale q)).obj V ⟶ Etale.mk q :=
  MorphismProperty.Over.homMk V.hom rfl

/-- A local system is a filtered union of finite local-system subsheaves, in the ambient
category of set sheaves. The monomorphisms are the actual cocone legs into F, and every
finite local-system subsheaf of F factors through one of them, so the family is cofinal among
all finite local-system subsheaves: F is the filtered union of all of them.
Source: ILO XVII 7.2.2–7.2.3 and the start of 7.2.6, pp. 301–302
(blueprint: lem-per-set-local-system-calculus).

Proof: Trivialize finite diagrams of finite local systems étale locally and descend their
finite limits and colimits (thm-galois-lc-etale, lem-pe-set-sheaf-cover-descent). On a connected
component, monodromy identifies a filtered presentation with a union of finite invariant
subsets (lem-per-set-local-system-monodromy, thm-galois-fundamental). Finite invariant subsets
are directed by union. Their inclusions are ambient monomorphisms, as can be tested on the
affine étale basis using aux-weil-pbc-affine-sections-colimit and
lem-weil-pbc-affine-etale-site-topos. Their colimit maps isomorphically to F by monodromy.
Every finite local-system subsheaf is among them, its fibre inclusion determining it by full
faithfulness.
A Noetherian scheme has finitely many open connected components; take the finite product of
these presentations. On the empty scheme the sole sheaf is the empty representable. -/
theorem indFiniteEtale_filtered_union (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (hF : IsIndFiniteEtaleSheaf F) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ X.FiniteEtale)
      (ι : D ⋙ ObjectProperty.ι _ ⋙ X.smallEtaleTopology.uliftYoneda.{u + 1} ⟶
        (Functor.const I).obj F),
      (∀ i : I, Mono (ι.app i)) ∧ Nonempty (IsColimit (Cocone.mk F ι)) ∧
      ∀ (P : X.FiniteEtale)
        (m : X.smallEtaleTopology.uliftYoneda.{u + 1}.obj ((ObjectProperty.ι _).obj P) ⟶ F),
        Mono m → ∃ (i : I)
          (g : X.smallEtaleTopology.uliftYoneda.{u + 1}.obj ((ObjectProperty.ι _).obj P) ⟶
            X.smallEtaleTopology.uliftYoneda.{u + 1}.obj ((ObjectProperty.ι _).obj (D.obj i))),
          g ≫ ι.app i = m := by
  sorry

/-- Closure under all small ambient colimits, including the empty colimit.
Source: ILO XVII 7.2.4, p. 302 (blueprint: lem-per-set-local-system-calculus).

Proof: Finite coproducts of finite subsystems are finite local systems, by an étale local
finite-set calculation. The ambient coproduct of arbitrary local systems is the filtered
colimit of these finite coproducts. For parallel arrows use finite invariant subsets (A,B)
with both images of A contained in B, and form their finite coequalizers. Their filtered
colimit is the ambient coequalizer by its universal property. An arbitrary small colimit
is a coequalizer of coproducts indexed by the objects and arrows. Apply this on the finite
open connected-component decomposition of X; the empty component case is automatic. -/
theorem indFiniteEtale_colimit (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X]
    {I : Type (u + 1)} [SmallCategory I]
    (D : I ⥤ Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hD : ∀ i : I, IsIndFiniteEtaleSheaf (D.obj i))
    (c : Cocone D) (hc : IsColimit c) : IsIndFiniteEtaleSheaf c.pt := by
  sorry

/-- Closure under finite ambient limits, including the terminal sheaf.
Source: ILO XVII 7.2.4, p. 302 (blueprint: lem-per-set-local-system-calculus).

Proof: Finite limits of finite local systems are finite by an étale local finite-set
calculation. Products and equalizers of filtered finite-subsystem unions are the filtered
colimits of their finite-stage products and equalizers. On the affine étale basis this is
filtered-colimit/finite-limit commutation for sets (aux-weil-pbc-affine-sections-colimit,
lem-weil-pbc-filtered-colimits-commute-finite-limits). The terminal sheaf is represented by
X. Products and equalizers give every finite limit. Reduce general X to its finitely many
open connected components, including the empty scheme. -/
theorem indFiniteEtale_finite_limit (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X]
    {I : Type (u + 1)} [SmallCategory I] [FinCategory I]
    (D : I ⥤ Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hD : ∀ i : I, IsIndFiniteEtaleSheaf (D.obj i))
    (c : Cone D) (hc : IsLimit c) : IsIndFiniteEtaleSheaf c.pt := by
  sorry

/-- Pullback along finite étale q preserves set local systems.
Source: ILO XVII 7.2.4, p. 302 (blueprint: lem-per-set-local-system-calculus).

Proof: Inverse image is restriction along q, by
lem-weil-pbc-sets-etale-inverse-image-restriction, and takes a finite étale representable
to its finite étale base change. It preserves colimits because it is left adjoint to
set-valued direct image (lem-weil-pbc-sets-etale-inverse-image-composition-units). Apply
this to the filtered finite-stage presentation, with no surjectivity requirement. -/
theorem indFiniteEtale_pullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    (q : Y ⟶ X) [IsFinite q] [Etale q]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (hF : IsIndFiniteEtaleSheaf F) :
    IsIndFiniteEtaleSheaf ((etaleSetPullback q).obj F) := by
  sorry

/-- The slice equivalence has the specified total-space sections and inverse fibres,
respects group-sheaf actions, and its total-space functor preserves local systems.
The equations characterize the equivalences on restrictions and on sheaf maps.
Source: ILO XVII 7.2.6, p. 302 (blueprint: lem-per-set-local-system-calculus).

Proof: (7) Identify Y's étale site with pairs (U,a), by étale composition and cancellation
(lem-weil-pbc-etale-composition-cancellation). Matching pairs (a_i,t_i) glue: first glue the
labels using representability of h_Y, then glue t_i in E. Thus the displayed sigma presheaf
is already a sheaf. The reverse construction is the fibre p(t)=a. Forgetting the label and
taking its fibre give inverse natural isomorphisms, so an equivalence of categories.
(8) An action over h_Y preserves each fibre. Restriction identifies the group of sections
there with that of q inverse-image G (lem-weil-pbc-sets-etale-inverse-image-restriction).
Conversely act on (a,t) without changing a. These formulas are mutually inverse, preserve
equivariant maps, and give the displayed action correspondence.
(9) Maps from the total space to H are natural families E(U,a) → H(U), so total space is
left adjoint to restriction. It preserves colimits (lem-weil-pbc-left-adjoint-preserves-colimits).
On a finite étale representable P over Y it is P regarded over X. Finite étale composition
(lem-weil-pbc-finite-composition) makes this a finite stage over X. Apply the colimit
preservation to any filtered presentation of E. No surjectivity is used, and empty fibres
are the empty sigma types. -/
theorem indFiniteEtale_total_space {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    (q : Y ⟶ X) [IsFinite q] [Etale q] :
    ∃ ξ : Sheaf Y.smallEtaleTopology (Type (u + 1)) ≌
        Over (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk q)),
      ∃ ε : ∀ (E : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : X.Etale),
        ((ξ.functor.obj E).left.obj.obj (op U)) ≃
          (Σ a : U ⟶ Etale.mk q, E.obj.obj (op (localSystemLift q a))),
      (∀ (E : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
          (t : (ξ.functor.obj E).left.obj.obj (op U)),
        ((ξ.functor.obj E).hom.hom.app (op U) t).down = (ε E U t).1) ∧
      (∀ (E : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U V : X.Etale)
          (b : V ⟶ U) (a : U ⟶ Etale.mk q)
          (t : E.obj.obj (op (localSystemLift q a))),
        ε E V ((ξ.functor.obj E).left.obj.map b.op ((ε E U).symm ⟨a, t⟩)) =
          ⟨b ≫ a, E.obj.map (localSystemLiftMap q b a).op t⟩) ∧
      (∀ (E E' : Sheaf Y.smallEtaleTopology (Type (u + 1))) (f : E ⟶ E')
          (U : X.Etale) (a : U ⟶ Etale.mk q)
          (t : E.obj.obj (op (localSystemLift q a))),
        ε E' U (((ξ.functor.map f).left).hom.app (op U) ((ε E U).symm ⟨a, t⟩)) =
          ⟨a, f.hom.app (op (localSystemLift q a)) t⟩) ∧
      (∀ (E : Sheaf Y.smallEtaleTopology (Type (u + 1))),
        IsIndFiniteEtaleSheaf E → IsIndFiniteEtaleSheaf (ξ.functor.obj E).left) ∧
      ∃ β : ∀
          (F : Over (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk q)))
          (V : Y.Etale),
        (ξ.inverse.obj F).obj.obj (op V) ≃
          {t : F.left.obj.obj
              (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale q)).obj V)) //
            (F.hom.hom.app
              (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale q)).obj V)) t).down =
                localSystemLabel q V},
      (∀ (F : Over (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk q)))
          (V W : Y.Etale) (b : W ⟶ V) (t : (ξ.inverse.obj F).obj.obj (op V)),
        (β F W ((ξ.inverse.obj F).obj.map b.op t)).val =
          F.left.obj.map
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale q)).map b).op
            (β F V t).val) ∧
      (∀ (F F' : Over (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk q)))
          (f : F ⟶ F') (V : Y.Etale) (t : (ξ.inverse.obj F).obj.obj (op V)),
        (β F' V ((ξ.inverse.map f).hom.app (op V) t)).val =
          f.left.hom.app
            (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale q)).obj V))
            (β F V t).val) ∧
      (∀ (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1})
          (F : Over (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk q))),
        ∃ α :
          {A : LocalSystemSheafAction G F.left //
            ∀ (U : X.Etaleᵒᵖ) (g : G.obj.obj U) (t : F.left.obj.obj U),
              F.hom.hom.app U (A.smul U g t) = F.hom.hom.app U t} ≃
          LocalSystemSheafAction
            ((AlgebraicGeometry.Etale.localizationRestriction GrpCat.{u + 1}
              q inferInstance).obj G) (ξ.inverse.obj F),
          ∀ (A : {A : LocalSystemSheafAction G F.left //
              ∀ (U : X.Etaleᵒᵖ) (g : G.obj.obj U) (t : F.left.obj.obj U),
                F.hom.hom.app U (A.smul U g t) = F.hom.hom.app U t})
            (V : Y.Etale)
            (g : G.obj.obj
              (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale q)).obj V)))
            (t : (ξ.inverse.obj F).obj.obj (op V)),
            (β F V ((α A).smul (op V) g t)).val =
              A.val.smul
                (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale q)).obj V))
                g (β F V t).val) := by
  sorry

end AlgebraicGeometry.Scheme
