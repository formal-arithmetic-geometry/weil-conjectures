/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module
public import Sheaf.ConstructibleSheaf.GaloisCoverModuleDescent
public import Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

import Sheaf.CategoryTheory.Galois.GaloisTransitive
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.FiniteEtaleFiniteLimits
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegree
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Monodromy and tensor products of descended modules

Source: Stacks Project, Fundamental Groups, Section 03SF and Lemma 0BN2;
ILO, Travaux de Gabber, Expose XVII, 7.2.1--7.2.4, pp. 301--302;
Stacks Project, Modules on Sites, Tags 03EL and 0GMW.
(blueprint: lem-per-galois-descent-monodromy-tensor).

The descent equivalence and its natural trivialization are those of
`exists_galoisCoverModuleDescent`. The normalization hypothesis is exactly its
already stated deck formula. The small-site realization, coefficients, constant
sections and tensors remain the existing constructions. Restriction of scalars
and the existing site equivalence connect them to the recorded geometric stalk
and ind-finite monodromy interfaces. The quotient precedes the quantification
of coefficient rings, so it depends only on the marked cover.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace AlgebraicGeometry.GaloisModuleDescent

/-- The sections of the existing descended module sheaf, regarded as fixed-R modules
by restricting scalars along `constantCoefficientUnit`. This is the coefficient
restriction for the CommRingCat-valued constant sheaf used by the descent dependency.
Source: Stacks 03CY, with the size convention in the node's proof Step 1
(blueprint: lem-per-galois-descent-monodromy-tensor). -/
def coefficientPresheaf (S : Scheme.{u}) (R : CommRingCat.{u + 1})
    (M : Modules S R) : (Site S)ᵒᵖ ⥤ ModuleCat.{u + 1} R :=
  let P := (PresheafOfModules.restrictScalars (constantCoefficientUnit (topology S) R)).obj M.val
  { obj := P.obj
    map := fun f ↦ P.map f
    map_id := fun X ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_id X)
    map_comp := fun f g ↦ by ext x; exact P.map_comp_apply f g x }

/-- The fixed-coefficient sheaf underlying the existing ringed-site module, retaining
its abelian sheaf and section maps. The sheaf condition is reflected by forgetting to
abelian groups. Source: Stacks 03CY and ILO XVII 7.2.3, module paragraph
(blueprint: lem-per-galois-descent-monodromy-tensor). -/
def coefficientSheaf (S : Scheme.{u}) (R : CommRingCat.{u + 1}) :
    Modules S R ⥤ Sheaf (topology S) (ModuleCat.{u + 1} R) where
  obj M := ⟨coefficientPresheaf S R M,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := { hom :=
    { app := fun X ↦ (ModuleCat.restrictScalars
        ((constantCoefficientUnit (topology S) R).app X).hom).map (f.val.app X)
      naturality := fun _ _ g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x } }

/-- Transport from the descent dependency's small representative to the original
small etale site, using Mathlib's sheaf equivalence. No sheaf is chosen from an
existence theorem. Source: Stacks 00XZ and the node's proof Step 1
(blueprint: lem-per-galois-descent-monodromy-tensor). -/
def etaleRealization (S : Scheme.{u}) (R : CommRingCat.{u + 1}) :
    Modules S R ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R) := by
  letI : (equivSmallModel.{u + 1} S.Etale).symm.inverse.IsDenseSubsite
      S.smallEtaleTopology (topology S) := by
    change (equivSmallModel.{u + 1} S.Etale).functor.IsDenseSubsite
      S.smallEtaleTopology (topology S)
    exact inferInstanceAs ((equivSmallModel.{u + 1} S.Etale).functor.IsDenseSubsite
      S.smallEtaleTopology
        ((equivSmallModel.{u + 1} S.Etale).inverse.inducedTopology S.smallEtaleTopology))
  exact coefficientSheaf S R ⋙
    ((equivSmallModel.{u + 1} S.Etale).symm.sheafCongr (topology S)
      S.smallEtaleTopology (ModuleCat.{u + 1} R)).functor

/-- The actual module-valued geometric stalk after this canonical site transport.
It is the pointed-neighbourhood colimit of `pointedEtaleStalk`, with its existing
functorial maps. Source: ILO XVII 7.2.3 and Stacks 04FM
(blueprint: lem-per-galois-descent-monodromy-tensor). -/
abbrev stalk {S : Scheme.{u}} (R : CommRingCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :=
  etaleRealization S R ⋙ (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)

/-- The natural local trivialization supplied by `exists_galoisCoverModuleDescent`,
written in the direction from constants to descended modules. Restriction to this
slice is the inverse image along the etale cover. Source: Stacks 04TR and 00XR
(blueprint: lem-per-galois-descent-monodromy-tensor). -/
abbrev trivialization {S : Scheme.{u}} (c : S.FiniteEtale) (R : CommRingCat.{u + 1})
    (E : Rep.{u + 1} R (Aut c) ≌ (Trivialized c R).FullSubcategory) :=
  forget₂ (Rep.{u + 1} R (Aut c)) (ModuleCat.{u + 1} R) ⋙
      constantCoefficientModule (topology S) R ⋙
        overFunctor (constantCoefficientRing (topology S) R) (coverObject c) ≅
    realization c R E ⋙ overFunctor (constantCoefficientRing (topology S) R) (coverObject c)

/-- The section s_v on the cover: apply the descent trivialization to the existing
constant section v. Source: the node's proof Steps 3--4; Stacks 04TR and ILO XVII 7.2.3
(blueprint: lem-per-galois-descent-monodromy-tensor). -/
def liftedConstant {S : Scheme.{u}} (c : S.FiniteEtale) (R : CommRingCat.{u + 1})
    (E : Rep.{u + 1} R (Aut c) ≌ (Trivialized c R).FullSubcategory)
    (e : trivialization c R E) (V : Rep.{u + 1} R (Aut c)) (v : V) :
    ((realization c R E).obj V).val.obj (op (coverObject c)) :=
  ((e.app V).hom.val.app (op (Over.mk (𝟙 (coverObject c)))))
    (constantSection S R ((forget₂ _ (ModuleCat R)).obj V) (coverObject c) v)

/-- The specified map v to the germ of s_v at the chosen lift, read as a stalk on S.
The map is the recorded pointed-neighbourhood germ at (T,t), rather than an arbitrary
stalk isomorphism. Source: Stacks 04FM and ILO XVII 7.2.3
(blueprint: lem-per-galois-descent-monodromy-tensor). -/
def constantGerm {S : Scheme.{u}} (c : S.FiniteEtale) (R : CommRingCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ c.obj.left)
    (E : Rep.{u + 1} R (Aut c) ≌ (Trivialized c R).FullSubcategory)
    (e : trivialization c R E) (V : Rep.{u + 1} R (Aut c)) (v : V) :
    (stalk R (t ≫ c.obj.hom)).obj ((realization c R E).obj V) :=
  (pointedEtaleGerm ((etaleRealization S R).obj ((realization c R E).obj V))
    (t ≫ c.obj.hom) c.obj (Over.homMk t rfl)).hom
      (liftedConstant c R E e V v)

/-- Exactly the deck-transformation clause of `exists_galoisCoverModuleDescent`.
It specifies the given left-action descent datum; the inverse comes from the
contravariance of sections. Source: Stacks 04TR and the node's proof Step 4
(blueprint: lem-per-galois-descent-monodromy-tensor). -/
def IsDeckNormalized {S : Scheme.{u}} (c : S.FiniteEtale) (R : CommRingCat.{u + 1})
    (E : Rep.{u + 1} R (Aut c) ≌ (Trivialized c R).FullSubcategory)
    (e : trivialization c R E) : Prop :=
  ∀ (V : Rep.{u + 1} R (Aut c)) (g : Aut c) (v : V),
    (((realization c R E).obj V).val.map (deckMap c g).op)
      (liftedConstant c R E e V v) = liftedConstant c R E e V (V.ρ g⁻¹ v)

/-- The existing ordinary tensor of two R_S-module sheaves. This abbreviation of
`siteSheafTensorRight` retains its sectionwise tensor and module sheafification.
Source: Stacks 03EK and 0GMW (blueprint: lem-per-galois-descent-monodromy-tensor). -/
def tensorSheaf {S : Scheme.{u}} (R : CommRingCat.{u + 1}) (F H : Modules S R) :
    Modules S R :=
  (siteSheafTensorRight
    (A := (constantSheaf (topology S) CommRingCat.{u + 1}).obj R) H).obj F

/-- The existing tensor maps, composed in the two variables. No new tensor is defined.
Source: Stacks 03EK and 03EL (blueprint: lem-per-galois-descent-monodromy-tensor). -/
def tensorSheafMap {S : Scheme.{u}} (R : CommRingCat.{u + 1})
    {F F' H H' : Modules S R} (f : F ⟶ F') (h : H ⟶ H') :
    tensorSheaf R F H ⟶ tensorSheaf R F' H' :=
  (siteSheafTensorRight
    (A := (constantSheaf (topology S) CommRingCat.{u + 1}).obj R) H).map f ≫
      siteSheafTensorSecondMap
        (A := (constantSheaf (topology S) CommRingCat.{u + 1}).obj R) F' h

/-- The recorded local-system monodromy, transported by its specified stalk isomorphism
onto the actual geometric stalk. Its finite-cover germ normalization is the field
`TorsionLocalSystemStalkEquivalence.finiteGerm`. Source: ILO XVII Proposition 7.2.3
(blueprint: lem-per-galois-descent-monodromy-tensor). -/
def stalkAction {S : Scheme.{u}} (R : CommRingCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (M : TorsionLocalSystemStalkEquivalence R s) (L : IndFiniteEtaleModules.{u} S R)
    (g : Aut (FiniteEtale.fiber s)) :
    ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).obj L.obj →ₗ[R]
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).obj L.obj :=
  ((M.stalkIso.hom.app L).hom).comp
    ((((M.equivalence.functor.obj L).obj.ρ g)).comp ((M.stalkIso.inv.app L).hom))

/-- Monodromy, the normalized stalk identification, and ordinary tensor compatibility
for modules descended along a connected finite etale Galois cover. The realization
E and e are supplied by `exists_galoisCoverModuleDescent`; the only condition on them
is that theorem's deck-action formula. The universally quantified monodromy interface
is the one in `torsion_local_system_monodromy`, including its finite-germ field.
The map cstar is the canonical induced map on fundamental groups, specified on all
finite-cover fibres by `pullbackFiberIso`. The kernel equality therefore means exactly
ker(theta) = c_* pi_1(T,t). Continuity into Aut(c) uses its finite discrete topology.
Source: Stacks 03SF and 0BN2; ILO XVII 7.2.3--7.2.4, pp. 301--302; Stacks 03EL and 0GMW
(blueprint: lem-per-galois-descent-monodromy-tensor).

Proof:
1. Work in the small etale representative, as in def-weil-size-convention. Positive
constant degree (lem-weil-pbc-finite-etale-trace-degree) makes c a covering. Slice
localization (lem-weil-pbc-etale-site-localization-open), inverse-image restriction
(lem-weil-pbc-etale-inverse-image-restriction) and constant restriction
(lem-weil-pbc-site-constant-restriction) give the stipulated local identifications.
2. The geometric finite-etale fibre is a Galois-category fibre
(lem-fet-galois-category), and c is connected
(lem-galois-finite-etale-connected-object). Its fundamental-group action is transitive
(lem-galois-transitive), and the deck action is simply transitive (def-galois-object).
For g define a_g uniquely by g(t) = a_g(t). The two actions commute by naturality,
so a_(gh) = a_h a_g. Set theta(g) = a_g inverse. This gives a homomorphism, continuous
and surjective by the finite discrete orbit map and transitivity. Its kernel is the
stabilizer of t, which is c_* pi_1(T,t) by thm-galois-fundamental. The characterization
of cstar is precisely the canonical finite-etale pullback-fibre comparison. This
construction does not involve a coefficient ring or a module.
3. Put L = T(V). Its inverse image is constant, hence it is a local system by the
converse finite-cover locality clause of lem-per-torsion-local-system-monodromy.
Take the germ of s_v = e(v) at t. The constant-stalk isomorphism
(lem-weil-pbc-constant-sheaf-geometric-stalk) identifies its underlying group with V;
constant scalar operations commute with germs, so this is an R-linear isomorphism.
Naturality of the descent trivialization takes s_v to s_f(v), proving naturality.
4. On the graph (id,a) the given left-action descent datum is rho(a), with cocycle
rho(ba) = rho(b) rho(a). The gluing convention e_2 = phi e_1
(lem-pe-set-sheaf-cover-descent) gives L(a)s_v = s_(rho(a inverse)v), precisely the
normalization hypothesis. The finite-cover germ law
(lem-per-local-system-finite-cover-germ-action) gives g germ_t(s_v) = germ_(a_g t)(s_v).
The pointed-neighbourhood colimit identifies this with germ_t(L(a_g)s_v), proving
monodromy g gamma(v) = gamma(rho(theta(g))v), with the required inverse sign.
5. Module sheafification of the tensor of constant presheaves gives the natural
constant-tensor comparison (lem-pc-sites-module-sheafification-tensor). It sends
constant pure tensors to their tensor. Localization commutes with tensor, with the
same normalization (lem-sfb-localized-site-tensor-restriction). No finite-generation
or flatness assumption is needed.
6. The maps (id,a), for a in Aut(c), identify the coproduct of copies of T with
T times_S T. They form a map of finite etale objects (lem-fet-finite-limits), bijective
on the geometric fibre by simple transitivity. The conservative fibre functor
(lem-fet-galois-category, def-galois-category) therefore makes it an isomorphism.
Triple overlaps have coordinates (x,ax,bax), with pair labels a,b,ba.
7. The local tensor comparison has transition rho(a) tensor sigma(a), exactly the
diagonal action on V tensor_R W. Step 6 checks this on the entire overlap. The local
comparison and its inverse glue uniquely (lem-pe-set-sheaf-cover-descent), as linearity
is local. Naturality of tensor maps glues by the same uniqueness. Step 5 gives the
pure-tensor normalization in the conclusion. Restricting this equation to each
etale object over T is exactly the asserted pullback normalization. -/
theorem galois_descent_monodromy_tensor
    {S : Scheme.{u}} [IsNoetherian S] [ConnectedSpace S]
    (c : S.FiniteEtale) [PreGaloisCategory.IsGalois c]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ c.obj.left) :
    ∃ θ : Aut (FiniteEtale.fiber (t ≫ c.obj.hom)) →* Aut c,
      @Continuous _ _ inferInstance ⊥ θ ∧ Function.Surjective θ ∧
      (∀ g : Aut (FiniteEtale.fiber (t ≫ c.obj.hom)),
        (FiniteEtale.fiber (t ≫ c.obj.hom)).map (θ g)⁻¹.hom (Over.homMk t rfl) =
          g.hom.app c (Over.homMk t rfl)) ∧
      (∃ cstar : Aut (FiniteEtale.fiber t) →*
          Aut (FiniteEtale.fiber (t ≫ c.obj.hom)),
        (∀ (g : Aut (FiniteEtale.fiber t)) (P : S.FiniteEtale)
          (a : (FiniteEtale.fiber t).obj ((FiniteEtale.pullback c.obj.hom).obj P)),
          (cstar g).hom.app P ((FiniteEtale.pullbackFiberIso c.obj.hom t).hom.app P a) =
            (FiniteEtale.pullbackFiberIso c.obj.hom t).hom.app P
              (g.hom.app ((FiniteEtale.pullback c.obj.hom).obj P) a)) ∧
        θ.ker = cstar.range) ∧
      ∀ (R : CommRingCat.{u + 1}) (n : ℕ), 0 < n → (n : R) = 0 →
      ∀ (E : Rep.{u + 1} R (Aut c) ≌ (Trivialized c R).FullSubcategory)
        (e : trivialization c R E), IsDeckNormalized c R E e →
      ∃ hL : ∀ V : Rep.{u + 1} R (Aut c),
          IsIndFiniteEtaleModule ((etaleRealization S R).obj ((realization c R E).obj V)),
      ∃ γ : ∀ V : Rep.{u + 1} R (Aut c),
          V ≃ₗ[R] (stalk R (t ≫ c.obj.hom)).obj ((realization c R E).obj V),
        (∀ (V : Rep.{u + 1} R (Aut c)) (v : V),
          γ V v = constantGerm c R t E e V v) ∧
        (∀ (V V' : Rep.{u + 1} R (Aut c)) (f : V ⟶ V') (v : V),
          ((stalk R (t ≫ c.obj.hom)).map ((realization c R E).map f)).hom (γ V v) =
            γ V' (f.hom v)) ∧
        (∀ (M : TorsionLocalSystemStalkEquivalence R (t ≫ c.obj.hom))
          (V : Rep.{u + 1} R (Aut c)) (g : Aut (FiniteEtale.fiber (t ≫ c.obj.hom)))
          (v : V),
          stalkAction R (t ≫ c.obj.hom) M
            ⟨(etaleRealization S R).obj ((realization c R E).obj V), hL V⟩ g (γ V v) =
              γ V (V.ρ (θ g) v)) ∧
        (∃ i : ∀ V W : Rep.{u + 1} R (Aut c),
            tensorSheaf R ((realization c R E).obj V) ((realization c R E).obj W) ≅
              (realization c R E).obj (V ⊗ W),
          (∀ (V V' W W' : Rep.{u + 1} R (Aut c)) (f : V ⟶ V') (h : W ⟶ W'),
            tensorSheafMap R ((realization c R E).map f) ((realization c R E).map h) ≫
                (i V' W').hom =
              (i V W).hom ≫ (realization c R E).map (f ⊗ₘ h)) ∧
          (∀ (V W : Rep.{u + 1} R (Aut c)) (v : V) (w : W),
            ((i V W).hom.val.app (op (coverObject c)))
                (siteSheafTensorTmul
                  (A := (constantSheaf (topology S) CommRingCat.{u + 1}).obj R)
                  ((realization c R E).obj V) ((realization c R E).obj W)
                  (op (coverObject c)) (liftedConstant c R E e V v)
                  (liftedConstant c R E e W w)) =
              liftedConstant c R E e (V ⊗ W) (v ⊗ₜ[R] w))) := by
  sorry

end AlgebraicGeometry.GaloisModuleDescent
