/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeSquare
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import Sheaf.Paper.HigherDirectImagePresheaf

/-! # Simultaneous affine coherent edge isomorphisms

Source: Stacks Project, Cohomology, Tags 0ATM, 01FB, 01F8 and 01F2.
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality).

The auxiliary maps below spell out the canonical maps in the statement. A single module
in cohomological degree one represents `E[-1]`. The normalization on the top projection
specifies the truncation projection, independently of any local splitting.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- `Rf_*(G[0])`. Source: Stacks, Tag 01F2
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeK {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) :=
  (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)

/-- Cohomology of the derived image, in particular `A` in degree zero and `E` in degree one.
Source: Stacks, Tag 01F2
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeCohomology {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) (n : ℤ) :=
  (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj (coherentEdgeK f G)

/-- The coefficient `G_T = j_T^*G`. Source: Stacks, Tag 0ATM
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeCoefficient {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :=
  (Scheme.Modules.tensorPullback (pullback.fst f g)).obj G

/-- The canonical module base change is the existing pinned single-degree composite,
specialized to degree zero and the chosen fibre product.
Source: Stacks, Tag 08HY
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeDelta {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :
    (derivedPullback g).obj (coherentEdgeK f G) ⟶
      coherentEdgeK (pullback.snd f g) (coherentEdgeCoefficient f G g) := by
  letI : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
    fun {_ _} k ↦ (Classical.choose exists_derivedPullbackComposition) k
  exact singleDegreeBaseChangeComposite f g (pullback.fst f g) (pullback.snd f g)
    pullback.condition 0 G

/-- `H^1(Lg^*tau)` with the specified single-module counit identifying its target with
`g^*E`. Source: Stacks, Tag 05TC, dual truncation argument
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
def coherentEdgeGamma {S T : Scheme.{u}} (g : T ⟶ S) (K : schemeDerivedCategory S)
    (τ : K ⟶ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj K)) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1).obj ((derivedPullback g).obj K) ⟶
    (Scheme.Modules.tensorPullback g).obj ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj K) :=
  by
  letI := (Classical.choose exists_derivedPullbackComposition) g
  exact (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1).map
        ((derivedPullback g).map τ ≫ pinnedSingleDegreeTensorComparison g
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj K) 1) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1).hom.app _

/-- The cocycle Leray edge, with its target expressed as `H^1(Rf_*(G[0]))` using the
canonical comparison between total and classical right derived functors.
The cocycle condition of the selected theorem determines the edge uniquely.
Source: Stacks, Tags 01F4(2) and 01E4
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
def coherentEdgeEpsilon {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) :
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj G) ⟶
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.globalSectionsFunctor S.toRingedSpace).obj
        (coherentEdgeCohomology f G 1)) :=
  (Classical.choose (exists_lerayEdge_isIso_of_vanishing f) 1).app G ≫
    (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.globalSectionsFunctor S.toRingedSpace).map
        (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
          (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) G 1).inv)

/-- Degree-one cohomology, with scalars restricted along `f_T` to `Gamma(T,O_T)`.
Source: Stacks, Tag 01F2 and the following module-structure remark
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeH {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :=
  (ModuleCat.restrictScalars (pullback.snd f g).appTop.hom).obj
    ((RingedSpace.moduleCohomology (pullback f g).toRingedSpace 1).obj
      (coherentEdgeCoefficient f G g))

/-- Section pullback along the normalized ordinary tensor-pullback unit, with the
preimage of the whole space identified with the whole space.
Source: Stacks, Tag 0096
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
def coherentEdgeSectionPullback {T T' : Scheme.{u}} (h : T' ⟶ T) (M : T.Modules)
    (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M) :
    (RingedSpace.globalSectionsFunctor T'.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback h).obj M) :=
  ((Scheme.Modules.tensorPullback h).obj M).val.presheaf.map
    (eqToHom (congrArg op (Opens.map_top h.base).symm))
      (((Scheme.Modules.tensorPullbackSectionAdjunction h).unit.app M).app ⊤ s)

/-- Section pullback followed by `h^*g^*E ≅ (gh)^*E`.
Source: Stacks, Tags 0096 and 0097
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
def coherentEdgeRho {S T T' : Scheme.{u}} (g : T ⟶ S) (h : T' ⟶ T) (E : S.Modules)
    (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback g).obj E)) :
    (RingedSpace.globalSectionsFunctor T'.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback (h ≫ g)).obj E) :=
  ((Scheme.Modules.tensorPullbackSectionComp h g).inv.app E).app ⊤
    (coherentEdgeSectionPullback h ((Scheme.Modules.tensorPullback g).obj E) s)

/-- The map `h_X : X_(gh) ⟶ X_g` of the chosen fibre products.
Source: Stacks, Tag 0ATM
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeXMap {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T) : pullback f (h ≫ g) ⟶ pullback f g :=
  baseChangeMap f (Over.homMk h (by rfl) : Over.mk (h ≫ g) ⟶ Over.mk g)

/-- Canonical coefficient identification `h_X^*G_T ≅ G_(gh)` using normalized pullback
composition and the first-projection equation of the fibre product.
Source: Stacks, Tags 0097 and 0ATM
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
def coherentEdgeCoefficientIso {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : T' ⟶ T) :
    (Scheme.Modules.tensorPullback (coherentEdgeXMap f g h)).obj
        (coherentEdgeCoefficient f G g) ≅ coherentEdgeCoefficient f G (h ≫ g) :=
  ((Scheme.Modules.tensorPullbackSectionComp (coherentEdgeXMap f g h)
      (pullback.fst f g)).symm.app G) ≪≫
    eqToIso (congrArg (fun k ↦ (Scheme.Modules.tensorPullback k).obj G)
      (by simp [coherentEdgeXMap, baseChangeMap]))

/-- The cohomology map with exactly the coefficient identification above.
Source: Stacks, Tags 01FB and 01F8
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
def coherentEdgePullback {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : T' ⟶ T) :=
  Scheme.Modules.moduleCohomologyFMap (coherentEdgeXMap f g h)
    ((Scheme.Modules.tensorPullbackSectionAdjunction (coherentEdgeXMap f g h)).homEquiv _ _
      (coherentEdgeCoefficientIso f G g h).hom) 1

/-- For a quasi-compact separated map with a universally base-change-compatible derived
image locally split into finite locally free terms in degrees zero and one, the normalized
truncation projection yields simultaneous linear affine Leray isomorphisms compatible
with every arrow of affine base schemes. The identity on degree-one cohomology specifies
its canonical truncation projection; its existence is part of the conclusion.
Source: Stacks Project, Cohomology, Tags 0ATM, 01FB, 01F8 and 01F2.
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality).

Proof:
1. Trivialize the two locally free cohomology modules on a splitting cover. Free modules
are flat (def-pc-flat-sheaf-modules), and the bounded-above two-term complex is K-flat
(lem-pc-bounded-above-flat-kflat). Derived pullback commutes with open restriction
(lem-pc-derived-pullback-open-restriction-universes) and is computed on this model.
The assumed canonical module base-change isomorphism therefore makes every base-changed
higher direct image quasi-coherent, zero above one, and locally free in degrees zero
and one. This uses no flatness of the base map.
2. The canonical top-cohomology comparison in degree one is precisely gamma, formed from
the truncation projection and the single-module counit. It is invertible by
lem-weil-pbc-derived-pullback-top-cohomology. Compose its inverse with H1(delta) to obtain
beta. This is an isomorphism of module sheaves.
3. On an affine base, lem-pc-affine-vanishing and lem-pc-leray-degenerate-sections make
the cocycle Leray edge invertible. Its cocycle formula is the whole-open value of theta
from lem-weil-pbc-higher-direct-image-presheaf, hence linear. Composing with sections
of beta inverse gives the displayed linear equivalence e.
4. For h : T' to T let m be the canonical module base-change map for f_T and h with the
specified coefficient identification. Horizontal pasting
(lem-pc-derived-base-change-horizontal-pasting), naturality in the coefficient, and
lem-pc-canonical-single-pullback-composition give delta_(gh) = m composed with Lh*(delta_g),
after the canonical composition identifications. The single-module counits here are the
same specified counits used in that pasting, so the composition factors cancel.
5. Naturality and composition of the canonical top comparison
(lem-weil-pbc-derived-pullback-top-cohomology) give
beta_(gh) composed with ordinary pullback composition = b_h composed with h*(beta_g),
where b_h = H1(m) composed with the inverse top comparison for h. No inverse of m is used.
6. Apply lem-weil-pbc-top-base-change-presheaf in top degree one. The vanishing from
step 1 supplies its hypothesis. At the whole open, its theta maps are these Leray edges,
and its coefficient morphism is exactly coherentEdgeCoefficientIso. Thus epsilon_(T')
composed with h_X* equals sections of b_h composed with section pullback and epsilon_T.
7. Substitute steps 5 and 6 into the formula for e_(gh). Naturality of the ordinary
pullback unit (lem-pc-module-pullback-adjunction) moves beta_g inverse across section
pullback; ordinary composition (lem-pc-module-pullback-identity-composition) identifies
the result with rho_h composed with e_g. All maps are canonical and the splitting cover
only checked the hypotheses, so this is one simultaneous family for all affine bases. -/
theorem coherent_affine_base_change_edge_naturality
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    (G : X.Modules) [G.IsQuasicoherent]
    [SheafOfModules.IsFiniteLocallyFree (coherentEdgeCohomology f G 0)]
    [SheafOfModules.IsFiniteLocallyFree (coherentEdgeCohomology f G 1)]
    (hsplit : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ Nonempty
      ((schemeOpenRestriction S U).mapDerivedCategory.obj (coherentEdgeK f G) ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
            ((schemeOpenRestriction S U).obj (coherentEdgeCohomology f G 0)) ⊞
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 1).obj
            ((schemeOpenRestriction S U).obj (coherentEdgeCohomology f G 1))))
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      IsIso (coherentEdgeDelta f G g)) :
    ∃ τ : coherentEdgeK f G ⟶ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj
          (coherentEdgeCohomology f G 1),
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).map τ ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).hom.app
            (coherentEdgeCohomology f G 1) = 𝟙 _) ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (coherentEdgeGamma g (coherentEdgeK f G) τ)) ∧
      ∃ β : ∀ (T : Scheme.{u}) (g : T ⟶ S),
          (Scheme.Modules.tensorPullback g).obj (coherentEdgeCohomology f G 1) ≅
            coherentEdgeCohomology (pullback.snd f g) (coherentEdgeCoefficient f G g) 1,
        (∀ (T : Scheme.{u}) (g : T ⟶ S),
          coherentEdgeGamma g (coherentEdgeK f G) τ ≫ (β T g).hom =
            (DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1).map
                (coherentEdgeDelta f G g)) ∧
        ∃ e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
            coherentEdgeH f G g ≃ₗ[Γ(T, ⊤)]
              (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
                ((Scheme.Modules.tensorPullback g).obj (coherentEdgeCohomology f G 1)),
          (∀ (T : Scheme.{u}) (g : T ⟶ S) (hT : IsAffine T),
            IsIso (coherentEdgeEpsilon (pullback.snd f g) (coherentEdgeCoefficient f G g)) ∧
            ∀ x : coherentEdgeH f G g,
              e T g hT x = (RingedSpace.globalSectionsFunctor T.toRingedSpace).map
                (β T g).inv
                  (coherentEdgeEpsilon (pullback.snd f g) (coherentEdgeCoefficient f G g) x)) ∧
          ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
            (hT : IsAffine T) (hT' : IsAffine T') (x : coherentEdgeH f G g),
            e T' (h ≫ g) hT' (coherentEdgePullback f G g h x) =
              coherentEdgeRho g h (coherentEdgeCohomology f G 1) (e T g hT x) := by
  sorry

end AlgebraicGeometry
