/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.AlgebraicGeometry.IndFiniteEtaleLocalSystem
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.AffineSectionsColimit
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.AlgebraicGeometry.FiniteEtaleFiniteLimits
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import Sheaf.CategoryTheory.SetSheafCoverDescent
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import WeilConjectures.AlgebraicGeometry.FiniteTypeEtaleModuleStalk
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence

/-! # Monodromy and ambient exactness of torsion local systems

Source: ILO, Travaux de Gabber, Exposé XVII, Definition 7.2.1 and Propositions
7.2.2–7.2.5, pp. 301–303 (blueprint: lem-per-torsion-local-system-monodromy).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open Opposite
namespace AlgebraicGeometry.Scheme

/-- The forgetful functor to coefficient modules, using the already defined category of
representations with open element stabilizers. Source: ILO XVII 7.2.3, module paragraph
(blueprint: lem-per-torsion-local-system-monodromy). -/
noncomputable abbrev torsionMonodromyForget (R : Type (u + 1)) [CommRing R]
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :=
  ObjectProperty.ι (fun M : Rep.{u + 1} R (Aut (FiniteEtale.fiber s)) ↦
    ∀ x : M.V, IsOpen {g | M.ρ g x = x}) ⋙
    forget₂ (Rep.{u + 1} R (Aut (FiniteEtale.fiber s))) (ModuleCat.{u + 1} R)

/-- A stalk equivalence normalized on germs over finite étale covers. This normalization
specifies the geometric monodromy action, rather than merely an abstract equivalence.
Source: ILO XVII 7.2.3 and its module consequence
(blueprint: lem-per-torsion-local-system-monodromy). -/
structure TorsionLocalSystemStalkEquivalence {S : Scheme.{u}}
    (R : Type (u + 1)) [CommRing R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) where
  /-- The equivalence to discrete continuous modules; no finite-stalk condition. -/
  equivalence : IndFiniteEtaleModules.{u} S R ≌
    Rep.DiscreteContinuousRep.{u + 1} R (Aut (FiniteEtale.fiber s))
  /-- The underlying functor is the actual module-valued geometric stalk. -/
  stalkIso : equivalence.functor ⋙ torsionMonodromyForget R s ≅
    ObjectProperty.ι _ ⋙ (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)
  /-- The equivalence respects sums of morphisms. -/
  additive : equivalence.functor.Additive
  /-- A section over a finite cover has its germ transported by the action on that cover. -/
  finiteGerm (L : IndFiniteEtaleModules.{u} S R) (P : S.FiniteEtale)
    (a : (FiniteEtale.fiber s).obj P) (x : L.obj.obj.obj (op P.obj))
    (g : Aut (FiniteEtale.fiber s)) :
    (stalkIso.hom.app L).hom
        ((equivalence.functor.obj L).obj.ρ g
          ((stalkIso.inv.app L).hom
            (((pointSmallEtale s).toPresheafFiber P.obj a L.obj.obj).hom x))) =
      ((pointSmallEtale s).toPresheafFiber P.obj (g.hom.app P a) L.obj.obj).hom x

/-- A connected component of a Noetherian scheme as an open subscheme. Source: ILO XVII
§7.2, reduction to connected components; existing Noetherian component-openness theorem
(blueprint: lem-per-torsion-local-system-monodromy). -/
def torsionLocalSystemComponent (S : Scheme.{u}) [IsNoetherian S] (x : S) : S.Opens :=
  ⟨connectedComponent x, TopologicalSpace.NoetherianSpace.isOpen_connectedComponent x⟩

/-- The full monodromy assertion, including ambient closure on disconnected schemes.
Source: ILO XVII, Definition 7.2.1 and Propositions 7.2.2–7.2.5, pp. 301–303
(blueprint: lem-per-torsion-local-system-monodromy).

Proof: (1) Restrict to the affine étale site and use affine-section filtered-colimit
comparison. A finite affine cover and finite covers of its overlaps express sections on
a qcqs object as a finite matching equalizer, commuting with filtered colimits.
(2) This gives the limit-colimit Hom formula for filtered colimits of finite étale
representables. The finite Galois equivalence and the fact that continuous discrete
profinite orbits are finite identify these with discrete continuous sets.
(3) Products and constants agree with ambient ones. (4) Transport addition, negation
and each scalar operation through this product-preserving equivalence; locally constant
scalars glue, giving the additive module equivalence and its finite-germ normalization.
(5) After forgetting R, use the finite ring Z/n. Finite invariant additive subgroups
exhaust every stalk, since finite lists of finite orbits generate finite groups of
exponent dividing n. These give finite locally constant additive subsystems.
(6) Apply finite-coefficient exactness to compatible pairs of finite additive subgroups.
Filtered colimits commute with kernels on the qcqs basis and with cokernels universally;
their stalks are the ordinary kernels and cokernels. This gives ambient short exactness.
(7) Direct sums are filtered unions of finite sums of these finite additive subsystems.
The standard difference-map cokernel presentation of a diagram colimit gives every
small ambient colimit. Geometric stalks commute with these colimits.
(8) In an ambient extension, translation by the kernel is a free action with quotient
the last sheaf. The torsion-torsor descent lemma (lem-per-torsion-torsor-descent) makes
the middle sheaf a local system.
(9) Finite-cover pullback is restriction on finite represented objects, hence on their
filtered colimits; the germ comparison specifies the map on fundamental groups.
(10) Finite-cover pushforward preserves local systems: on a splitting cover it is a
finite product, and qcqs-section comparison passes this to filtered additive systems.
(11) For arbitrary L whose pullback is a local system, the cover-descent equalizer of
the two unit maps into successive push-pulls is L. Its terms are local systems by (10),
and its equalizer is a kernel, hence local by (6).
(12) The pointwise stabilizer of the finite union of the orbits of finitely many module
generators is open normal and acts trivially. Its finite Galois cover trivializes L.
Conversely local finite type implies finitely generated geometric stalks.
(13) A Noetherian scheme has finitely many clopen connected components. Sheaves,
operations and exact sequences restrict componentwise; finite products of filtered
index categories combine component presentations. The empty scheme is included. -/
theorem torsion_local_system_monodromy (R : Type (u + 1)) [CommRing R]
    (n : ℕ) (hn : 0 < n) (hR : (n : R) = 0) :
    (∃ E : ∀ (S : Scheme.{u}) [IsNoetherian S] [ConnectedSpace S]
        (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        TorsionLocalSystemStalkEquivalence R s,
      (∀ (S : Scheme.{u}) [IsNoetherian S] [ConnectedSpace S]
        (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
        (K : ShortComplex (IndFiniteEtaleModules.{u} S R)),
        (K.map (ObjectProperty.ι
          (IsIndFiniteEtaleModule.{u} (S := S) (R := R)))).ShortExact ↔
          Function.Injective
            (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).map K.f.hom).hom ∧
          Function.Exact
            (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).map K.f.hom).hom
            (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).map K.g.hom).hom ∧
          Function.Surjective
            (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).map K.g.hom).hom) ∧
      (∀ (S : Scheme.{u}) [IsNoetherian S] [ConnectedSpace S]
        (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
        (L : IndFiniteEtaleModules.{u} S R),
        (L.obj.IsConstant S.smallEtaleTopology ↔
          ∀ (g : Aut (FiniteEtale.fiber s)) (x : ((E S Ω s).equivalence.functor.obj L).obj.V),
            ((E S Ω s).equivalence.functor.obj L).obj.ρ g x = x) ∧
        (IsFiniteLocallyConstantSheaf L.obj ↔
          Module.Finite R
            (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).obj L.obj)) ∧
        (Module.Finite R
            (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).obj L.obj) →
          ∃ P : S.FiniteEtale, IsGalois P ∧
            ((Etale.upperStar (ModuleCat.{u + 1} R) P.obj.hom).obj L.obj).IsConstant
              P.obj.left.smallEtaleTopology)) ∧
      (∀ (S T : Scheme.{u}) [IsNoetherian S] [ConnectedSpace S]
        [IsNoetherian T] [ConnectedSpace T] (c : T ⟶ S) [IsFinite c] [Etale c]
        (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        ∃ h : Aut (FiniteEtale.fiber t) →* Aut (FiniteEtale.fiber (t ≫ c)),
          Continuous h ∧ Function.Injective h ∧
          IsOpen (h.range : Set (Aut (FiniteEtale.fiber (t ≫ c)))) ∧
          (∀ (g : Aut (FiniteEtale.fiber t)) (P : S.FiniteEtale)
            (a : (FiniteEtale.fiber t).obj ((FiniteEtale.pullback c).obj P)),
            (h g).hom.app P ((FiniteEtale.pullbackFiberIso c t).hom.app P a) =
              (FiniteEtale.pullbackFiberIso c t).hom.app P
                (g.hom.app ((FiniteEtale.pullback c).obj P) a)) ∧
          ∀ (L : IndFiniteEtaleModules.{u} S R),
            ∃ hL : IsIndFiniteEtaleModule
                ((Etale.upperStar (ModuleCat.{u + 1} R) c).obj L.obj),
              (∀ (g : Aut (FiniteEtale.fiber t))
                (x : ((E T Ω t).equivalence.functor.obj
                  ⟨(Etale.upperStar (ModuleCat.{u + 1} R) c).obj L.obj, hL⟩).obj.V),
                ((E S Ω (t ≫ c)).stalkIso.inv.app L).hom
                    (((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) c t).hom.app
                      L.obj).hom
                      (((E T Ω t).stalkIso.hom.app
                        ⟨(Etale.upperStar (ModuleCat.{u + 1} R) c).obj L.obj, hL⟩).hom
                        (((E T Ω t).equivalence.functor.obj
                          ⟨(Etale.upperStar (ModuleCat.{u + 1} R) c).obj L.obj, hL⟩).obj.ρ
                          g x))) =
                  ((E S Ω (t ≫ c)).equivalence.functor.obj L).obj.ρ (h g)
                    (((E S Ω (t ≫ c)).stalkIso.inv.app L).hom
                      (((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) c t).hom.app
                        L.obj).hom
                        (((E T Ω t).stalkIso.hom.app
                          ⟨(Etale.upperStar (ModuleCat.{u + 1} R) c).obj L.obj, hL⟩).hom x)))) ∧
              (((Etale.upperStar (ModuleCat.{u + 1} R) c).obj L.obj).IsConstant
                  T.smallEtaleTopology ↔
                ∀ (g : Aut (FiniteEtale.fiber t))
                  (x : ((E S Ω (t ≫ c)).equivalence.functor.obj L).obj.V),
                  ((E S Ω (t ≫ c)).equivalence.functor.obj L).obj.ρ (h g) x = x))) ∧
    (∀ (S : Scheme.{u}) [IsNoetherian S]
      (F G : IndFiniteEtaleModules.{u} S R) (f : F ⟶ G),
      IsIndFiniteEtaleModule.{u} (kernel f.hom) ∧ IsIndFiniteEtaleModule.{u} (cokernel f.hom)) ∧
    (∀ (S : Scheme.{u}) [IsNoetherian S]
      (K : ShortComplex (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R))),
      K.ShortExact → IsIndFiniteEtaleModule K.X₁ → IsIndFiniteEtaleModule K.X₃ →
        IsIndFiniteEtaleModule K.X₂) ∧
    (∀ (S : Scheme.{u}) [IsNoetherian S] (I : Type (u + 1)) [SmallCategory I]
      (D : I ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R))
      (c : Cocone D), IsColimit c → (∀ i, IsIndFiniteEtaleModule.{u} (D.obj i)) →
      IsIndFiniteEtaleModule c.pt ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
          Nonempty (IsColimit
            (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).mapCocone c))) ∧
    (∀ (S : Scheme.{u}) [IsNoetherian S] (M : ModuleCat.{u + 1} R),
      IsIndFiniteEtaleModule.{u} ((constantSheaf S.smallEtaleTopology
        (ModuleCat.{u + 1} R)).obj M)) ∧
    (∀ (S T : Scheme.{u}) [IsNoetherian S] [ConnectedSpace S]
      [IsNoetherian T] [ConnectedSpace T] (c : T ⟶ S) [IsFinite c] [Etale c]
      (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)),
      IsIndFiniteEtaleModule.{u} ((Etale.upperStar (ModuleCat.{u + 1} R) c).obj L) →
        IsIndFiniteEtaleModule L) ∧
    (∀ (S : Scheme.{u}) [IsNoetherian S]
      (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)),
      IsIndFiniteEtaleModule L ↔ ∀ x : S,
        IsIndFiniteEtaleModule.{u} ((Etale.upperStar (ModuleCat.{u + 1} R)
          (torsionLocalSystemComponent S x).ι).obj L)) := by
  sorry

end AlgebraicGeometry.Scheme
