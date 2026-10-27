/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.AlgebraicGeometry.GeometricStalkToposPoint
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Geometric stalks of Zariski-to-étale module pullback

Source: Stacks Project, Tags 04HX (`lemma-describe-etale-local-ring`),
05V5 (`lemma-pullback-stalk`), and the proof of 08H8 (`lemma-epsilon-flat`)
(blueprint: lem-sfb-etale-zariski-module-geometric-stalk).

The comparison record specifies the module action on neighbourhood germs and normalizes
its linear isomorphism by the tensor-pullback adjunction unit. No quasi-coherence is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The existing pointed-neighbourhood colimit of the étale structure sheaf.
Source: Stacks 04HX (blueprint: lem-sfb-etale-zariski-module-geometric-stalk). -/
abbrev etaleStructureGeometricStalk {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) : CommRingCat.{u} :=
  pointedEtaleStalk ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩ t

/-- The additive stalk functor on modules over the actual étale structure sheaf.
This is the recorded pointed-neighbourhood colimit applied to the underlying additive sheaf.
Source: Stacks 05V5 (blueprint: lem-sfb-etale-zariski-module-geometric-stalk). -/
abbrev etaleStructureModuleAdditiveStalk {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    SmallEtaleModules T ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (smallEtaleModuleRing T) ⋙ (pointSmallEtale t).sheafFiber

/-- Witnesses for the module comparison, including its canonical scalar action.
The action equation identifies the H-action with the structure-ring stalk action transported
by α, on all neighbourhood germs. The unit equation fixes the tensor comparison, rather than
choosing an arbitrary natural automorphism. Tensor factors are written H first, using the
usual symmetry to express M_x tensor_R H as an H-module.
Source: Stacks 05V5, applied in 08H8
(blueprint: lem-sfb-etale-zariski-module-geometric-stalk). -/
structure EtaleZariskiModuleStalkComparison {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (c : ZariskiEtaleModuleContext T) (H : Type u) [CommRing H]
    [Algebra (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω))) H]
    (α : etaleStructureGeometricStalk t ≃+* H) where
  /-- The transported stalk action, characterized by the following germ equation. -/
  [module : ∀ M : T.Modules,
    Module H ((etaleStructureModuleAdditiveStalk t).obj (c.extension.obj M))]
  /-- Scalar multiplication on every pointed neighbourhood induces the stalk action. -/
  scalar_germ : ∀ (M : T.Modules) (V : T.Etale)
      (v : (pointSmallEtale t).fiber.obj V) (r : Γ(V.left, ⊤))
      (m : (c.extension.obj M).val.obj (op V)),
    (pointSmallEtale t).toPresheafFiber V v (c.extension.obj M).val.presheaf (r • m) =
      @SMul.smul H ((etaleStructureModuleAdditiveStalk t).obj (c.extension.obj M))
        (module M).toSMul
        (α ((pointSmallEtale t).toPresheafFiber V v T.etaleStructurePresheaf r))
        ((pointSmallEtale t).toPresheafFiber V v (c.extension.obj M).val.presheaf m)
  /-- The isomorphism of H-modules, for every Zariski module. -/
  comparison : ∀ M : T.Modules,
    ((etaleStructureModuleAdditiveStalk t).obj (c.extension.obj M)) ≃ₗ[H]
      TensorProduct (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω))) H
        ((RingedSpace.moduleStalkFunctor T.toRingedSpace
          (t (IsLocalRing.closedPoint Ω))).obj M)
  /-- Naturality for all module morphisms. -/
  naturality : ∀ (M N : T.Modules) (h : M ⟶ N)
      (m : (etaleStructureModuleAdditiveStalk t).obj (c.extension.obj M)),
    comparison N ((etaleStructureModuleAdditiveStalk t).map (c.extension.map h) m) =
      TensorProduct.map LinearMap.id
        ((RingedSpace.moduleStalkFunctor T.toRingedSpace
          (t (IsLocalRing.closedPoint Ω))).map h).hom (comparison M m)
  /-- The canonical comparison sends the pullback-unit germ of m to 1 tensor m_x. -/
  unit_germ : ∀ (M : T.Modules) (W : T.Opens)
      (hx : t (IsLocalRing.closedPoint Ω) ∈ W)
      (w : (pointSmallEtale t).fiber.obj ((AlgebraicGeometry.gabberOpenEtale T).obj W))
      (m : Γ(M, W)),
    comparison M
        ((pointSmallEtale t).toPresheafFiber _ w (c.extension.obj M).val.presheaf
          (((c.adjunction.unit.app M).app W) m)) =
      TensorProduct.tmul (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω))) (1 : H)
        (M.presheaf.germ W (t (IsLocalRing.closedPoint Ω)) hx m)

/-- The étale local ring is the strict henselization relative to the residue separable
closure in Ω, and arbitrary module pullbacks have the canonical tensor stalk comparison.
The open-germ equation asserts R-algebra compatibility. The pointed-evaluation equation
selects the canonical strict-henselization identification relative to the chosen embedding
of its residue field into Ω, including when that residue closure is smaller than Ω.

Source: Stacks 04HX, 05V5, and the proof of 08H8
(blueprint: lem-sfb-etale-zariski-module-geometric-stalk).

Proof:
1. Choose an affine open about x. By affine stalk localization its localized coordinate
ring is R. Shrink pointed étale neighbourhoods into this open and then to affine ones.
Cofilteredness and the full-subcategory colimit lemma justify these restrictions and a
small representative system (lem-weil-pbc-affine-open-stalk-localization,
lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink,
lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered,
lem-weil-pbc-colimit-initial-full-subcategory,
lem-weil-pbc-affine-etale-essentially-small-cover).
2. Translate affine pointed neighbourhoods into residue triples. Étale residue extensions
are finite separable, so their embeddings into Ω factor through the relative separable
closure K. The affine spectrum correspondence identifies arrows as well as objects
(def-weil-pbc-etale-residue-triples, lem-weil-pbc-etale-residue-field-extension-separable,
def-weil-pbc-relative-separable-closure, def-weil-affine-spectrum).
3. Apply lem-weil-pbc-strict-henselization-triples to identify this colimit with the
specified presentation of R^sh. The map on fractions is the germ of the numerator divided
by the germ of the denominator; this proves the open-germ equation. The pointings give
the evaluation equation, so the identification respects the chosen residue embedding.
4. The image under epsilon of the geometric topos point is the ordinary point x:
on opens its skyscraper is E when x belongs to the open and the singleton otherwise.
The adjunction with germs identifies its inverse image with the ordinary stalk
(lem-fix-geometric-stalk-topos-point, lem-trf-zariski-etale-tensor-sections).
5. Apply lem-sfb-ringed-topos-pullback-stalk (05V5) to this ringed morphism and any M.
Compose its tensor comparison with the ring identification from step 3. This produces
the indicated scalar action, linear isomorphism, and unit-germ normalization. Naturality
of the pullback-stalk comparison gives h_x tensor 1, written 1 tensor h_x here. No
quasi-coherence is used at any step. -/
theorem etaleZariski_module_geometric_stalk
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T)
    [Algebra (IsLocalRing.ResidueField (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))) Ω]
    (hΩ : algebraMap
      (IsLocalRing.ResidueField (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))) Ω =
      (T.descResidueField (stalkClosedPointTo t)).hom)
    [Algebra (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))
      (separableClosure
        (IsLocalRing.ResidueField (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))) Ω)]
    [IsScalarTower (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))
      (IsLocalRing.ResidueField (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω))))
      (separableClosure
        (IsLocalRing.ResidueField (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))) Ω)]
    (H : Type u) [CommRing H]
    [Algebra (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω))) H]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u}
      (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))
      (separableClosure
        (IsLocalRing.ResidueField (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))) Ω) H) :
    ∃ c : ZariskiEtaleModuleContext T,
      ∃ α : etaleStructureGeometricStalk t ≃+* H,
        (∀ (W : T.Opens) (hx : t (IsLocalRing.closedPoint Ω) ∈ W)
            (w : (pointSmallEtale t).fiber.obj ((AlgebraicGeometry.gabberOpenEtale T).obj W))
            (r : Γ(T, W)),
          α ((pointSmallEtale t).toPresheafFiber _ w T.etaleStructurePresheaf
              (T.restrictFunctorΓ.inv.app (op W) r)) =
            algebraMap (T.presheaf.stalk (t (IsLocalRing.closedPoint Ω))) H
              (T.presheaf.germ W (t (IsLocalRing.closedPoint Ω)) hx r)) ∧
        (∀ (V : T.Etale) (v : (pointSmallEtale t).fiber.obj V) (r : Γ(V.left, ⊤)),
          (P.residueMap (α ((pointSmallEtale t).toPresheafFiber V v
            T.etaleStructurePresheaf r))).val =
              (v.left.appTop ≫ (ΓSpecIso (.of Ω)).hom) r) ∧
        Nonempty (EtaleZariskiModuleStalkComparison t c H α) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
