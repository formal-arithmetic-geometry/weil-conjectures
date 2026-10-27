/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Sheaf.SixFunctors.ClassicalDefinition
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
import WeilConjectures.AlgebraicGeometry.ZariskiClosedImmersionConnectedRestriction
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.GabberH0EtaleCriterion

/-! # Henselian-pair comparison in degree zero

Source: blueprint main-20261015, Henselian-pair comparison in degree zero;
Stacks Project, Tag 0A0C, lemma-h0-proper-over-henselian-pair
(blueprint: sk-thm-pbc-henselian-h0).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The inclusion of the closed fibre over the quotient by `J`, constructed as the
first projection of the scheme-theoretic fibre product. No henselian or properness
hypothesis is needed to construct this map.
Source: Stacks Project, Tag 0A0C, lemma-h0-proper-over-henselian-pair, setup
(blueprint: sk-thm-pbc-henselian-h0). -/
noncomputable def henselianPairClosedFibreι
    (A : Type u) [CommRing A] (J : Ideal A) {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of A)) :
    pullback f (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)).op) ⟶ Z :=
  pullback.fst f (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)).op)

/-- Restriction on global sections to the closed fibre: evaluate the set-valued
inverse-image adjunction unit at the identity object over `Z`, then identify its
base change with the identity object over the closed fibre, using the second
projection of the pullback of an identity.
Source: Stacks Project, Tag 0A0C, canonical comparison map, and Tag 09ZF, unit notation
(blueprint: sk-thm-pbc-henselian-h0). -/
noncomputable def henselianPairH0SetRestriction
    (A : Type u) [CommRing A] (J : Ideal A) {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of A)) (F : Sheaf Z.smallEtaleTopology (Type (u + 1))) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 Z))) ⟶
      ((Scheme.etaleSetPullback (henselianPairClosedFibreι A J f)).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙
          (pullback f (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)).op))))) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ (henselianPairClosedFibreι A J f))
      (Type (u + 1)) (Z.smallGrothendieckTopology @Etale)
      ((pullback f
        (Scheme.Spec.map
          (CommRingCat.ofHom (Ideal.Quotient.mk J)).op)).smallGrothendieckTopology @Etale)).unit.app
            F).hom.app
          (op (Scheme.Etale.mk (𝟙 Z))) ≫
    ((Scheme.etaleSetPullback (henselianPairClosedFibreι A J f)).obj F).obj.map
      (MorphismProperty.Over.isoMk
        (asIso (pullback.snd (𝟙 Z) (henselianPairClosedFibreι A J f)))
        (Category.comp_id _)).inv.op

/-- Restriction to the closed fibre of a proper scheme over a henselian pair is
bijective for all set-valued etale sheaves, naturally in the sheaf. The last two
clauses give the corresponding isomorphisms for abelian sheaves and sheaves of
modules over every discrete commutative ring. Module-valued sheaves are the
constant-coefficient encoding of modules over the constant ring sheaf.

Source: blueprint main-20261015, Henselian-pair comparison in degree zero;
Stacks Project, Tag 0A0C, lemma-h0-proper-over-henselian-pair
(blueprint: sk-thm-pbc-henselian-h0).

Proof:
1. The quotient spectrum map is a closed immersion, as is its base change to Z,
   by lem-weil-pbc-spec-quotient-closed-immersion and
   lem-weil-pbc-closed-immersion-base-change. Properness implies quasi-compactness
   and quasi-separatedness over the affine base, so Z is qcqs by
   lem-weil-pbc-qcqs-over-affine and def-weil-proper-morphism.
2. Apply lem-weil-pbc-zariski-h0-proper-henselian-pair (Tag 0A0B) to obtain the
   global-section comparison for every Zariski sheaf of sets on Z.
3. For every finite h : Z' to Z, f after h is proper by clause (c) of
   lem-weil-pbc-finite-morphism-permanence. The fibre-product universal property
   (def-pc-fibre-product) identifies its closed fibre with the base change of i.
   Apply the same Zariski comparison to Z'. No surjectivity of h is required.
4. The two comparisons of steps 2 and 3 meet the hypotheses of
   lem-weil-pbc-gabber-h0-etale-criterion (Tag 09ZF). It gives bijectivity of the
   canonical unit on global sections for every set sheaf. The terminal-object
   transport in henselianPairH0SetRestriction is an isomorphism, so preserves it.
5. The units clause (0) of lem-weil-pbc-sets-etale-inverse-image-composition-units
   gives naturality in F; naturality of restriction along the terminal-object
   isomorphism gives precisely the displayed equality. Bijectivity then implies
   naturality of the inverse comparison as well.
6. By lem-weil-pbc-etale-inverse-image-algebraic-structures, forgetting abelian
   structure identifies the abelian inverse image and its unit with the set ones.
   Thus its section homomorphism is bijective and hence an isomorphism. By
   prop-weil-pbc-inverse-image-modules-exact, clauses (1)--(3), the same statement
   holds for constant-ring modules, with the same unit after forgetting scalars.
   A bijective linear map is an isomorphism, and the naturality from step 5
   restricts to abelian and module morphisms. -/
theorem henselian_pair_h0
    (A : Type u) [CommRing A] (J : Ideal A) [HenselianRing A J]
    (Z : Scheme.{u}) (f : Z ⟶ Spec (.of A)) [IsProper f] :
    (∀ F : Sheaf Z.smallEtaleTopology (Type (u + 1)),
      Function.Bijective (henselianPairH0SetRestriction A J f F)) ∧
    (∀ (F G : Sheaf Z.smallEtaleTopology (Type (u + 1))) (α : F ⟶ G),
      α.hom.app (op (Scheme.Etale.mk (𝟙 Z))) ≫ henselianPairH0SetRestriction A J f G =
        henselianPairH0SetRestriction A J f F ≫
          ((Scheme.etaleSetPullback (henselianPairClosedFibreι A J f)).map α).hom.app
            (op (Scheme.Etale.mk (𝟙
              (pullback f (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)).op)))))) ∧
    (∀ G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsIso (Etale.globalSectionsUpperStarMap AddCommGrpCat.{u + 1}
        (henselianPairClosedFibreι A J f) G)) ∧
    (∀ (R : Type (u + 1)) [CommRing R]
      (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)),
      IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} R)
        (henselianPairClosedFibreι A J f) M)) := by
  let q := Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)).op
  let i := henselianPairClosedFibreι A J f
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst f q))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated f
  have hrange : Set.range i = f ⁻¹' PrimeSpectrum.zeroLocus (J : Set A) := by
    change Set.range (pullback.fst f q) = _
    rw [Scheme.Pullback.range_fst]
    exact congrArg (fun S ↦ f ⁻¹' S) (Etale.range_specMap_quotientMk J)
  have hconn (X' : Scheme.{u}) (h : X' ⟶ Z) [IsFinite h]
      (C : Set X') (hC : IsClosed C) (hC' : IsIrreducible C) :
      IsConnected (C ∩ h ⁻¹' Set.range i) := by
    rw [hrange]
    exact (h ≫ f).isConnected_inter_preimage_zeroLocus J hC hC'
  have hZar := zariski_closed_immersion_connected_restriction i (fun x ↦ by
    simpa using hconn Z (𝟙 Z) (closure ({x} : Set Z)) isClosed_closure
      (isIrreducible_singleton.closure))
  have hFinite (X' : Scheme.{u}) (h : X' ⟶ Z) [IsFinite h] := by
    let : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace h
    let : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated h
    exact zariski_closed_immersion_connected_restriction (pullback.snd i h) (fun x ↦ by
      rw [Scheme.Pullback.range_snd]
      exact hconn X' h (closure ({x} : Set X')) isClosed_closure
        (isIrreducible_singleton.closure))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F
    have hb := gabber_h0_etale_criterion i hZar hFinite F
    let e : (MorphismProperty.Over.pullback @Etale ⊤ i).obj
        (Scheme.Etale.mk (𝟙 Z)) ≅ Scheme.Etale.mk (𝟙 (pullback f q)) :=
      MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Z) i)) (Category.comp_id _)
    have ht : IsIso (((Scheme.etaleSetPullback i).obj F).obj.map e.inv.op) :=
      inferInstance
    change Function.Bijective
      ((((Scheme.etaleSetPullback i).obj F).obj.map e.inv.op) ∘ _)
    exact (ConcreteCategory.bijective_of_isIso
      (((Scheme.etaleSetPullback i).obj F).obj.map e.inv.op)).comp hb
  · intro F G α
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
      (Z.smallGrothendieckTopology @Etale)
      ((pullback f q).smallGrothendieckTopology @Etale)
    have hn := congrArg (fun k ↦ k.hom.app (op (Scheme.Etale.mk (𝟙 Z))))
      (adj.unit.naturality α)
    change α.hom.app _ ≫ (adj.unit.app G).hom.app _ =
      (adj.unit.app F).hom.app _ ≫
        ((Scheme.etaleSetPullback i).map α).hom.app _ at hn
    change α.hom.app _ ≫ ((adj.unit.app G).hom.app _ ≫ _) =
      ((adj.unit.app F).hom.app _ ≫ _) ≫ _
    rw [← Category.assoc, hn, Category.assoc, Category.assoc]
    congr 1
    exact (((Scheme.etaleSetPullback i).map α).hom.naturality _).symm
  · intro G
    exact Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_of_henselianRing
      J f i (pullback.snd f q) (IsPullback.of_hasPullback f q) G
  · intro R _ M
    exact Etale.isIso_globalSectionsUpperStarMap_of_henselianRing
      R J f i (pullback.snd f q) (IsPullback.of_hasPullback f q) M

end AlgebraicGeometry
