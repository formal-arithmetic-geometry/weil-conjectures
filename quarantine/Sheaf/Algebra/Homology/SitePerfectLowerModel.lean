/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.Paper.WeilTensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract
import Sheaf.Algebra.Homology.SitePerfectModelRestriction
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Local shortening of finite-projective complexes -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

/-- Lower shortening of an upper-bounded strict-perfect chart uses the flat
finitely presented opcycle in its bottom degree.

Source: Stacks Project, Cohomology on Sites, Tag 08G7, final displayed complex,
with Tag 08G0 and Modules on Sites Tag 08FD

Proof: Every term of P is flat, since it is a retract of a finite free sheaf.
Boundedness makes P K-flat. The K-flat descent comparison, resolved degree-zero
test sheaves, and the tensor-cone isomorphism identify ordinary tensor of P with
its derived tensor. The lower Tor vanishing therefore gives exactness in degree
a-1 for every ordinary tensor test and gives P no cohomology below a. The universal
opcycle criterion makes N = coker(P^(a-1) → P^a) flat. A finite presentation of N
is obtained from the two finite-free retract presentations using the matrix
(1-ip, i d q). By Tag 08FD, N is locally a finite free retract. On this cover,
the good truncation of P at a has N in degree a and agrees with P above a.
The quotient chain map is a quasi-isomorphism because P has no cohomology below a.
The truncation has no terms below a, and retains the upper bound b because a ≤ b.
Exact restriction preserves cokernels, cohomology and finite-free retracts.
The canonical successive-restriction comparison identifies the resulting models
with restrictions of E. Viewed as arrows into U, the cover on the slice yields
a covering sieve on U. No sectionwise surjectivity on U is used.
(blueprint: lem-sf-site-perfect-lower-model). -/
theorem exists_strictPerfect_lower_model
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    [hDU : ∀ U : C, HasDerivedCategory.{w'} (SheafOfModules.{max u v}
      (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U))]
    (E : DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)))
    (U : C)
    (P : StrictPerfectCoefficientRepresentationOfUniverses.{u, v, 0} R U
      (ringedSiteDerivedRestrictionOfUniverses
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U E))
    (a b : ℤ) (hab : a ≤ b)
    (hupper : ∀ r : ℤ, b < r → IsZero (P.F.X r))
    (hTor : ∀ (G : SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
        (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((wfSiteDerivedTensor J R).obj
          (E, (DerivedCategory.singleFunctor _ 0).obj G)))) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ P : StrictPerfectCoefficientRepresentationOfUniverses.{u, v, 0} R V
          (ringedSiteDerivedRestrictionOfUniverses
            ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) V E),
          ∀ r : ℤ, r < a ∨ b < r → IsZero (P.F.X r) := by
  classical
  let O := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  obtain ⟨B, _, hB, ⟨eB⟩⟩ :=
    (torAmplitude_iff_exists_bounded_flat_model J R E a b hab).1 hTor
  let F := overFunctor.{max u v} O U
  have : PreservesFiniteLimits F := (overFunctor_exact_ofUniverses O U).1
  have : PreservesFiniteColimits F := (overFunctor_exact_ofUniverses O U).2
  let ep : DerivedCategory.Q.obj P.F ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj B) :=
    P.represents.symm ≪≫ overFunctor_derivedRestrictionIso O U E ≪≫
      F.mapDerivedCategory.mapIso eB ≪≫ F.mapDerivedCategoryFactors.app B
  have hcoh (r : ℤ) (hr : r < a) : IsZero (P.F.homology r) := by
    have hb : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj B).homology r) :=
      (HomologicalComplex.ExactAt.of_isZero (F.map_isZero (hB r (Or.inl hr)))).isZero_homology
    exact hb.of_iso (((DerivedCategory.homologyFunctorFactors _ r).app P.F).symm ≪≫
      (DerivedCategory.homologyFunctor _ r).mapIso ep ≪≫
      (DerivedCategory.homologyFunctorFactors _ r).app _)
  obtain ⟨S, hS, hs⟩ := exists_local_retract_opcycles_of_perfect_tor
    J R E U P a b hab hTor
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨n, ⟨rn⟩⟩ := hs V f hf
  let G := overMap.{max u v} O f
  have : PreservesFiniteLimits G := (overMap_exact_ofUniverses O f).1
  have : PreservesFiniteColimits G := (overMap_exact_ofUniverses O f).2
  let L : CochainComplex (SheafOfModules.{max u v} (O.over V)) ℤ :=
    (G.mapHomologicalComplex (.up ℤ)).obj P.F
  let Q := L.truncGE a
  let p := P.package.map G (overMapUnitIso f)
  have hz (r : ℤ) (hr : r < a) : IsZero (Q.X r) :=
    CochainComplex.isZero_of_isStrictlyGE _ a r hr
  have hu (r : ℤ) (hr : b < r) : IsZero (Q.X r) := by
    exact (G.map_isZero (hupper r hr)).of_iso (L.truncGEXIso a r (by omega))
  have : L.IsGE a := (L.isGE_iff a).2 (fun r hr ↦ by
    rw [L.exactAt_iff_isZero_homology]
    exact (G.map_isZero (hcoh r hr)).of_iso ((P.F.sc r).mapHomologyIso G))
  have : QuasiIso (L.πTruncGE a) := inferInstance
  have hp (r : ℤ) : ∃ m : ℕ,
      Nonempty (Retract (Q.X r) (∏ᶜ fun _ : Fin m ↦ unit (O.over V))) := by
    obtain hr | rfl | hr := lt_trichotomy r a
    · exact ⟨0, ⟨(hz r hr).retract _⟩⟩
    · exact ⟨n, ⟨(Retract.ofIso (L.truncGEXIsoOpcycles r ≪≫
        (P.F.sc r).mapOpcyclesIso G)).trans rn⟩⟩
    · exact ⟨P.package.N r, ⟨(Retract.ofIso (L.truncGEXIso a r hr)).trans
        ⟨p.i r, p.p r, p.splitting r⟩⟩⟩
  choose m rm using hp
  let package : StrictPerfectCoefficientPackageOnSite (O.over V) Q :=
    { N := m
      i r := (rm r).some.i
      p r := (rm r).some.r
      splitting r := (rm r).some.retract }
  let H := overFunctor.{max u v} O V
  have : PreservesFiniteLimits H := (overFunctor_exact_ofUniverses O V).1
  have : PreservesFiniteColimits H := (overFunctor_exact_ofUniverses O V).2
  let K := DerivedCategory.Q.objPreimage E
  let ec := (Functor.mapHomologicalComplexCompIso (overFunctorMap O f) (.up ℤ)).app K
  let e : ringedSiteDerivedRestrictionOfUniverses O V E ≅ DerivedCategory.Q.obj L :=
    (DerivedCategory.Q.mapIso ec).symm ≪≫
    (G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj K)).symm ≪≫
    G.mapDerivedCategory.mapIso P.represents ≪≫ G.mapDerivedCategoryFactors.app P.F
  refine ⟨⟨Q, ⟨a, b, ?_⟩,
    e ≪≫ asIso (DerivedCategory.Q.map (L.πTruncGE a)), package⟩, ?_⟩
  · intro r hr
    exact hr.elim (hz r) (hu r)
  · intro r hr
    exact hr.elim (hz r) (hu r)

end SheafOfModules
