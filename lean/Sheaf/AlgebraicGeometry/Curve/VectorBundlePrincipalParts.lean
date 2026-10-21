/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AdelicDifferentials
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting
import Sheaf.AlgebraicGeometry.ModuleSheafCoproductLocalSupport
import Sheaf.Paper.ModuleCupFlasqueAcyclicity
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import Mathlib.RingTheory.Etale.Kaehler

/-! # Principal parts of a vector bundle on a regular curve

Source: Tate, Residues of differentials on curves, §3 pp. 156–157 and §4 p. 157;
finite locally free extension of the local construction
(blueprint: lem-pc-vector-bundle-principal-parts).

We use the existing generic skyscraper and principal-parts sheaf. The sectionwise
finite-support identification below identifies the latter with the direct sum of
closed-point skyscrapers, including its restriction maps. Cohomology is the right
derived functor on module sheaves, not the abelian-sheaf `Modules.H`.
-/

@[expose] public section

universe u w₁ w₂

set_option autoImplicit false

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

/-- The canonical generic-germ morphism of a module, obtained from the identity of its
actual generic stalk using the existing stalk–skyscraper adjunction.
Source: Tate §3 pp. 156–157, first arrow of the residue sequence, with finite locally
free coefficients (blueprint: lem-pc-vector-bundle-principal-parts). -/
noncomputable def vectorBundleToGeneric (E : X.Modules) :
    E ⟶ skyscraper (genericPoint X) (E.presheaf.stalk (genericPoint X)) :=
  toSkyscraper (LinearMap.id : E.presheaf.stalk (genericPoint X) →ₗ[X.functionField]
    E.presheaf.stalk (genericPoint X))

/-- The generic skyscraper map induced by a module morphism, using its actual stalk map.
Source: Tate §3 pp. 156–157, functoriality with coefficients
(blueprint: lem-pc-vector-bundle-principal-parts). -/
noncomputable def vectorBundleGenericMap {E F : X.Modules} (f : E ⟶ F) :
    skyscraper (genericPoint X) (E.presheaf.stalk (genericPoint X)) ⟶
      skyscraper (genericPoint X) (F.presheaf.stalk (genericPoint X)) :=
  toSkyscraper (f.stalkLinearMap (genericPoint X) ∘ₗ
    skyscraperStalkEval (genericPoint X) (E.presheaf.stalk (genericPoint X)))

/-- The standard degree-zero right-derived identification for module global sections.
Source: Stacks Tag 01DZ; Tate §3 pp. 156–157, the H⁰ identification
(blueprint: lem-pc-vector-bundle-principal-parts). -/
noncomputable def vectorBundleModuleH0Iso :
    RingedSpace.moduleCohomology X.toRingedSpace 0 ≅
      RingedSpace.globalSectionsFunctor X.toRingedSpace :=
  letI : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedZeroIsoSelf

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]
  [Algebra k X.functionField] [IsFunctionFieldAlgebra k X]

/-- Restriction of scalars on the actual generic stalk. This is data, using the
specified compatible function-field algebra, without a choice of a vector space.
Source: Tate §3 pp. 156–157, rational sections with coefficients
(blueprint: lem-pc-vector-bundle-principal-parts). -/
noncomputable instance vectorBundleGenericStalkModule (E : X.Modules) :
    Module k (E.presheaf.stalk (genericPoint X)) :=
  Module.compHom (E.presheaf.stalk (genericPoint X)) (algebraMap k X.functionField)

/-- The restriction-of-scalars tower on the generic stalk.
Source: Tate §3 pp. 156–157, rational sections with coefficients
(blueprint: lem-pc-vector-bundle-principal-parts). -/
instance vectorBundleGenericStalkTower (E : X.Modules) :
    IsScalarTower k X.functionField (E.presheaf.stalk (genericPoint X)) :=
  IsScalarTower.of_compHom k X.functionField (E.presheaf.stalk (genericPoint X))

/-- Local finite freeness makes generic germs injective and identifies the local
lattice with the image of the actual specialization map on stalks.
Source: Tate §3 pp. 156–157 and §4 p. 157, finite locally free version
(blueprint: lem-pc-vector-bundle-principal-parts).

Proof (node step 1): on a trivializing open use coordinatewise injectivity of sections
and local rings into the function field (lem-sc-integral-scheme-stalks-in-function-field).
Generic germs commute with the finite sums. Gluing proves injectivity on arbitrary
opens; the colimit description of a stalk identifies its image with stalkLattice. -/
theorem finiteLocallyFree_generic_germs (E : X.Modules) [E.IsFiniteLocallyFree] :
    (∀ U : X.Opens, Function.Injective ((vectorBundleToGeneric E).app U)) ∧
    ∀ x : X,
      Function.Injective (E.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes (Set.mem_univ x))) ∧
      (stalkLattice k (vectorBundleToGeneric E) x : Set (E.presheaf.stalk (genericPoint X))) =
        Set.range (E.presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes (Set.mem_univ x))) := by
  sorry

/-- Every vector in the generic stalk is represented near the generic point.
Source: Tate §3 pp. 156–157, construction of rational sections
(blueprint: lem-pc-vector-bundle-principal-parts).

Proof (node step 2): represent a stalk element by a section on an open neighbourhood.
The generic-germ map of that section is the chosen element, by toSkyscraper_app_apply. -/
theorem vectorBundle_generic_generates (E : X.Modules) :
    ∀ v : E.presheaf.stalk (genericPoint X),
      v ∈ stalkLattice k (vectorBundleToGeneric E) (genericPoint X) := by
  sorry

variable [hN : IsNoetherian X] [hR : IsRegular X] (hdim : topologicalKrullDim X = 1)

include hN hR hdim

/-- The principal-parts resolution and the direct-sum description on every open.
Source: Tate §3 pp. 156–157 and §4 p. 157, finite locally free version
(blueprint: lem-pc-vector-bundle-principal-parts).

Proof:
1. Node step 1 gives the generic injection and identifies the stalk lattices.
2. Represent a generic vector on an open; its complement is finite by
lem-sc-nonempty-open-complement-finite-dim-le-one. All its points are closed by
lem-sc-dim-one-point-outside-open-closed. This gives finite pole sets.
3. Apply lem-pur-module-sheaf-coproduct-local-support. Noetherian opens are quasi-compact,
so locally finite support is finite support. Restriction discards coordinates and is
surjective by extension by zero; the generic skyscraper is also flasque.
4. A rational section with zero principal parts is locally regular at every point;
generic injectivity identifies its local lifts on overlaps, so the lifts glue.
5. At a closed point lift its class to a rational vector and remove the other finitely
many poles. At the generic point remove the finite support and lift by zero. The
stalkwise epimorphism criterion lem-sc-abelian-sheaf-epi-iff-stalk-epi proves exactness. -/
theorem finiteLocallyFree_principalParts_resolution (E : X.Modules) [E.IsFiniteLocallyFree] :
    (residueShortComplex k (vectorBundleToGeneric E)).ShortExact ∧
    TopCat.Presheaf.IsFlasque
      (skyscraper (genericPoint X) (E.presheaf.stalk (genericPoint X))).presheaf ∧
    TopCat.Presheaf.IsFlasque (principalParts k (vectorBundleToGeneric E)).presheaf ∧
    (∀ v : E.presheaf.stalk (genericPoint X),
      {x : closedPoints X | v ∉ stalkLattice k (vectorBundleToGeneric E) x.1}.Finite) ∧
    ∃ e : ∀ U : X.Opens,
      Γ(principalParts k (vectorBundleToGeneric E), U) ≃+
        Π₀ x : {x : closedPoints X // x.1 ∈ U},
          E.presheaf.stalk (genericPoint X) ⧸
            stalkLattice k (vectorBundleToGeneric E) x.1.1,
      (∀ (U : X.Opens) (s : Γ(principalParts k (vectorBundleToGeneric E), U))
        (x : {x : closedPoints X // x.1 ∈ U}),
        e U s x = PrincipalParts.val (vectorBundleToGeneric E) s ⟨x.1.1, x.2⟩) ∧
      ∀ (U W : X.Opens) (h : W ≤ U)
        (s : Γ(principalParts k (vectorBundleToGeneric E), U))
        (x : {x : closedPoints X // x.1 ∈ W}),
        e W ((principalParts k (vectorBundleToGeneric E)).presheaf.map (homOfLE h).op s) x =
          e U s ⟨x.1, h x.2⟩ := by
  sorry

/-- Cohomology of vector bundles is the intersection and the cokernel, naturally.
Source: Tate §3 pp. 156–157 and §4 p. 157, with finite locally free coefficients
(blueprint: lem-pc-vector-bundle-principal-parts).

Proof:
6. The preceding resolution has two flasque terms. Apply
lem-sc-module-cup-flasque-acyclicity and pqf-def-cohomology. Degree zero is global
sections by lem-weil-pbc-right-derived-universal-delta-functor. The long exact sequence
therefore identifies H⁰ with the kernel (the intersection of the stalk lattices),
and H¹ with the cokernel. The displayed formula identifies the inverse cokernel
isomorphism with the actual connecting map, after the finite-support identification.
7. A module morphism sends each local representative to its image, hence preserves
the lattices and sends each quotient class [v] to [f_eta(v)]. It gives a morphism of
short exact sequences. Naturality of the right-derived connecting map gives the
last equation. The degree-zero formula gives naturality of the intersection map. -/
theorem finiteLocallyFree_principalParts_cohomology
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤)))] :
    ∃ e₀ : ∀ (E : X.Modules) [E.IsFiniteLocallyFree],
      (RingedSpace.moduleCohomology X.toRingedSpace 0).obj E ≃+
        ↥(⨅ x : closedPoints X, stalkLattice k (vectorBundleToGeneric E) x.1),
    ∃ e₁ : ∀ (E : X.Modules) [E.IsFiniteLocallyFree],
      ((Π₀ x : closedPoints X, E.presheaf.stalk (genericPoint X) ⧸
        stalkLattice k (vectorBundleToGeneric E) x.1) ⧸
          LinearMap.range (principalPartsMap k (vectorBundleToGeneric E) hdim.le
            (vectorBundle_generic_generates k E))) ≃+
        (RingedSpace.moduleCohomology X.toRingedSpace 1).obj E,
      (∀ (E : X.Modules) [E.IsFiniteLocallyFree]
        (z : (RingedSpace.moduleCohomology X.toRingedSpace 0).obj E),
        (e₀ E z).1 = genericValue (vectorBundleToGeneric E) (U := ⊤) trivial
          (vectorBundleModuleH0Iso.hom.app E z)) ∧
      (∀ (E : X.Modules) [E.IsFiniteLocallyFree]
        (s : Γ(principalParts k (vectorBundleToGeneric E), ⊤)),
        e₁ E (Submodule.Quotient.mk
          (globalPrincipalParts k (vectorBundleToGeneric E) hdim.le
            (vectorBundle_generic_generates k E) s)) =
          ((finiteLocallyFree_principalParts_resolution k hdim E).1.rightDerivedδ
            (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0)
            ((vectorBundleModuleH0Iso.inv.app
              (principalParts k (vectorBundleToGeneric E))) s)) ∧
      (∀ (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree]
        (f : E ⟶ F) (z : (RingedSpace.moduleCohomology X.toRingedSpace 0).obj E),
        (e₀ F ((RingedSpace.moduleCohomology X.toRingedSpace 0).map f z)).1 =
          f.stalkLinearMap (genericPoint X) (e₀ E z).1) ∧
      ∀ (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] (f : E ⟶ F)
        (d : Π₀ x : closedPoints X, E.presheaf.stalk (genericPoint X) ⧸
          stalkLattice k (vectorBundleToGeneric E) x.1),
        ∃ d' : Π₀ x : closedPoints X, F.presheaf.stalk (genericPoint X) ⧸
          stalkLattice k (vectorBundleToGeneric F) x.1,
          (∀ (x : closedPoints X) (v : E.presheaf.stalk (genericPoint X)),
            d x = Submodule.Quotient.mk v →
              d' x = Submodule.Quotient.mk (f.stalkLinearMap (genericPoint X) v)) ∧
          e₁ F (Submodule.Quotient.mk d') =
            (RingedSpace.moduleCohomology X.toRingedSpace 1).map f
              (e₁ E (Submodule.Quotient.mk d)) := by
  sorry

/-- Naturality of the actual short exact sequence and of its quotient coordinates.
Source: Tate §3 pp. 156–157 and §4 p. 157, functorial coefficient construction
(blueprint: lem-pc-vector-bundle-principal-parts).

Proof (node step 7): f sends a local representative s to f(s), so f_eta preserves every
stalk lattice. Send [v] at x to [f_eta(v)] at x. This preserves finite support and
restrictions. On rational vectors the same coordinate formula makes both squares
commute, giving a morphism of the short exact sequences. -/
theorem finiteLocallyFree_principalParts_naturality
    (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] (f : E ⟶ F) :
    ∃ p : principalParts k (vectorBundleToGeneric E) ⟶
      principalParts k (vectorBundleToGeneric F),
      vectorBundleToGeneric E ≫ vectorBundleGenericMap f = f ≫ vectorBundleToGeneric F ∧
      vectorBundleGenericMap f ≫ toPrincipalParts k (vectorBundleToGeneric F) =
        toPrincipalParts k (vectorBundleToGeneric E) ≫ p ∧
      ∀ (U : X.Opens) (s : Γ(principalParts k (vectorBundleToGeneric E), U))
        (x : U) (v : E.presheaf.stalk (genericPoint X)),
        PrincipalParts.val (vectorBundleToGeneric E) s x = Submodule.Quotient.mk v →
          PrincipalParts.val (vectorBundleToGeneric F) (p.app U s) x =
            Submodule.Quotient.mk (f.stalkLinearMap (genericPoint X) v) := by
  sorry

/-- Smooth differentials give the usual rational and local differential lattices.
Source: Stacks Tags 02G1 and 00RT(2), Tag 01UM; Tate §4 p. 157
(blueprint: lem-pc-vector-bundle-principal-parts).

Proof (node step 8): lem-ag-smooth-relative-differentials-finite-locally-free makes
Ω¹ finite locally free. On an affine Spec A, the differential sheaf is the tilde
of Ω[A/k]. Localization of differentials at A minus the point prime and at all
nonzero elements identifies its point and generic stalks with Ω[O_x/k] and Ω[K/k].
The localization formula sends da/s to s⁻¹ d(a/1), so it identifies the actual
specialization map with the canonical differential map. The injectivity of step 1
identifies its image with the stalk lattice. The localSubalgebra used below is the
actual local ring via the existing stalkEquivLocalSubalgebra. -/
theorem finiteLocallyFree_principalParts_differentials [Smooth (X ↘ Spec (.of k))] :
    ∃ e : (X ↘ Spec (.of k)).relativeDifferentials.presheaf.stalk (genericPoint X) ≃ₗ[
        X.functionField] Ω[X.functionField⁄k],
      (∀ (U : X.Opens) (h : genericPoint X ∈ U)
        (s : Γ((X ↘ Spec (.of k)).relativeDifferentials, U)),
        e ((X ↘ Spec (.of k)).relativeDifferentials.presheaf.germ U (genericPoint X) h s) =
          genericValue (X.differentialsToGeneric k) h s) ∧
      ∀ x : X,
        Set.image e (stalkLattice k
          (vectorBundleToGeneric (X ↘ Spec (.of k)).relativeDifferentials) x) =
          Set.range (KaehlerDifferential.map k k (X.localSubalgebra k x) X.functionField) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
