module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.Mathlib.RingTheory.LocalRing.Basic
import Sheaf.FieldTheory.FamilyCommonExtensionFields
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Stein factorization of an algebraic space over an affine scheme

Source: Stacks Project, More on Morphisms of Spaces, Tags 0A1C and 0A19
(blueprint: lem-sfb-space-stein-factorization-affine).

Global functions are actual compatible regular functions on the existing small affine
etale model. The evaluation morphism is normalized by its restriction to every such chart.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pointwise commutative ring structure on compatible regular functions.
Source: Stacks, Properties of Spaces, Tag 03G7
(blueprint: lem-sfb-space-stein-factorization-affine). -/
instance steinGlobalFunctionsCommRing {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CommRing (RingCat.sectionsSubring X.smallStructureRings.obj) :=
  @Subring.toCommRing (∀ T : X.SmallEtaleModelᵒᵖ, X.smallStructureSheaf.obj.obj T)
    inferInstance (RingCat.sectionsSubring X.smallStructureRings.obj)

/-- The ring of compatible regular functions on the small affine etale model.
The affine charts form a basis of the small etale site, so these are precisely
its structure-sheaf global sections, with pointwise ring operations.
Source: Stacks, Properties of Spaces, Tag 03G7, and More on Morphisms of Spaces,
Tag 0A1C (blueprint: lem-sfb-space-stein-factorization-affine). -/
abbrev steinGlobalFunctions {S : Scheme.{u}} (X : AlgebraicSpace S) : CommRingCat.{u} :=
  .of (RingCat.sectionsSubring X.smallStructureRings.obj)

/-- Restriction of a global function to a chart in the small affine model.
Source: Stacks, Tags 03G7 and 0A1C
(blueprint: lem-sfb-space-stein-factorization-affine). -/
def steinChartRestriction {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : X.SmallEtaleModel) :
    X.steinGlobalFunctions ⟶ X.smallStructureSheaf.obj.obj (op T) :=
  CommRingCat.ofHom
    { toFun := fun b ↦ b.val (op T)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The second Stein map is the spectrum of the existing pullback on compatible
regular functions; no choice of an algebra homomorphism enters this construction.
Source: Stacks, More on Morphisms of Spaces, Tags 0A19 and 0A1C
(blueprint: lem-sfb-space-stein-factorization-affine). -/
def steinAffineProjection (A : Type u) [CommRing A]
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec (.of A))))) :
    Spec X.steinGlobalFunctions ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (affineGlobalScalar A
    (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))) (Iso.refl _) X f))

/-- A proper algebraic space over an arbitrary affine scheme has the canonical Stein
factorization: the second map is integral, the evaluation map is proper, and every
field-valued fibre remains nonempty and connected after every field extension.
The first clause identifies evaluation on every affine etale chart; the second is
factorization of the given map. `ConnectedSpace` includes nonemptiness.

Source: Stacks, More on Morphisms of Spaces, Tag 0A1C, clauses (1), (2), (4),
and Tag 0A19, surjectivity (blueprint: lem-sfb-space-stein-factorization-affine).

Proof:
1. Apply lem-sfb-space-affine-target-global-functions with the identity on global
   functions to construct q. Its chart restrictions are the displayed evaluation
   maps. Apply injectivity of that bijection to obtain f = pi q.
2. The affine source makes pi separated (lem-weil-pbc-affine-source-morphism-separated).
   Proper cancellation (lem-sfb-space-proper-cancellation) makes q proper. Its closed
   diagonal is quasi-compact by lem-sfb-space-closed-subspace-proper.
3. The base is qcqs (lem-weil-pbc-affine-scheme-qcqs). Apply
   lem-sfb-space-proper-noetherian-approximation and then
   lem-sfb-space-affine-limits-schematic-stages. On a final tail the bases are affine
   Noetherian, by lem-weil-pbc-finite-type-over-noetherian and
   pqf-lem-affine-open-locnoeth.
4. The structure modules at these stages are coherent by
   lem-sfb-space-noetherian-coherent-acc. Apply lem-sfb-proper-space-coherent-ext-finite
   in degree zero to two structure modules. By lem-weil-pbc-derived-single-fully-faithful,
   their Hom is the global-functions module, by evaluation at one. Thus it is finite.
5. By lem-sfb-space-limit-sections every global function descends to a stage. The
   monic equation there (lem-weil-pbc-finite-algebra-is-integral) pulls back, proving
   integrality over A without a Noetherian hypothesis on A.
6. At a prime of B form its localized ring and strict henselization with separably
   closed residue field, using def-weil-pbc-localization-at-prime,
   lem-weil-pbc-separable-closure-exists-galois, lem-weil-pbc-strict-henselization-triples
   and lem-sc-strict-henselization-faithfully-flat. Flatness of localization and
   composition (lem-weil-pbc-localization-flat, lem-weil-pbc-flat-ring-map-comp,
   lem-weil-pbc-flat-ring-map-iff-flat-affine) allow flat base change; properness is
   preserved by lem-sfb-space-proper-base-change.
7. Apply lem-sfb-space-flat-higher-image-base-change in degree zero. Since q pulls
   global functions back identically, the structure map on the henselian base change
   identifies its global-functions ring with the strict henselization H.
8. The idempotent/clopen correspondence (lem-sfb-space-global-idempotent-clopen)
   and lem-weil-pbc-local-ring-idempotent-zero-one make this space nonempty connected.
9. Properness makes its image closed. The image formula of lem-a1-space-point-open-calculus
   then makes its closed fibre nonempty, using def-weil-closed-immersion and
   lem-sfb-space-proper-composition.
10. The henselian terminology of def-weil-pbc-henselian-terminology and
    lem-sfb-space-henselian-proper-clopen-lift make the closed fibre connected.
11. Finally lem-sfb-space-sepclosed-components-base-change,
    lem-trf-family-common-extension-field and lem-pc-field-extension-surjective
    transfer nonemptiness and connectedness to every field extension of every
    field-valued fibre. The empty space has B = 0 and no field-valued points of Spec B. -/
theorem steinFactorization_affine (A : Type u) [CommRing A]
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))))
    (hf : MapIsProper f) :
    ∃ q : X ⟶ schemeSpace
        (Over.mk (specULiftZIsTerminal.from (Spec X.steinGlobalFunctions))),
      (∀ T : X.SmallEtaleModel,
        (yoneda.preimage ((X.smallEtaleInclusion.obj T).obj.hom ≫ q.hom.hom)).left =
          (X.etaleForget.obj (X.smallEtaleInclusion.obj T)).toSpecΓ ≫
            Spec.map (steinChartRestriction X T)) ∧
      q.hom.hom ≫ yoneda.map
        (Over.homMk
          (V := Over.mk (specULiftZIsTerminal.from (Spec (.of A))))
          (steinAffineProjection A X f)
          (specULiftZIsTerminal.hom_ext _ _)) = f.hom.hom ∧
      IsIntegralHom (steinAffineProjection A X f) ∧ MapIsProper q ∧
      ∀ (K : Type u) [Field K] (z : Spec (.of K) ⟶ Spec X.steinGlobalFunctions)
        (L : Type u) [Field L] [Algebra K L],
        ConnectedSpace (Point (Limits.pullback q.hom
          ((Scheme.fppfTopology.over (Spec (.of (ULift.{u} ℤ)))).yoneda.map
            (Over.homMk
              (U := Over.mk (specULiftZIsTerminal.from (Spec (.of L))))
              (V := Over.mk (specULiftZIsTerminal.from (Spec X.steinGlobalFunctions)))
              (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ z)
              (specULiftZIsTerminal.hom_ext _ _)))).obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
