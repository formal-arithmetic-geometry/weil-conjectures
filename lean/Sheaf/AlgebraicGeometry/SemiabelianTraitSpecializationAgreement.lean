module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import Sheaf.RingTheory.NormalStrictLocalTraitLifts
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.SemiabelianPrimeToTorsionSchematicDensity

/-! # Agreement of trait specializations of a semiabelian homomorphism

Source: Faltings, Finiteness Theorems for Abelian Varieties over Number Fields,
Chapter II, section 2, Lemma 1 proof, printed pages 10-11. The compatibility input
is the agent-formulated torsion/normality expansion of the valuation reduction.
(blueprint: lem-sfb-semiabelian-trait-specialization-agreement)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Restrict a base-changed group homomorphism along a map of base schemes,
transporting along the specified commuting triangle. This is the underlying
scheme morphism of the canonical restriction, with both ends on the single
chosen pullback along `t`. The only transports are equality and pullback pasting.

Source: Stacks Project, Schemes, fibre products (Tag 01JO); Faltings II section 2,
Lemma 1 proof, the base changes in the valuation comparison.
(blueprint: lem-sfb-semiabelian-trait-specialization-agreement) -/
noncomputable def baseChangeGroupHomAlong
    {S T B : Scheme.{u}} (P Q : Grp (Over S))
    (a : B ⟶ S) (t : T ⟶ S) (r : T ⟶ B) (h : t = r ≫ a)
    (v : (Over.pullback a).mapGrp.obj P ⟶ (Over.pullback a).mapGrp.obj Q) :
    ((Over.pullback t).obj P.X).left ⟶ ((Over.pullback t).obj Q.X).left :=
  (eqToHom (congrArg (fun b => (Over.pullback b).obj P.X) h) ≫
    (Over.pullbackComp r a).hom.app P.X ≫
    (Over.pullback r).map v.hom.hom ≫
    (Over.pullbackComp r a).inv.app Q.X ≫
    eqToHom (congrArg (fun b => (Over.pullback b).obj Q.X) h.symm)).left

/-- Two given trait extensions of the same generic homomorphism have identical
specializations to the common geometric fibre. The generic triangle `hgeneric`
expresses dominance and the induced embedding of the generic residue field.
The triangle `hspecial` expresses the common closed point and compatibility of
the specified residue-field embeddings with the common embedding `es` into `Ω`.
Fields are included alongside DVRs, with their unique point both generic and closed.
Equality is equality of scheme morphisms; the maps already preserve the group laws.

Source: Faltings, Finiteness Theorems for Abelian Varieties over Number Fields,
Chapter II, section 2, Lemma 1 proof, printed pages 10-11; agent-formulated
compatibility input expanding its valuation-ring comparison.
(blueprint: lem-sfb-semiabelian-trait-specialization-agreement)

Proof:
1. Set A to the local ring of S at s. Dominance makes A to R_i injective,
   and both maps are local. Normality makes A a normal domain. Apply
   lem-sfb-normal-strict-local-trait-lifts with the given geometric embeddings:
   obtain a common strict henselization H and dominant local maps H to the strict
   henselizations B_i of R_i, with compatible fraction fields and evaluations in Ω.
   For a field R_i, s is the generic point and A is the generic residue field.
2. For a strictly henselian local C evaluated at its closed geometric point in Ω,
   an etale C-scheme E has E(C) bijective with E_Ω(Ω). Use the subcanonical clause
   of lem-sfb-space-etale-pullback-chart-comparison, then
   lem-weil-pbc-sets-strictly-henselian-open-sections-stalk and
   lem-galois-stalk-representable. Evaluation commutes with H to B_i, so
   E(H) to E(B_i) is bijective as well.
3. Fix a positive integer n nonzero in Ω. It is a unit in H and B_i. Smooth base
   change (lem-pc-proper-base-change) and
   lem-sfb-smooth-group-invertible-multiplication make P_H[n] and Q_H[n] etale,
   compatibly with base change. Lift any geometric n-torsion point x to a section
   a over H and then to a_i over B_i. The sections v_i(a_i) descend uniquely to
   sections b_i of Q_H[n]. Over Frac B_i they equal u(a), so equality descends to
   Frac H by faithful field extension. By lem-pc-closed-imm-base-change the
   equalizers are closed. Injectivity of H to Frac H forces b_1=b_2. Evaluating
   gives agreement of the specializations on every invertible-order torsion point.
4. The equalizer Z in P_Ω of the two specialized maps is closed, using the closed
   diagonal of Q and lem-pc-closed-imm-base-change. By step 3 it contains every
   invertible-order torsion point. The semiabelian, smooth, separated finite-type
   hypotheses persist under base change (lem-pc-proper-base-change and
   lem-pod-separated-finite-type-base-change); finite presentation implies finite
   type. Apply lem-sfb-semiabelian-prime-to-torsion-schematic-density to conclude
   Z=P_Ω as schemes. Hence the two scheme morphisms, and thus homomorphisms, agree.
The statement assumes the extensions and asserts no existence over S. -/
theorem semiabelian_trait_specializations_agree
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (P Q : Grp (Over S)) [IsCommMonObj P.X] [IsCommMonObj Q.X]
    [Smooth P.X.hom] [IsSeparated P.X.hom]
    [LocallyOfFinitePresentation P.X.hom] [QuasiCompact P.X.hom]
    [Smooth Q.X.hom] [IsSeparated Q.X.hom]
    [LocallyOfFinitePresentation Q.X.hom] [QuasiCompact Q.X.hom]
    (hP : HasSemiabelianGeometricFibres P)
    (hQ : HasSemiabelianGeometricFibres Q)
    (uη : (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj P ⟶
      (Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj Q)
    (R L : Fin 2 → Type u) [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsLocalRing (R i)] (hR : ∀ i, IsField (R i) ∨ IsDiscreteValuationRing (R i))
    [∀ i, Field (L i)] [∀ i, Algebra (R i) (L i)] [∀ i, IsFractionRing (R i) (L i)]
    (a : ∀ i, Spec (.of (R i)) ⟶ S)
    (j : ∀ i, S.residueField (genericPoint S) ⟶ CommRingCat.of (L i))
    (hgeneric : ∀ i, Spec.map (j i) ≫ S.fromSpecResidueField (genericPoint S) =
      Spec.map (CommRingCat.ofHom (algebraMap (R i) (L i))) ≫ a i)
    (v : ∀ i, (Over.pullback (a i)).mapGrp.obj P ⟶
      (Over.pullback (a i)).mapGrp.obj Q)
    (hv : ∀ i, baseChangeGroupHomAlong P Q (a i)
      (Spec.map (j i) ≫ S.fromSpecResidueField (genericPoint S))
      (Spec.map (CommRingCat.ofHom (algebraMap (R i) (L i)))) (hgeneric i) (v i) =
      baseChangeGroupHomAlong P Q (S.fromSpecResidueField (genericPoint S))
        (Spec.map (j i) ≫ S.fromSpecResidueField (genericPoint S))
        (Spec.map (j i)) rfl uη)
    (s : S) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (es : S.residueField s →+* Ω)
    (e : ∀ i, IsLocalRing.ResidueField (R i) →+* Ω)
    (hspecial : ∀ i,
      Spec.map (CommRingCat.ofHom es) ≫
        S.fromSpecResidueField s =
      Spec.map (CommRingCat.ofHom ((e i).comp (IsLocalRing.residue (R i)))) ≫ a i) :
    baseChangeGroupHomAlong P Q (a 0)
        (Spec.map (CommRingCat.ofHom es) ≫
          S.fromSpecResidueField s)
        (Spec.map (CommRingCat.ofHom ((e 0).comp (IsLocalRing.residue (R 0)))))
        (hspecial 0) (v 0) =
      baseChangeGroupHomAlong P Q (a 1)
        (Spec.map (CommRingCat.ofHom es) ≫
          S.fromSpecResidueField s)
        (Spec.map (CommRingCat.ofHom ((e 1).comp (IsLocalRing.residue (R 1)))))
        (hspecial 1) (v 1) := by
  sorry

end AlgebraicGeometry
