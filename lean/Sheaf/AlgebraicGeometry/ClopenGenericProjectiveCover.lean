/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Selected generic components of a normal projective scheme

Source: ILO, Travaux de Gabber, Expose X, 2.3, Step 2, diagram (2.c), printed p.151;
Stacks Project, Tag 033M, `lemma-normal-Noetherian`
(blueprint: lem-sfb-clopen-generic-projective-cover).

The open subscheme is specified by equality with the union of the selected components.
Residue degrees always use the algebra structure induced by the indicated morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The components selected by one good generic point over each generic point of the base
form a clopen normal projective cover. The equality of generic-point sets discards repetitions.
No residue-degree hypothesis is imposed on the omitted components.

Source: ILO X 2.3, Step 2, diagram (2.c), printed p.151, component-selection refinement;
Stacks Project, Tag 033M (blueprint: lem-sfb-clopen-generic-projective-cover).

Proof:
1. Projectivity over F implies properness (`lem-kun-projective-implies-proper`) and finite
   type. Spec F is Noetherian: its only ideals are zero and the unit ideal, and its space
   has one point (`pqf-def-locnoeth`). Finite type over a Noetherian scheme makes X
   Noetherian (`lem-weil-pbc-finite-type-over-noetherian`).
2. The normal decomposition (`rem-pc-regular-normal`, clause 2) makes the components a
   finite disjoint family of clopen normal integral opens. The selected union and its
   complementary union are open, so the selected union is clopen and normal. Its inclusion
   is closed: on this open it induces identity stalk maps, and on the open complement
   its structure sheaf is zero (`def-weil-closed-immersion`, `def-weil-open-immersion`).
3. Compose this closed inclusion with a projective embedding of X over F
   (`lem-weil-pbc-closed-immersion-comp`, `def-kun-projective`). This gives projectivity
   of the selected union over F.
4. An irreducible subset cannot cross complementary clopen unions. Its maximality
   therefore identifies the components of the open subscheme with the selected
   components (`def-weil-irreducible-components`). Sobriety (`lem-sc-scheme-sober`)
   identifies their generic points with exactly the chosen points. Each chosen point
   still maps to its designated generic point of B, so every generic fibre is met.
5. Open restriction preserves stalks and residue fields (`def-weil-open-immersion`,
   `def-weil-residue-field`), and preserves the induced residue-field maps. Thus each
   restricted generic point has precisely its assumed finite prime-to-ell degree.
6. Properness of B over e gives separatedness (`def-weil-proper-morphism`). Apply
   `lem-sfb-finite-constant-projective-graph` to the selected projective F-scheme and
   its map to B, with the identity base change. The resulting graph embedding gives
   projectivity in both conventions, and hence properness of the restricted map.
7. Its image is closed (`lem-weil-pbc-proper-closed-image`) and contains every generic
   point of B. Each integral summand is the closure of its generic point
   (`def-pc-integral-scheme`, `lem-sc-scheme-sober`, `def-sc-generic-point`). Thus the
   image contains every summand and the map is surjective. -/
theorem clopen_generic_projective_cover
    (e F : Type u) [Field e] [Field F] [Algebra e F] [Module.Finite e F]
    (ell : ℕ) (hell : ell.Prime)
    (B X : Scheme.{u}) (q : B ⟶ Spec (.of e)) (p : X ⟶ Spec (.of F))
    [Nonempty B] [IsProper q]
    (hB : ∃ (n : ℕ) (V : Fin n → B.Opens),
      (∀ i : Fin n, IsIntegral (V i).toScheme) ∧
      Pairwise (fun i j : Fin n ↦ Disjoint (V i) (V j)) ∧ (⨆ i : Fin n, V i) = ⊤)
    [IsHProjective p]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (d : X ⟶ B)
    (hbase : d ≫ q = p ≫ Spec.map (CommRingCat.ofHom (algebraMap e F)))
    (c : genericPoints B → genericPoints X)
    (hc : ∀ b : genericPoints B, d (c b).val = b.val)
    (hdegree : ∀ b : genericPoints B, ∃ n : ℕ,
      @FieldExtension.degree (B.residueField (d (c b).val)) (X.residueField (c b).val)
        _ _ (d.residueFieldMap (c b).val).hom.toAlgebra = (n : WithTop ℕ) ∧
      n.Coprime ell) :
    ∃ U : X.Opens,
      (U : Set X) = ⋃ b : genericPoints B, (genericPoints.component (c b)).val ∧
      IsClopen (U : Set X) ∧
      (∀ x : U.toScheme, IsDomain (U.toScheme.presheaf.stalk x) ∧
        IsIntegrallyClosed (U.toScheme.presheaf.stalk x)) ∧
      IsHProjective (U.ι ≫ p) ∧
      (∀ b : genericPoints B, ∃ x : U.toScheme, (U.ι ≫ d) x = b.val) ∧
      IsHProjective (U.ι ≫ d) ∧ IsProjectiveBundle (U.ι ≫ d) ∧ Surjective (U.ι ≫ d) ∧
      (∀ x ∈ genericPoints U.toScheme,
        (U.ι ≫ d) x ∈ genericPoints B ∧ ∃ n : ℕ,
          @FieldExtension.degree (B.residueField ((U.ι ≫ d) x)) (U.toScheme.residueField x)
            _ _ ((U.ι ≫ d).residueFieldMap x).hom.toAlgebra = (n : WithTop ℕ) ∧
          n.Coprime ell) ∧
      U.ι '' genericPoints U.toScheme = Set.range (fun b : genericPoints B ↦ (c b).val) := by
  sorry

end AlgebraicGeometry
