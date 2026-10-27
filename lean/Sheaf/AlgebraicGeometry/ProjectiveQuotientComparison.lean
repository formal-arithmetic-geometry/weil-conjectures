/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Mathlib.Topology.Sheaves.LocallySurjective

/-! # Immersion comparison for projective-bundle line quotients

Source: Stacks Project, Morphisms, Tag 01VR, lemma-relatively-very-ample,
proof of (2) implies (4), the comparison open and omitted factorization verification;
Constructions, Tags 01OA and 01OB
(blueprint: lem-trf-projective-quotient-comparison).

The auxiliary definitions only spell out the restriction of the given quotient,
the composite with a map of modules, and the comparison diagram in the statement.
All pullbacks use the section-normalized tensor pullback.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry

open Scheme.Modules

/-- Restriction of q to the inverse image of an open of the base, with the
canonical tensor-pullback identification of its source.
Source: Stacks, Tag 01VR, comparison in (2) implies (4); Tag 0097
(blueprint: lem-trf-projective-quotient-comparison). -/
noncomputable def restrictedLineQuotient {Z X : Scheme.{u}} (g : Z ⟶ X)
    (F : X.Modules) (N : Z.Modules) (q : (tensorPullback g).obj F ⟶ N)
    (V : X.Opens) :
    (tensorPullback (g ∣_ V)).obj ((tensorPullback V.ι).obj F) ⟶
      (tensorPullback (g ⁻¹ᵁ V).ι).obj N :=
  (tensorPullbackSectionComp (g ∣_ V) V.ι).inv.app F ≫
    (eqToIso (congrArg (fun f ↦ (tensorPullback f).obj F)
      (morphismRestrict_ι g V))).hom ≫
    (tensorPullbackSectionComp (g ⁻¹ᵁ V).ι g).hom.app F ≫
    (tensorPullback (g ⁻¹ᵁ V).ι).map q

/-- The quotient q_j induced by alpha_j and the restriction of q.
Source: Stacks, Tag 01VR, comparison in (2) implies (4)
(blueprint: lem-trf-projective-quotient-comparison). -/
noncomputable def inducedLocalLineQuotient {Z X : Scheme.{u}} (g : Z ⟶ X)
    (F : X.Modules) (N : Z.Modules) (q : (tensorPullback g).obj F ⟶ N)
    (V : X.Opens) (E : V.toScheme.Modules)
    (α : E ⟶ (tensorPullback V.ι).obj F) :
    (tensorPullback (g ∣_ V)).obj E ⟶ (tensorPullback (g ⁻¹ᵁ V).ι).obj N :=
  (tensorPullback (g ∣_ V)).map α ≫ restrictedLineQuotient g F N q V

/-- The map beta from the pulled-back E to the tautological line on P(F).
Source: Stacks, Tag 01VR, the comparison open U_j
(blueprint: lem-trf-projective-quotient-comparison). -/
noncomputable def comparisonLineMap {S : Scheme.{u}} {F : S.Modules}
    [F.IsQuasicoherent] (D : TautologicalQuotient F) (E : S.Modules) (α : E ⟶ F) :
    (tensorPullback (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom).obj E ⟶
      D.line :=
  (tensorPullback (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom).map α ≫ D.quotient

/-- The entire comparison over one base open. The cartesian square and quotient
identity specify P(F restricted to V) as the canonical restriction of P(F).
The open U is exactly the stalk-surjectivity locus of beta, and the morphism h
classifies the restriction of beta. The last two identities give the factorization
of r restricted to g inverse V and its composite with h.
Source: Stacks, Tag 01VR, comparison in (2) implies (4); Tags 01OA and 01OB
(blueprint: lem-trf-projective-quotient-comparison). -/
def HasQuotientOpenComparison {Z X : Scheme.{u}} (g : Z ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] (N : Z.Modules)
    (q : (tensorPullback g).obj F ⟶ N) (D : TautologicalQuotient F)
    (r : Z ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData F).relProj)
    (V : X.Opens) (E : V.toScheme.Modules) [E.IsQuasicoherent]
    (α : E ⟶ (tensorPullback V.ι).obj F) (DE : TautologicalQuotient E)
    (i : (g ⁻¹ᵁ V).toScheme ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) : Prop :=
  ∃ tautological : TautologicalQuotient ((tensorPullback V.ι).obj F),
  ∃ inclusion : (SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback V.ι).obj F)).relProj ⟶
      (SymmetricAlgebraSheaf.gradedAlgebraData F).relProj,
  ∃ square : IsPullback inclusion
    (SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback V.ι).obj F)).relProjHom
    (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom V.ι,
  ∃ lineIso : (tensorPullback inclusion).obj D.line ≅ tautological.line,
  ((tensorPullbackSectionComp inclusion
      (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom).hom.app F ≫
        (tensorPullback inclusion).map D.quotient ≫ lineIso.hom =
      (eqToIso (congrArg (fun f ↦ (tensorPullback f).obj F) square.w)).hom ≫
        (tensorPullbackSectionComp
          (SymmetricAlgebraSheaf.gradedAlgebraData
            ((tensorPullback V.ι).obj F)).relProjHom V.ι).hom.app F ≫
          tautological.quotient) ∧
  ∃ restriction : (g ⁻¹ᵁ V).toScheme ⟶
    (SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback V.ι).obj F)).relProj,
  (Classifies tautological (g ∣_ V)
    ((tensorPullback (g ⁻¹ᵁ V).ι).obj N) (restrictedLineQuotient g F N q V) restriction) ∧
  (restriction ≫ inclusion = (g ⁻¹ᵁ V).ι ≫ r) ∧
  ∃ locus : (SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback V.ι).obj F)).relProj.Opens,
  (∀ y, y ∈ locus ↔ Function.Surjective
    ((RingedSpace.moduleStalkFunctor
      (SymmetricAlgebraSheaf.gradedAlgebraData
        ((tensorPullback V.ι).obj F)).relProj.toRingedSpace y).map
      (comparisonLineMap tautological E α))) ∧
  ∃ comparison : locus.toScheme ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
  (Classifies DE
    (locus.ι ≫ (SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback V.ι).obj F)).relProjHom)
    ((tensorPullback locus.ι).obj tautological.line)
    ((tensorPullbackSectionComp locus.ι
      (SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback V.ι).obj F)).relProjHom).hom.app E ≫
      (tensorPullback locus.ι).map (comparisonLineMap tautological E α)) comparison) ∧
  ∃ lift : (g ⁻¹ᵁ V).toScheme ⟶ locus.toScheme,
  (lift ≫ locus.ι = restriction) ∧
  (lift ≫ comparison = i)

/-- Immersion comparison for arbitrary quasi-coherent projective-bundle quotients.
No quasi-compactness, finite-type or local-freeness hypothesis is imposed on g, E_j or F.

Source: Stacks Project, Morphisms, Tag 01VR, lemma-relatively-very-ample,
proof of (2) implies (4), comparison open and omitted verification; Constructions,
Tags 01OA and 01OB (blueprint: lem-trf-projective-quotient-comparison).

Proof:
1. Use lem-trf-projective-bundle-quotient-geometry to identify the restriction of P(F),
its line and quotient with P(F restricted to V_j). It classifies the restricted q.
Functoriality of def-pc-module-pullback identifies the pullback of beta_j with q_j.
2. At a point where beta_j is surjective choose a local frame l of its invertible
range (def-sc-invertible-module), lift its germ, represent the lift on a neighborhood,
and shrink until beta_j(e)=l. Sending a*l to a*e splits beta_j on that neighborhood.
Thus its stalk-surjectivity locus U_j is open, with surjective restricted quotient
by lem-weil-pbc-locally-surjective-iff-stalks. No finite generation of E_j is needed.
3. Apply lem-trf-projective-bundle-quotient-geometry to that quotient to obtain h_j.
4. If r_j(z) lay outside U_j, the image ideal of beta_j at r_j(z), in a line frame,
would be proper and contained in the maximal ideal. The local stalk map
(def-weil-locally-ringed-space-morphism) sends this ideal into the maximal ideal at z.
By lem-weil-pbc-module-stalk-pullback the pullback of beta_j on stalks is extension
of scalars. Every finite sum of images of pure tensors is in that maximal ideal,
so cannot hit 1. This contradicts the surjectivity of q_j. Hence r_j lands in U_j.
5. Factor through U_j using lem-weil-pbc-morphism-factors-through-open-subscheme.
Pullback naturality and uniqueness in lem-trf-projective-bundle-quotient-geometry
show that the composite with h_j classifies q_j, and so equals the given i_j.
6. Apply lem-zl-immersion-cancellation to see that the lift is an immersion.
Composing its closed-then-open factorization with U_j into P_j is an immersion
(def-weil-closed-immersion and def-weil-open-immersion). These P_j cover P(F),
so lem-zl-immersion-near-image-locality proves that r is an immersion. -/
theorem projective_quotient_comparison {Z X : Scheme.{u}} (g : Z ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] (N : Z.Modules) [N.IsInvertible]
    (q : (tensorPullback g).obj F ⟶ N) [Epi q] (D : TautologicalQuotient F)
    (r : Z ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData F).relProj)
    (hr : Classifies D g N q r)
    (J : Type v) (V : J → X.Opens) (hV : iSup V = ⊤)
    (E : (j : J) → (V j).toScheme.Modules) [∀ j, (E j).IsQuasicoherent]
    (α : (j : J) → E j ⟶ (tensorPullback (V j).ι).obj F)
    (DE : (j : J) → TautologicalQuotient (E j))
    (i : (j : J) → (g ⁻¹ᵁ V j).toScheme ⟶
      (SymmetricAlgebraSheaf.gradedAlgebraData (E j)).relProj)
    (hqi : ∀ j, Epi (inducedLocalLineQuotient g F N q (V j) (E j) (α j)))
    (hi : ∀ j, Classifies (DE j) (g ∣_ V j) ((tensorPullback (g ⁻¹ᵁ V j).ι).obj N)
      (inducedLocalLineQuotient g F N q (V j) (E j) (α j)) (i j))
    (himm : ∀ j, IsImmersion (i j)) :
    (∀ j, HasQuotientOpenComparison g F N q D r (V j) (E j) (α j) (DE j) (i j)) ∧
      IsImmersion r := by
  sorry

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
