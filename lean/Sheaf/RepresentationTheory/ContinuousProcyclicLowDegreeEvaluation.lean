/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous procyclic scalar cochains in degrees zero and one

Source: the scalar analytic input to paragraph (3) of the current blueprint's
six-functors direct-images proof; Stacks Tag 0DVG supplies the differential only
(blueprint: lem-sfb-continuous-procyclic-low-degree-evaluation).

The two-element family of coefficient fields expresses an arbitrary coefficient embedding
and both its source and target simultaneously. Taking equal fields and the identity recovers
the single-field assertion. All objects and arrows are pinned by their section coordinates;
no definition chooses unspecified data from the existence theorem. The existing continuous
scalar ring bundles exactly the recorded continuous-map condensed ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar Profinite.CondensedAction

namespace ContinuousCohomology

/-- Section evaluation preserves the zero arrow, with its actual underlying zero linear map.
This structural instance lets us evaluate complexes in the ordinary section-module category.
Source: the abstract module cohomology clause of the scalar input to direct-images paragraph (3)
(blueprint: lem-sfb-continuous-procyclic-low-degree-evaluation). -/
instance continuousScalarSections_preservesZeroMorphisms (F : Type u) [NormedField F]
    (S : Profinite.{u}) :
    (sectionsFunctor (continuousScalarRing F) ⋙
      SheafOfModules.evaluation _ (op S)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Continuous scalar cochains, their generator-evaluation map, its parameter and coefficient
naturality, and the abstract sectionwise cohomology calculation in degrees zero and one.
The coefficient fields need not be complete. `Bool` labels an arbitrary pair of fields
and `j` an arbitrary continuous field embedding over the specified isometric embeddings.
The section-coordinate equivalences, scalar and restriction equations specify precisely
all continuous functions, with the internal module structure of the dependency.

Source: current blueprint, direct-images proof paragraph (3), agent-supplied scalar
analytic input; Stacks Tag 0DVG, continuous cochain differential
(blueprint: lem-sfb-continuous-procyclic-low-degree-evaluation).

Proof, following the eight DAG steps:
1. Descend matching continuous functions along a finite jointly surjective cover after
   taking its product with H^q. The map is a compact-Hausdorff quotient by
   lem-sfb-compact-hausdorff-surjection-quotient. The norm topology on the p-adic integers
   is their inverse-limit topology by lem-sfb-integers-profinite-tower, applied to Q_l.
   Surjectivity gives uniqueness. The empty parameter has just its zero section.
2. Pointwise multiplication through the parameter gives the internal module action by
   sk-def-sfb-sheaf-tensor and sk-def-sfb-module-objects. Every continuous face fixes the
   parameter, so the signed differential is linear and commutes with restrictions.
3. Pair faces (i,j), i<j, with (j-1,i). Disjoint substitutions commute; adjacent merges
   agree by associativity. Their opposite signs cancel, proving d squared zero. Degree
   zero and negative degrees vanish by the prescribed conventions.
4. Evaluation along s |-> (s,1) is continuous and linear. Its degree-zero component is
   the identity and the remaining components are zero. Every chain-map equation has
   both sides zero, since the target differentials and the source d^0 vanish.
5. Restriction and coefficient postcomposition commute with evaluation pointwise and
   with every finite signed sum. Thus the actual maps of complexes have a commuting
   coefficient square, including empty parameter sets.
6. For an additive f, put a(s)=f(s,1). Additivity gives f(s,n)=n*a(s). Residue representatives
   of t modulo l^m converge to t. Continuity and the isometric coefficient embedding
   show f(s,t)=t*a(s) by uniqueness of limits. Both limits already exist as values of
   continuous maps, so no completeness assumption is used.
7. Conversely t*a(s) is jointly continuous and additive and evaluates to a(s). These
   formulas give mutually inverse linear maps over C(S,F), also for empty S.
8. H^0 is the scalar module and evaluation is its identity. The degree-one differential
   is f(s,y)-f(s,x+y)+f(s,x), so its kernel is exactly the additive families. Its incoming
   image is zero. The target has zero differentials. Ordinary module kernel/image
   homology therefore gives the two claimed isomorphisms, without taking any closure.
-/
theorem exists_continuousProcyclicLowDegreeEvaluation (ell : ℕ) [Fact ell.Prime]
    (F : Bool → Type u) [∀ b : Bool, NormedField (F b)]
    (iota : ∀ b : Bool, ℚ_[ell] →+* F b)
    (hiota : ∀ b : Bool, Isometry (iota b))
    (j : F false →+* F true) (hj : Continuous j)
    (hjQ : j.comp (iota false) = iota true) :
    ∃ (U K : ∀ b : Bool, CochainComplex (Modules (continuousScalarRing (F b))) ℤ)
      (e : ∀ (b : Bool) (n : ℕ) (S : Profinite.{u}),
        sections (continuousScalarRing (F b)) ((U b).X (n : ℤ)) S ≃+
          C(S × (Fin n → ℤ_[ell]), F b))
      (k : ∀ (b : Bool) (n : ℕ) (_ : n ≤ 1) (S : Profinite.{u}),
        sections (continuousScalarRing (F b)) ((K b).X (n : ℤ)) S ≃+ C(S, F b))
      (epsilon : ∀ b : Bool, U b ⟶ K b),
      (∀ b : Bool,
        (∀ n : ℤ, n < 0 → IsZero ((U b).X n)) ∧
        (∀ n : ℤ, (n < 0 ∨ 1 < n) → IsZero ((K b).X n)) ∧
        (U b).d 0 1 = 0 ∧
        (∀ n m : ℤ, (K b).d n m = 0) ∧
        (∀ (n : ℕ) (S : Profinite.{u})
          (a : sectionRing (continuousScalarRing (F b)) S)
          (x : sections (continuousScalarRing (F b)) ((U b).X (n : ℤ)) S)
          (s : S) (t : Fin n → ℤ_[ell]),
          e b n S (a • x) (s, t) = a.down s * e b n S x (s, t)) ∧
        (∀ (n : ℕ) (hn : n ≤ 1) (S : Profinite.{u})
          (a : sectionRing (continuousScalarRing (F b)) S)
          (x : sections (continuousScalarRing (F b)) ((K b).X (n : ℤ)) S) (s : S),
          k b n hn S (a • x) s = a.down s * k b n hn S x s) ∧
        (∀ (n : ℕ) (S T : Profinite.{u}) (v : T ⟶ S)
          (x : sections (continuousScalarRing (F b)) ((U b).X (n : ℤ)) S)
          (s : T) (t : Fin n → ℤ_[ell]),
          e b n T (((U b).X (n : ℤ)).X.obj.map v.op x) (s, t) =
            e b n S x (v s, t)) ∧
        (∀ (n : ℕ) (hn : n ≤ 1) (S T : Profinite.{u}) (v : T ⟶ S)
          (x : sections (continuousScalarRing (F b)) ((K b).X (n : ℤ)) S) (s : T),
          k b n hn T (((K b).X (n : ℤ)).X.obj.map v.op x) s = k b n hn S x (v s)) ∧
        (∀ (n : ℕ) (S : Profinite.{u})
          (x : sections (continuousScalarRing (F b)) ((U b).X (n : ℤ)) S)
          (s : S) (t : Fin (n + 1) → ℤ_[ell]),
          e b (n + 1) S ((((U b).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom.hom.app (op S)) x)
            (s, t) = e b n S x (s, fun a ↦ t a.succ) +
              ∑ a : Fin (n + 1), (-1 : ℤ) ^ (a.val + 1) •
                e b n S x (s, Fin.contractNth a (· + ·) t)) ∧
        (∀ (S : Profinite.{u})
          (x : sections (continuousScalarRing (F b)) ((U b).X 0) S) (s : S),
          k b 0 (by decide) S ((((epsilon b).f 0).hom.hom.app (op S)) x) s =
            e b 0 S x (s, Fin.elim0)) ∧
        (∀ (S : Profinite.{u})
          (x : sections (continuousScalarRing (F b)) ((U b).X 1) S) (s : S),
          k b 1 (by decide) S ((((epsilon b).f 1).hom.hom.app (op S)) x) s =
            e b 1 S x (s, fun _ ↦ 1)) ∧
        (∀ n : ℤ, (n < 0 ∨ 1 < n) → (epsilon b).f n = 0) ∧
        (∀ S : Profinite.{u},
          ∃ L :
            LinearMap.ker (((sectionsFunctor (continuousScalarRing (F b)) ⋙
              SheafOfModules.evaluation _ (op S)).map ((U b).d 1 2)).hom) ≃ₗ[
                sectionRing (continuousScalarRing (F b)) S]
              sections (continuousScalarRing (F b)) ((K b).X 1) S,
            (∀ x, L x = (((epsilon b).f 1).hom.hom.app (op S)) x.val) ∧
            (∀ (x : sections (continuousScalarRing (F b)) ((U b).X 1) S),
              x ∈ LinearMap.ker (((sectionsFunctor (continuousScalarRing (F b)) ⋙
                SheafOfModules.evaluation _ (op S)).map ((U b).d 1 2)).hom) ↔
                ∀ (s : S) (t t' : ℤ_[ell]),
                  e b 1 S x (s, fun _ ↦ t + t') =
                    e b 1 S x (s, fun _ ↦ t) + e b 1 S x (s, fun _ ↦ t')) ∧
            (∀ (a : sections (continuousScalarRing (F b)) ((K b).X 1) S)
              (s : S) (t : ℤ_[ell]),
              e b 1 S (L.symm a).val (s, fun _ ↦ t) =
                iota b (t : ℚ_[ell]) * k b 1 (by decide) S a s)) ∧
        (∀ (S : Profinite.{u}) (n : ℤ), n = 0 ∨ n = 1 →
          IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).map
            (((sectionsFunctor (continuousScalarRing (F b)) ⋙
              SheafOfModules.evaluation _ (op S)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map (epsilon b))))) ∧
      ∃ (uMap :
          ((Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
            (continuousScalarRing (F false)).X).mapHomologicalComplex (.up ℤ)).obj (U false) ⟶
          ((Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
            (continuousScalarRing (F true)).X).mapHomologicalComplex (.up ℤ)).obj (U true))
        (kMap :
          ((Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
            (continuousScalarRing (F false)).X).mapHomologicalComplex (.up ℤ)).obj (K false) ⟶
          ((Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
            (continuousScalarRing (F true)).X).mapHomologicalComplex (.up ℤ)).obj (K true)),
        (∀ (n : ℕ) (S : Profinite.{u})
          (x : sections (continuousScalarRing (F false)) ((U false).X (n : ℤ)) S)
          (s : S) (t : Fin n → ℤ_[ell]),
          e true n S (((uMap.f (n : ℤ)).hom.app (op S)) x) (s, t) =
            j (e false n S x (s, t))) ∧
        (∀ (n : ℕ) (hn : n ≤ 1) (S : Profinite.{u})
          (x : sections (continuousScalarRing (F false)) ((K false).X (n : ℤ)) S) (s : S),
          k true n hn S (((kMap.f (n : ℤ)).hom.app (op S)) x) s =
            j (k false n hn S x s)) ∧
        ((Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
          (continuousScalarRing (F false)).X).mapHomologicalComplex (.up ℤ)).map
            (epsilon false) ≫ kMap =
          uMap ≫ ((Mod.forget
            (D := Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
            (continuousScalarRing (F true)).X).mapHomologicalComplex (.up ℤ)).map
              (epsilon true) := by
  sorry

end ContinuousCohomology
