/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
import Sheaf.CategoryTheory.InternalActionSitePresentation
import Sheaf.CategoryTheory.CondensedProductActionInflation

/-! # Condensed induction along a split profinite coset projection

Source: main-20261015, direct-image stability proof, paragraph (3), agent-formulated
exact-induction input (external reference WANTED).
(blueprint: lem-sfb-condensed-split-coset-induction).

The section tensor product is presented by finite sums of symbols [p] tensor m,
modulo [ph] tensor m = [p] tensor hm. The presheaf, its restrictions, its
sheafification, the induced action, functoriality, and both adjunction formulas
are specified together. No object is chosen from the postponed existence theorem.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction.SplitCosetInduction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The recorded section ring of the arbitrary condensed ring.
Source: the sectionwise tensor formula in paragraph (3)'s exact-induction input
(blueprint: lem-sfb-condensed-split-coset-induction). -/
abbrev scalar (S : Profinite.{u}) :=
  (InternalAbelianSheafModule.sectionRings (coherentTopology Profinite.{u}) R.X).obj (op S)

/-- The recorded ring sheaf used by module sheafification.
Source: the module-sheafification clause of the exact-induction input
(blueprint: lem-sfb-condensed-split-coset-induction). -/
abbrev ringSheaf :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat RingCat)).obj
    (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) R.X)

variable (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
  (H : Subgroup P)

/-- The continuous inclusion of the subgroup, giving the recorded restriction functor.
Source: subgroup restriction in the exact-induction input
(blueprint: lem-sfb-condensed-split-coset-induction). -/
def inclusion : H →ₜ* P := ⟨H.subtype, continuous_subtype_val⟩

/-- The right-H balancing relations in the direct sum of copies of M(S) indexed by P(S).
This is the usual presentation of A(S)[P(S)] tensor over A(S)[H(S)] with M(S).
Source: step 2 of the exact-induction input
(blueprint: lem-sfb-condensed-split-coset-induction). -/
def relations (M : ActionModule R H) (S : Profinite.{u}) :
    Submodule (scalar R S) (C(S, P) →₀ sectionModule R M.module S) := by
  classical
  exact Submodule.span (scalar R S)
    {z | ∃ (p : C(S, P)) (h : C(S, H)) (m : sectionModule R M.module S),
      z = Finsupp.single (p * ((inclusion P H).toContinuousMap.comp h)) m -
        Finsupp.single p (M.act S h m)}

/-- The actual section tensor product, as its standard generators-and-relations quotient.
Source: the displayed tensor presheaf in the exact-induction input
(blueprint: lem-sfb-condensed-split-coset-induction). -/
abbrev sectionTensor (M : ActionModule R H) (S : Profinite.{u}) :=
  (C(S, P) →₀ sectionModule R M.module S) ⧸ relations R P H M S

/-- The canonical tensor symbol, with no choice of coset representatives.
Source: the symbols [p] tensor m in steps 2--8 of the exact-induction input
(blueprint: lem-sfb-condensed-split-coset-induction). -/
def tensorSymbol (M : ActionModule R H) (S : Profinite.{u})
    (p : C(S, P)) (m : sectionModule R M.module S) : sectionTensor R P H M S := by
  classical
  exact Submodule.Quotient.mk (Finsupp.single p m)

/-- The tensor presheaf, specified by its actual section tensor products and restriction
on their generators. Linearity and finite sums determine the full restriction maps.
Source: step 2 of the exact-induction input
(blueprint: lem-sfb-condensed-split-coset-induction). -/
structure TensorPresheaf (M : ActionModule R H) where
  /-- The presheaf of modules over the existing section-ring presheaf. -/
  presheaf : PresheafOfModules.{u + 1} (ringSheaf R).obj
  /-- Its sections are precisely the balanced tensor products. -/
  sections (S : Profinite.{u}) :
    presheaf.obj (op S) ≃ₗ[scalar R S] sectionTensor R P H M S
  /-- Restriction is induced by coefficient restriction and precomposition. -/
  restriction (S T : Profinite.{u}) (f : T ⟶ S) (p : C(S, P))
      (m : sectionModule R M.module S) :
    sections T (presheaf.map f.op ((sections S).symm (tensorSymbol R P H M S p m))) =
      tensorSymbol R P H M T (p.comp f.hom.hom) ((M.module.X.obj.map f.op).hom m)

/-- An induction functor with its specified tensor presheaf and module sheafification.
The comparison is data, not a selection of an unspecified induced object.
Source: steps 2--3 of the exact-induction input
(blueprint: lem-sfb-condensed-split-coset-induction). -/
structure Construction where
  /-- The prescribed tensor presheaf for every input. -/
  tensor (M : ActionModule R H) : TensorPresheaf R P H M
  /-- The functor on internal equivariant modules. -/
  functor : ActionModule R H ⥤ ActionModule R P
  /-- The underlying module is the recorded module sheafification. -/
  comparison (M : ActionModule R H) :
    (InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) R.X).obj (functor.obj M).module ≅
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj (tensor M).presheaf

variable {R P H}

/-- A tensor symbol in the induced sheaf, via the ordinary sheafification unit.
Source: steps 2--5, the map eta_M in the exact-induction input
(blueprint: lem-sfb-condensed-split-coset-induction). -/
def generator (D : Construction R P H) (M : ActionModule R H) (S : Profinite.{u})
    (p : C(S, P)) (m : sectionModule R M.module S) :
    sectionModule R (D.functor.obj M).module S :=
  ((D.comparison M).inv.val.app (op S))
    ((toSheafify (coherentTopology Profinite.{u}) (D.tensor M).presheaf.presheaf).app
      (op S) (((D.tensor M).sections S).symm (tensorSymbol R P H M S p m)))

variable (R P H)

/-- The exact additive induction functor, normalized by its generators and the two
adjunction formulas. The tensor and sheafification comparisons determine its objects;
the generator formulas determine its action and maps.
Source: all clauses of the exact-induction input to paragraph (3)
(blueprint: lem-sfb-condensed-split-coset-induction). -/
structure Datum extends Construction R P H where
  /-- Induction preserves sums of morphisms. -/
  [additive : functor.Additive]
  /-- Left multiplication induces the condensed action on sheafification. -/
  action (M : ActionModule R H) (S : Profinite.{u}) (g p : C(S, P))
      (m : sectionModule R M.module S) :
    (functor.obj M).act S g (generator toConstruction M S p m) =
      generator toConstruction M S (g * p) m
  /-- Maps are induced by tensoring the given equivariant map. -/
  map {M N : ActionModule R H} (f : M ⟶ N) (S : Profinite.{u}) (p : C(S, P))
      (m : sectionModule R M.module S) :
    ((functor.map f).val.hom.hom.app (op S)).hom (generator toConstruction M S p m) =
      generator toConstruction N S p ((f.val.hom.hom.app (op S)).hom m)
  /-- The left adjunction is to the existing restriction-by-inflation functor. -/
  adjunction : functor ⊣ inflate (R := R) (inclusion P H)
  /-- The forward transpose evaluates at [1] tensor m. -/
  transpose (M : ActionModule R H) (N : ActionModule R P) (f : functor.obj M ⟶ N)
      (S : Profinite.{u}) (m : sectionModule R M.module S) :
    (((adjunction.homEquiv M N f).val.hom.hom.app (op S)).hom m) =
      (f.val.hom.hom.app (op S)).hom (generator toConstruction M S 1 m)
  /-- The inverse transpose extends [p] tensor m to p acting on f(m). -/
  untranspose (M : ActionModule R H) (N : ActionModule R P)
      (f : M ⟶ (inflate (R := R) (inclusion P H)).obj N) (S : Profinite.{u})
      (p : C(S, P)) (m : sectionModule R M.module S) :
    ((((adjunction.homEquiv M N).symm f).val.hom.hom.app (op S)).hom
      (generator toConstruction M S p m)) =
        N.act S p ((f.val.hom.hom.app (op S)).hom m)
  /-- Exactness means preservation of all short exact sequences. -/
  exact : ∀ (C : ShortComplex (ActionModule R H)), C.ShortExact →
    (C.map functor).ShortExact

/-- Induction along a closed subgroup with continuously split profinite right-coset
projection is additive and exact, and left adjoint to restriction with the stated
transpose formulas, for arbitrary internal equivariant modules.

Source: agent-formulated exact-induction input below main-20261015, direct-image
stability, paragraph (3); external reference WANTED
(blueprint: lem-sfb-condensed-split-coset-induction).

Proof:
1. Closed H is profinite. Use lem-sfb-internal-action-site-presentation and
   lem-sfb-condensed-product-action-inflation (with a trivial second factor) to
   compute equivariant kernels and cokernels on underlying module sheaves.
2. Form finite sums [p] tensor m modulo the displayed balancing relations.
   Restriction sends [p] tensor m to [p composed with t] tensor t*m. Left
   multiplication preserves these relations and commutes with restrictions.
   Equivariant sheafification, using def-weil-presheaf-modules-sheafification,
   produces the induced object. The formula [p] tensor m maps to [p] tensor u(m)
   gives its additive functor structure by uniqueness of sheafification extensions.
3. Evaluate F at [1] tensor m. Balancing and equivariance give H-equivariance.
4. Conversely send [p] tensor m to p*f(m). H-equivariance proves balancing;
   naturality gives a presheaf map and sheafification extends it uniquely.
5. The two formulas are inverse: evaluate the first composite at [1] tensor m;
   for the second use P-equivariance on each [p] tensor m, then uniqueness of
   extension. The same formulas prove naturality in both variables.
6. The continuous section s gives p=s(q(p))*h_p with unique continuous H-valued
   h_p. Thus P(S) is the disjoint union of s(x)*H(S), indexed by x in C(S,P/H).
7. Send [p] tensor m to the x=q(p) summand with entry h_p*m; its inverse sends
   m in the x summand to [s composed with x] tensor m. Balancing proves that the
   first map is well-defined and the two maps are inverse.
8. These normal forms commute with restriction. When distinct indices become
   equal, their entries add, as in the restriction of finite formal sums.
9. Direct sums of copies of a map have the direct sum of its kernels. These
   identify presheaf kernels naturally. Apply exact module sheafification
   (lem-weil-pbc-ringed-site-module-sheafification-exact) and the action-site
   kernel description to obtain preservation of equivariant kernels.
10. The explicit adjunction preserves cokernels by their universal property.
    A short exact sequence in the abelian action category is a kernel/cokernel
    pair, so induction preserves it. No finite-coset or discrete-module condition
    entered the argument. Trivial groups, H=P, the zero ring and empty test sets
    obey the same formulas.
-/
theorem exists_datum [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hclosed : IsClosed (H : Set P)) [T2Space (P ⧸ H)]
    [TotallyDisconnectedSpace (P ⧸ H)] (s : C(P ⧸ H, P))
    (hs : Function.RightInverse s (QuotientGroup.mk : P → P ⧸ H)) :
    Nonempty (Datum R P H) := by
  sorry

end Profinite.CondensedAction.SplitCosetInduction
