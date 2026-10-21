/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Paper.FiniteSubextensionsDirected
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Profinite derived invariants with algebraic-closure coefficients

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
arithmetic coefficient-topology input
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison).

We retain the finite-field action after restricting scalars. The scalar compatibility
of ordinary derived invariants identifies this with forgetting the C- or B-action after
taking their ordinary derived invariants. All maps are specified on tensor generators
and then derived by the universal property, before evaluation at the one-point set.
- In particular no underived continuous-cochain model is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace Profinite.AlgclInvariantsComparison

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- Bundle the existing finite-field condensed ring, with no change of its tensor structure.
Source: paragraph (3), A = E underline
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
def scalarRing : CategoryTheory.CondensedBar.Ring.{u} :=
  { X := Profinite.continuousMapRingObj E
    mon := inferInstance
    comm := inferInstance }

/-- The regular finite-subextension coefficient module, restricted to the finite field.
Source: paragraph (3), C regarded as an A-module
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
abbrev finiteModule : CategoryTheory.CondensedBar.Modules (scalarRing.{u} ℓ E) :=
  (Mod.comap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)).obj
    (Mod.regular (Profinite.padicAlgClRingObj ℓ))

/-- The existing continuous scalar inclusion E to the norm-topological algebraic closure.
Source: paragraph (3), A to B
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
def normScalarMap : (scalarRing.{u} ℓ E).X ⟶
    Profinite.continuousMapRingObj (PadicAlgCl ℓ) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (algebraMap E (PadicAlgCl ℓ))
        continuous_subtype_val)

/-- The scalar inclusion is a ring-object map, by the existing ring-sheaf construction.
Source: paragraph (3), A to B
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
instance normScalarMap_isMonHom : IsMonHom (normScalarMap.{u} ℓ E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (algebraMap E (PadicAlgCl ℓ))
        continuous_subtype_val)))

/-- The regular all-continuous coefficient module, restricted to the finite field.
Source: paragraph (3), B regarded as an A-module
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
abbrev normModule : CategoryTheory.CondensedBar.Modules (scalarRing.{u} ℓ E) :=
  (Mod.comap (normScalarMap ℓ E)).obj
    (Mod.regular (Profinite.continuousMapRingObj (PadicAlgCl ℓ)))

/-- Forget scalars and evaluate the actual underlying abelian sheaf at the point.
Source: paragraph (3), ev_*
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
def pointEvaluation : CategoryTheory.CondensedBar.Modules (scalarRing.{u} ℓ E) ⥤
    Ab.{u + 1} :=
  Mod.forget (scalarRing ℓ E).X ⋙
    sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
      (evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op (Profinite.of (ULift.{u} PUnit)))

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The ordinary equivariant tensor functor with trivial coefficient action. The underlying
functor is the existing relative tensor; its action is fixed on pure tensors at every test set.
Source: paragraph (3), diagonal action on R tensor_A M
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
structure TensorModel (R : CategoryTheory.CondensedBar.Modules (scalarRing.{u} ℓ E)) where
  functor : CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G ⥤
    CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G
  additive : functor.Additive
  underlying : functor ⋙ CategoryTheory.CondensedBar.forgetAction ≅
    CategoryTheory.CondensedBar.forgetAction ⋙ (curriedTensor _).obj R
  action : ∀ (M : CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G)
    (S : Profinite.{u}) (g : C(S, G))
    (z : Profinite.CondensedAction.sectionModule (scalarRing ℓ E).toMon R S)
    (m : Profinite.CondensedAction.sectionModule (scalarRing ℓ E).toMon M.module S),
    ((underlying.hom.app M).hom.hom.app (op S))
      ((functor.obj M).act S g
        (((underlying.inv.app M).hom.hom.app (op S))
          (Profinite.CondensedAction.InternalBar.pureTensor
            (scalarRing ℓ E).toMon R M.module S z m))) =
      Profinite.CondensedAction.InternalBar.pureTensor
        (scalarRing ℓ E).toMon R M.module S z (M.act S g m)

attribute [instance] TensorModel.additive

section Derived
variable [CategoryTheory.CondensedBar.ActionAbelian (scalarRing.{u} ℓ E) G]
  [IsGrothendieckAbelian.{u + 1}
    (CategoryTheory.CondensedBar.Equivariant (scalarRing.{u} ℓ E) G)]
  [HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Equivariant (scalarRing.{u} ℓ E) G)]
  [HasDerivedCategory.{u + 2} Ab.{u + 1}]

/-- A total left-derived tensor pair, with its universal counit and K-flat normalization.
These conditions determine the pair up to the unique counit-compatible isomorphism.
Source: paragraph (3), derived scalar tensor computed on K-flat models
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
structure DerivedTensor {R : CategoryTheory.CondensedBar.Modules (scalarRing.{u} ℓ E)}
    (T : TensorModel ℓ E G R) where
  functor : DerivedCategory (CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G) ⥤
    DerivedCategory (CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G)
  counit : DerivedCategory.Qh ⋙ functor ⟶
    T.functor.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  universal : functor.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso
      (CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G) (.up ℤ))
  shift : functor.CommShift ℤ
  shiftCounit : letI := shift; NatTrans.CommShift counit ℤ
  kflat : ∀ P : CochainComplex
    (CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G) ℤ,
    CochainComplex.IsKFlatForTotalTensor
      (((CategoryTheory.CondensedBar.forgetAction (A := scalarRing ℓ E) (G := G))
        |>.mapHomologicalComplex (.up ℤ)).obj P) →
    IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

attribute [instance] DerivedTensor.universal DerivedTensor.shift

/-- The universal left-derived transformation of a specified ordinary tensor map.
Source: paragraph (3), z tensor v maps to c(z) tensor v on a K-flat model
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
def derivedCoefficientMap
    {TC : TensorModel ℓ E G (finiteModule ℓ E)}
    {TB : TensorModel ℓ E G (normModule ℓ E)}
    (LC : DerivedTensor ℓ E G TC) (LB : DerivedTensor ℓ E G TB)
    (η : TC.functor ⟶ TB.functor) : LC.functor ⟶ LB.functor :=
  Functor.leftDerivedNatTrans LC.functor LB.functor LC.counit LB.counit
    (HomotopyCategory.quasiIso
      (CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G) (.up ℤ))
    (Functor.whiskerRight (η.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh)

/-- Condensation of a continuous finite-dimensional representation, normalized on every
section, restriction, scalar and generalized group element. This specifies underline W,
including its given norm topology, rather than a discrete action on point sections.
Source: paragraph (3), underline W(P) = C(P,W)
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
structure RepresentationModel (W : Type (u + 1)) [NormedAddCommGroup W] [NormedSpace E W]
    (ρ : G →* Module.End E W) where
  object : CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G
  sections : ∀ S : Profinite.{u}, object.module.X.obj.obj (op S) ≃+ C(S, W)
  restriction : ∀ (S T : Profinite.{u}) (f : T ⟶ S)
    (m : object.module.X.obj.obj (op S)),
    sections T (object.module.X.obj.map f.op m) = (sections S m).comp f.hom.hom
  scalar : ∀ (S : Profinite.{u})
    (r : CategoryTheory.CondensedBar.sectionRing (scalarRing ℓ E) S)
    (m : object.module.X.obj.obj (op S)) (s : S),
    sections S (r • m) s = r.down s • sections S m s
  action : ∀ (S : Profinite.{u}) (g : C(S, G))
    (m : object.module.X.obj.obj (op S)) (s : S),
    sections S (object.act S g m) s = ρ (g s) (sections S m s)

/-- The fully normalized comparison assertion. All tensor, condensation and exact-functor
existence is asserted, not supplied as hypotheses. The coefficient arrow is fixed on every
section, and the comparison is its universal derived transformation followed by ordinary
right-derived invariants and point evaluation.
Source: paragraph (3), the displayed alpha and its isomorphism assertion
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
def Comparison : Prop := by
  refine ∃ (V : CategoryTheory.CondensedBar.Invariants (scalarRing ℓ E) G)
    (hAdd : (pointEvaluation ℓ E).Additive), ?_
  letI := hAdd
  refine ∃ (TC : TensorModel ℓ E G (finiteModule ℓ E))
    (TB : TensorModel ℓ E G (normModule ℓ E))
    (c : finiteModule ℓ E ⟶ normModule ℓ E)
    (η : TC.functor ⟶ TB.functor)
    (LC : DerivedTensor ℓ E G TC) (LB : DerivedTensor ℓ E G TB), ?_
  exact
    (∀ (S : Profinite.{u}) (z : (finiteModule ℓ E).X.obj.obj (op S)),
      ((c.hom.hom.app (op S)) z).down = z.down.val) ∧
    (∀ M : CategoryTheory.CondensedBar.Equivariant (scalarRing ℓ E) G,
      (η.app M).val ≫ (TB.underlying.hom.app M) =
        (TC.underlying.hom.app M) ≫ c ▷ M.module) ∧
    PreservesFiniteLimits (pointEvaluation.{u} ℓ E) ∧
    PreservesFiniteColimits (pointEvaluation.{u} ℓ E) ∧
    LC.functor.IsTriangulated ∧ LB.functor.IsTriangulated ∧
    NatTrans.CommShift
      (Functor.whiskerRight (derivedCoefficientMap ℓ E G LC LB η)
        (V.functor ⋙ pointEvaluation ℓ E).rightDerivedFunctor) ℤ ∧
    ∀ (W : Type (u + 1)) [NormedAddCommGroup W] [NormedSpace E W]
      [FiniteDimensional E W] (ρ : G →* Module.End E W),
      Continuous (fun x : G × W ↦ ρ x.1 x.2) →
      ∃ N : RepresentationModel ℓ E G W ρ,
        IsIso ((Functor.whiskerRight (derivedCoefficientMap ℓ E G LC LB η)
          (V.functor ⋙ pointEvaluation ℓ E).rightDerivedFunctor).app
            ((DerivedCategory.singleFunctor _ 0).obj N.object))
end Derived

/-- The assertion includes the action category's abelian and Grothendieck structures;
localizations use the standard size, so these are not extra mathematical hypotheses.
Source: paragraph (3), ordinary unbounded categories for arbitrary profinite G
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison). -/
def Assertion : Prop := by
  refine ∃ h : CategoryTheory.CondensedBar.ActionAbelian (scalarRing.{u} ℓ E) G, ?_
  letI := h
  refine ∃ g : IsGrothendieckAbelian.{u + 1}
    (CategoryTheory.CondensedBar.Equivariant (scalarRing.{u} ℓ E) G), ?_
  letI := g
  letI := HasDerivedCategory.standard
    (CategoryTheory.CondensedBar.Equivariant (scalarRing.{u} ℓ E) G)
  letI := HasDerivedCategory.standard Ab.{u + 1}
  exact Comparison ℓ E G

/-- After evaluation at the point, the actual inclusion-induced ordinary derived-invariants
comparison is invertible for every continuous finite-dimensional E-representation.
Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3), agent
arithmetic coefficient-topology input; exact literature reference WANTED
(blueprint: lem-sfb-profinite-algcl-derived-invariants-comparison).

Proof:
1. Choose an E-basis of W. Finite-dimensional continuity identifies underline W with A^d
   (lem-sfb-finite-dimensional-linear-map-continuous). Finite free degree-zero modules
   are K-flat (def-pc-kflat-complex). Thus scalar tensor is represented by R^d with the
   original E-matrix action, including d=0.
2. Free A[P] is slice extension by zero of the unit, hence flat by
   lem-pc-sites-modules-j-shriek-flat. Apply lem-sfb-dc-hom-scalar-adjunction and
   lem-sfb-normed-scalar-profinite-hom-acyclic to compute the derived-function columns
   for B and every finite coefficient field, with their evaluation normalization.
3. Finite extensions containing E are cofinal by det-def-sfb-qlbar-condensed-subextensions.
   Use lem-sfb-qlbar-point-abelian-colimit and
   lem-sfb-profinite-derived-functions-filtered-colimit to compute the C column as the
   finite-field-valued functions. Finite coverings and finitely many coordinates permit
   one common field. The column map is inclusion into all norm-continuous functions.
4. Apply lem-sfb-condensed-derived-invariant-bar. Its scalar compatibility permits doing
   the entire calculation after restricting to A. The first face is the given E-action;
   all others are precomposition. Apply lem-sc-first-quadrant-total-column-comparison.
   Finite diagonals and exact point evaluation (lem-zl-contractible-derived-sections-tensor)
   identify the actual derived map with inclusion of finite-field-valued continuous
   cochains into all continuous cochains; no such identification was assumed.
5. In degree zero both modules are W tensor_E Omega, and the invariant kernels coincide.
   Negative cohomology vanishes by the nonnegative bar models.
6. For injectivity in positive degrees, a continuous primitive of a finite-field cocycle
   can be projected continuously E-linearly into that finite field using
   lem-sfb-finite-subfield-continuous-linear-retraction. The projection commutes with the
   E-matrix action and hence with every differential, so yields a finite-field primitive.
7. For surjectivity, lem-sfb-local-norm-algcl-cocycle-descent gives a finite-field cocycle
   cohomologous to the restriction on an open subgroup. Apply
   lem-sfb-continuous-cochain-finite-index-transfer: its naturality preserves the field,
   and corestriction of restriction is the finite positive subgroup index. Divide by that
   index in E to obtain a finite-field cocycle representing the original class.
8. The actual map is a quasi-isomorphism, hence invertible in the ordinary derived
   category (def-weil-abstract-derived-category). Universal derived functors provide the
   specified exact functors and shift-compatible transformation, with their K-flat
   tensor normalization. No internal condensed isomorphism is asserted.
-/
theorem profinite_algcl_derived_invariants_comparison
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Assertion ℓ E G := by
  sorry

end Profinite.AlgclInvariantsComparison
