/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSized
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement

/-!
# Integral normalization data for rational monodromy realization

Source: Bhatt--Scholze, Definition 6.8.3, Proposition 6.8.4(1),(4),(6),
and the proof of Corollary 6.8.5
(blueprint: def-sfb-monodromy-realization-data).

The integral model is specified by a limit cone over finite etale local systems,
with the quotient maps and monodromy prescribed on the geometric fibre. Compatibility
on lattice-preserving maps fixes the rational realization independently of a lattice.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme

/-- A connected topologically Noetherian qcqs base with geometric point and a profinite
model of its etale fundamental group. All group actions are the fibre-functor actions.
Source: Bhatt--Scholze, proof of Corollary 6.8.5
(blueprint: def-sfb-monodromy-realization-data). -/
structure SfMonodromyPoint (T : Scheme.{u}) where
  /-- Connectedness. -/
  connected : ConnectedSpace T
  /-- Quasi-compactness. -/
  compact : CompactSpace T
  /-- Quasi-separatedness. -/
  quasiSeparated : QuasiSeparatedSpace T
  /-- Only the underlying space is Noetherian. -/
  noetherian : TopologicalSpace.NoetherianSpace T
  /-- The algebraically closed field of the geometric point. -/
  Ω : Type u
  /-- Its field structure. -/
  field : Field Ω
  /-- Algebraic closedness. -/
  closed : IsAlgClosed Ω
  /-- The geometric point. -/
  point : Spec (.of Ω) ⟶ T
  /-- The profinite fundamental group. -/
  group : ProfiniteGrp.{u}
  /-- Its actions on the finite etale fibres. -/
  actions : ∀ P, MulAction group ((FiniteEtale.fiber point).obj P)
  /-- The group is the fundamental group of this fibre functor. -/
  fundamental : IsFundamentalGroup (FiniteEtale.fiber point) group

attribute [instance] SfMonodromyPoint.field SfMonodromyPoint.closed
  SfMonodromyPoint.actions SfMonodromyPoint.fundamental

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The already defined jointly continuous finite-dimensional representation category,
using the identity profinite model. Source: Bhatt--Scholze, Corollary 6.8.5
(blueprint: def-sfb-monodromy-realization-data). -/
abbrev SfContinuousRepresentations {T : Scheme.{u}} (p : SfMonodromyPoint T) :=
  galoisCoefficientRepresentations l E p.group (ContinuousMulEquiv.refl _)

/-- Rational sheaf modules over continuous functions. Source: Bhatt--Scholze,
Definition 6.8.3 (blueprint: def-sfb-monodromy-realization-data). -/
abbrev SfRationalModules (T : Scheme.{u}) :=
  ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ProEtale.lisseFieldSheafSized l E T))

/-- Integral sheaf modules over continuous functions. Source: Bhatt--Scholze,
Definition 6.8.3 (blueprint: def-sfb-monodromy-realization-data). -/
abbrev SfIntegralModules (T : Scheme.{u}) :=
  ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ProEtale.lisseIntegerSheafSized l E T))

/-- Restriction of the representation's scalars to the valuation ring.
Source: Bhatt--Scholze, proof of Corollary 6.8.5
(blueprint: def-sfb-monodromy-realization-data). -/
abbrev sfIntegralRepresentationModule {T : Scheme.{u}} {p : SfMonodromyPoint T}
    (V : SfContinuousRepresentations l E p) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) :=
  (ModuleCat.restrictScalars (Padic.coefficientExtensionIntegers l E).subtype).obj
    ((forget₂ (Rep.{u + 1} E p.group) (ModuleCat.{u + 1} E)).obj V.obj)

/-- A stable finite free lattice inside a representation. Spanning over `E` says that
its canonical scalar extension is `V`; the inclusion is part of the submodule data.
Source: Bhatt--Scholze, proof of Corollary 6.8.5
(blueprint: def-sfb-monodromy-realization-data). -/
structure SfInvariantLattice {T : Scheme.{u}} {p : SfMonodromyPoint T}
    (V : SfContinuousRepresentations l E p) where
  /-- The actual submodule, not an abstract module isomorphic to one. -/
  submodule : Submodule (Padic.coefficientExtensionIntegers l E)
    (sfIntegralRepresentationModule l E V)
  /-- Finite generation. -/
  finite : Module.Finite (Padic.coefficientExtensionIntegers l E) submodule
  /-- Freeness, including rank zero. -/
  free : Module.Free (Padic.coefficientExtensionIntegers l E) submodule
  /-- Its scalar extension spans the original vector space. -/
  spans : Submodule.span E (Set.range (fun b : submodule ↦ (b.val : V.obj.V))) = ⊤
  /-- Stability under the given action. -/
  stable : ∀ (g : p.group) (b : submodule), V.obj.ρ g b.val ∈ submodule

/-- The positive-level lattice quotient `B/ϖ^(n+1)B` as a valuation-ring module.
Source: Bhatt--Scholze, Proposition 6.8.4(1)
(blueprint: def-sfb-monodromy-realization-data). -/
abbrev sfLatticeQuotient {T : Scheme.{u}} {p : SfMonodromyPoint T}
    {V : SfContinuousRepresentations l E p} (B : SfInvariantLattice l E V) (n : ℕ) :=
  ModuleCat.of (Padic.coefficientExtensionIntegers l E)
    (B.submodule ⧸ (Padic.coefficientExtensionIdeal l E (n + 1) •
      (⊤ : Submodule (Padic.coefficientExtensionIntegers l E) B.submodule)))

/-- The quotient projection, keeping its canonical formula on lattice elements.
Source: Bhatt--Scholze, Proposition 6.8.4(1)
(blueprint: def-sfb-monodromy-realization-data). -/
abbrev sfLatticeQuotientMk {T : Scheme.{u}} {p : SfMonodromyPoint T}
    {V : SfContinuousRepresentations l E p} (B : SfInvariantLattice l E V) (n : ℕ)
    (b : B.submodule) : sfLatticeQuotient l E B n :=
  Submodule.Quotient.mk b

/-- Forgetting the module action commutes with the geometric fibre; this is the
canonical filtered-colimit comparison. Source: Stacks 03Q0, Bhatt--Scholze 6.8.4(1)
(blueprint: def-sfb-monodromy-realization-data). -/
def sfModuleFiberToSet {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  letI : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1}
        (Padic.coefficientExtensionIntegers l E))) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  ((pointSmallEtale p.point).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E)))).inv.app F

/-- The finite-level sheaves, pulled to the pro-etale site, with their underlying
abelian-group structure. Source: Bhatt--Scholze, Proposition 6.8.4(1)
(blueprint: def-sfb-monodromy-realization-data). -/
abbrev sfMonodromyAbDiagram (T : Scheme.{u})
    (F : ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  F ⋙ ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) T ⋙
    sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        AddCommGrpCat.{u + 1})

/-- A normalization on one lattice. Its finite levels and transition maps are
characterized by their geometric fibres and the specified fundamental-group action.
The integral module is their inverse limit, with the usual action of constant scalars.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(4) and Corollary 6.8.5
(blueprint: def-sfb-monodromy-realization-data). -/
structure SfLatticeNormalization {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group)
    (J : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T)
    (V : SfContinuousRepresentations l E p) (B : SfInvariantLattice l E V) where
  /-- The finite locally constant etale systems. -/
  etale : ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
  /-- The underlying set sheaves are finite locally constant. -/
  flc : ∀ n, IsLisseEtaleSheafOfSets
    (galoisUnderlyingSetSheaf _ (etale.obj (op n)))
  /-- The prescribed module fibres. -/
  fiber : ∀ n, (((pointSmallEtale p.point).sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj (etale.obj (op n))) ≅
    sfLatticeQuotient l E B n
  /-- The transition sends the residue of b to the residue of b. -/
  transition : ∀ (n m : ℕ) (h : m ≤ n) (b : B.submodule),
    (fiber m).hom ((((pointSmallEtale p.point).sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).map
      (etale.map (homOfLE h).op)) ((fiber n).inv (sfLatticeQuotientMk l E B n b))) =
        sfLatticeQuotientMk l E B m b
  /-- Monodromy is the quotient of the given action, using the finite correspondence. -/
  monodromy : ∀ (n : ℕ) (g : p.group) (b : B.submodule),
    (c.γ g).hom.app
        (galoisUnderlyingFLC _ (etale.obj (op n)) (flc n))
        (sfModuleFiberToSet l E p (etale.obj (op n))
          ((fiber n).inv (sfLatticeQuotientMk l E B n b))) =
      sfModuleFiberToSet l E p (etale.obj (op n))
        ((fiber n).inv (sfLatticeQuotientMk l E B n
          ⟨V.obj.ρ g b.val, B.stable g b⟩))
  /-- The integral model, with genuine continuous coefficient action. -/
  integral : SfIntegralModules l E T
  /-- Its limit projections. -/
  projection : (Functor.const ℕᵒᵖ).obj ((SheafOfModules.toSheaf _).obj integral) ⟶
    sfMonodromyAbDiagram l E T etale
  /-- The projections exhibit the integral model as the inverse limit. -/
  isLimit : IsLimit (Cone.mk _ projection)
  /-- The inverse-limit identification respects every constant integral scalar. -/
  scalar : ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E)
      (x : integral.val.obj U),
    (projection.app (op n)).hom.app U
        ((ProEtale.lisseIntegerConstantSized l E T U a) • x) =
      @SMul.smul (Padic.coefficientExtensionIntegers l E)
        (((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) T).obj
            (etale.obj (op n))).obj.obj U) inferInstance a
              ((projection.app (op n)).hom.app U x)
  /-- Rationalization along the actual integral-to-field inclusion gives J(V). -/
  rational : J.obj V ≅ SheafOfModules.changeOfRings.{u, u + 1, u + 1}
    (ProEtale.lisseIntegerToFieldSized l E T) integral

/-- Compatibility of two lattice normalizations on a lattice-preserving equivariant map.
Both the finite-level and rational maps are prescribed, rather than chosen independently.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(4)
(blueprint: def-sfb-monodromy-realization-data). -/
structure SfNormalizationMap {T : Scheme.{u}} {p : SfMonodromyPoint T}
    {c : GaloisLisseFiniteCorrespondence p.point p.group}
    {J : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T}
    {V W : SfContinuousRepresentations l E p} (f : V ⟶ W)
    (B : SfInvariantLattice l E V) (C : SfInvariantLattice l E W)
    (h : ∀ b : B.submodule, f.hom.hom b.val ∈ C.submodule)
    (N : SfLatticeNormalization l E p c J V B)
    (M : SfLatticeNormalization l E p c J W C) where
  /-- The map of integral continuous-coefficient modules. -/
  integral : N.integral ⟶ M.integral
  /-- The compatible maps of finite etale local systems. -/
  levels : N.etale ⟶ M.etale
  /-- The level maps are the reductions of the original equivariant map. -/
  fiber : ∀ (n : ℕ) (b : B.submodule),
    (M.fiber n).hom ((((pointSmallEtale p.point).sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).map
      (levels.app (op n))) ((N.fiber n).inv (sfLatticeQuotientMk l E B n b))) =
        sfLatticeQuotientMk l E C n ⟨f.hom.hom b.val, h b⟩
  /-- The integral map is induced by the compatible level maps on inverse limits. -/
  limit_comm : ∀ n : ℕ,
    (SheafOfModules.toSheaf _).map integral ≫ M.projection.app (op n) =
      N.projection.app (op n) ≫
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) T) ⋙
          sheafCompose (ProEt.topology T)
            (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
              AddCommGrpCat.{u + 1})).map (levels.app (op n))
  /-- Rationalization is the given J(f), under the fixed normalization isomorphisms. -/
  rational_comm : J.map f ≫ M.rational.hom =
    N.rational.hom ≫ SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (ProEtale.lisseIntegerToFieldSized l E T) N.integral integral

/-- A fully faithful exact rational realization with its integral-monodromy
normalization. Linearity is expressed on sections using the constant E scalars;
exactness is in the ambient sheaf-module category. Normalizations for all stable
lattices are chosen simultaneously and commute with every lattice-preserving map.
Source: Bhatt--Scholze, Definition 6.8.3, Proposition 6.8.4(1),(4), Corollary 6.8.5
(blueprint: def-sfb-monodromy-realization-data). -/
structure SfMonodromyRealization {T : Scheme.{u}} (p : SfMonodromyPoint T) where
  /-- The finite-coefficient correspondence, with its prescribed evaluation action. -/
  finiteCorrespondence : GaloisLisseFiniteCorrespondence p.point p.group
  /-- The rational realization functor. -/
  functor : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T
  /-- Full faithfulness in the ambient module category. -/
  fullyFaithful : functor.FullyFaithful
  /-- Additivity on every Hom group. -/
  additive : functor.Additive
  /-- E-linearity, written without choosing a separate scalar structure on the category. -/
  linear : ∀ (V W : SfContinuousRepresentations l E p) (f : V ⟶ W) (a : E)
      (U : T.ProEtᵒᵖ) (x : (functor.obj V).val.obj U),
    (functor.map (a • f)).val.app U x =
      ProEtale.lisseFieldConstantSized l E T U a • (functor.map f).val.app U x
  /-- The images are lisse, including the zero representation. -/
  lisse : ∀ V, (functor.obj V).IsFiniteLocallyFree
  /-- Every short exact sequence of underlying vector spaces has ambient exact image. -/
  exact : ∀ (V W Z : SfContinuousRepresentations l E p) (f : V ⟶ W) (g : W ⟶ Z),
    Function.Injective f.hom.hom → Function.Exact f.hom.hom g.hom.hom →
      Function.Surjective g.hom.hom →
        ∃ w : functor.map f ≫ functor.map g = 0,
          (ShortComplex.mk (functor.map f) (functor.map g) w).ShortExact
  /-- The specified inverse-limit realization of every invariant lattice. -/
  normalization : ∀ (V : SfContinuousRepresentations l E p) (B : SfInvariantLattice l E V),
    SfLatticeNormalization l E p finiteCorrespondence functor V B
  /-- These identifications commute with equivariant lattice maps. By commensurability
  this determines the rational functor independently of every choice of lattice. -/
  naturality : ∀ (V W : SfContinuousRepresentations l E p) (f : V ⟶ W)
      (B : SfInvariantLattice l E V) (C : SfInvariantLattice l E W)
      (h : ∀ b : B.submodule, f.hom.hom b.val ∈ C.submodule),
    Nonempty (SfNormalizationMap l E f B C h (normalization V B) (normalization W C))

end AlgebraicGeometry.Scheme
