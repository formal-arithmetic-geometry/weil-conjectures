/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit

/-!
# Underived projection for a closed pro-etale immersion

Source: Stacks Project, proetale.tex, Tags 09AA and 09AH, and sites-modules.tex,
Section 03EK and Tag 03EL. The projection consequence is agent-formulated.
(blueprint: lem-weil-pbc-proetale-closed-underived-projection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ProEtaleClosedProjection

/-- The actual module adjunction is uniquely characterized by its constructed unit
on every section. This fixes adjunction data, rather than choosing an arbitrary
adjunction between the functors.
Source: Stacks, Tags 03D2, 03D3 and 09AA; the canonical adjunct in the statement
(blueprint: lem-weil-pbc-proetale-closed-underived-projection).
Proof: transport the existing pullbackPushforwardAdjunction on the AsSmall model
back along the explicit module equivalences. The right-adjoint comparison is the
sectionwise identity. Evaluation of the transported unit gives inverseSection,
since the model equivalences are inverse on sections and their comparison units
are identities. For uniqueness, two units satisfying this equation agree by
sectionwise extensionality of module morphisms and natural transformations.
An adjunction is determined by its unit: the Hom equivalence sends f to the unit
followed by the right-adjoint image of f, so equal units give equal Hom equivalences,
and their inverses and counits agree. -/
theorem adjunction_exists {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X) :
    ∃! ai : inverse i R ⊣ proEtaleRingedDirectImage i R,
      ∀ (F : Modules R) (V : X.ProEt) (s : F.val.obj (op V)),
        (ai.unit.app F).val.app (op V) s = inverseSection i F V s := by
  sorry

/-- The canonical module adjunction, selected from the unique unit-normalized
characterization. Its data are determined by the actual inverse-image section map.
Source: Stacks, Tags 03D2, 03D3 and 09AA; the canonical adjunct in the statement
(blueprint: lem-weil-pbc-proetale-closed-underived-projection). -/
noncomputable def adjunction {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X) :
    inverse i R ⊣ proEtaleRingedDirectImage i R :=
  Classical.choose (adjunction_exists i R)

/-- The projection map is the specified adjunct of the normalized tensor comparison
followed by the counit on the first factor. No isomorphism or arbitrary map is chosen.
Source: Stacks, Tags 03EL and 09AA; the adjunct formula in the statement
(blueprint: lem-weil-pbc-proetale-closed-underived-projection). -/
noncomputable def projection {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X)
    (M : Modules (inverseRing i R)) (F : Modules R) :
    tensor ((proEtaleRingedDirectImage i R).obj M) F ⟶
      (proEtaleRingedDirectImage i R).obj (tensor M ((inverse i R).obj F)) :=
  ((adjunction i R).homEquiv _ _)
    (comparison i R ((proEtaleRingedDirectImage i R).obj M) F ≫
      tensorMap ((adjunction i R).counit.app M) (𝟙 ((inverse i R).obj F)))

/-- The ring sheaf B regarded as an R-module through the given ring morphism.
Source: Stacks, Section 03EK; the coefficient clause
(blueprint: lem-weil-pbc-proetale-closed-underived-projection). -/
noncomputable abbrev coefficientModule {X : Scheme.{u}} {R B : Rings X} (a : R ⟶ B) :
    Modules R :=
  (restrict a).obj (SheafOfModules.unit (proEtaleModuleCoefficients B))

/-- The coefficient clause expressed using module sheaves and prescribed actions.
The isomorphisms eS and eT identify their restricted R-modules with the actual tensor
objects. Their pure-tensor equations prescribe the B-actions on the second factors.
The isomorphism eB identifies the inverse image of the regular module with the
inverse-image ring, normalized by the actual ring and module units. The B-linear map
p has exactly the original projection as its underlying map. Its target is the actual
direct image over B, so its action is through B to i_*i^{-1}B. This packages B-linearity
without identifying unequal coefficient categories or replacing the projection map.
Source: Stacks, Section 03EK and Tag 03EL; the coefficient clause
(blueprint: lem-weil-pbc-proetale-closed-underived-projection). -/
def CoefficientLinear {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X)
    (M : Modules (inverseRing i R)) (B : Rings X) (a : R ⟶ B) : Prop :=
  ∃ eB : (inverse i R).obj (coefficientModule a) ≅
      (restrict (inverseRingMap i a)).obj
        (SheafOfModules.unit (proEtaleModuleCoefficients (inverseRing i B))),
    (∀ (V : X.ProEt) (b : B.obj.obj (op V)),
      eB.hom.val.app (op ((proEtaleBaseChange i).obj V))
        (inverseSection i (coefficientModule a) V b) =
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app B).hom.app (op V) b) ∧
  ∃ (S : Modules B) (T : Modules (inverseRing i B))
    (eS : (restrict a).obj S ≅
      tensor ((proEtaleRingedDirectImage i R).obj M) (coefficientModule a))
    (eT : (restrict (inverseRingMap i a)).obj T ≅
      tensor M ((inverse i R).obj (coefficientModule a))),
    (∀ (V : X.ProEt)
      (m : ((proEtaleRingedDirectImage i R).obj M).val.obj (op V))
      (b c : B.obj.obj (op V)),
      eS.inv.val.app (op V)
        (pure ((proEtaleRingedDirectImage i R).obj M) (coefficientModule a) V m (c * b)) =
      c • @id (S.val.obj (op V)) (eS.inv.val.app (op V)
        (pure ((proEtaleRingedDirectImage i R).obj M) (coefficientModule a) V m b))) ∧
    (∀ (W : Z.ProEt) (m : M.val.obj (op W))
      (b c : (inverseRing i B).obj.obj (op W)),
      eT.inv.val.app (op W)
        (pure M ((inverse i R).obj (coefficientModule a)) W m
          (eB.inv.val.app (op W) (c * b))) =
      c • @id (T.val.obj (op W)) (eT.inv.val.app (op W)
        (pure M ((inverse i R).obj (coefficientModule a)) W m
          (eB.inv.val.app (op W) b)))) ∧
    ∃ p : S ⟶ (proEtaleRingedDirectImage i B).obj T,
      IsIso p ∧ ∀ (V : X.ProEt)
        (x : (tensor ((proEtaleRingedDirectImage i R).obj M)
          (coefficientModule a)).val.obj (op V)),
        p.val.app (op V) (eS.inv.val.app (op V) x) =
        eT.inv.val.app (op ((proEtaleBaseChange i).obj V))
          ((projection i R M (coefficientModule a)).val.app (op V) x)

/-- The specified projection is invertible, jointly natural, and B-linear under every
commutative coefficient extension. The adjunct uses the actual constructed module
adjunction, fixed by its actual sectionwise unit, with no arbitrary choice and no
hypothesis on coefficients or modules.

Source: Stacks Project, Tags 09AA, 09AH and 03EL; agent-formulated consequence
(blueprint: lem-weil-pbc-proetale-closed-underived-projection).

Proof:
1. Put H = i_*M tensor F and N = M tensor i^{-1}F. The tensor comparison sigma
is invertible by lem-pur-proetale-inverse-image-tensor-comparison. The counit is
invertible by lem-weil-pbc-proetale-ringed-closed-counit, for every adjunction on
these functors. Thus alpha = sigma followed by epsilon_M tensor identity is invertible.
The adjunct formula defining projection is eta_H followed by i_*(alpha).
2. The open restriction of H is zero: inverse image commutes with tensor and the
open restriction of i_*M is zero by lem-weil-pbc-proetale-ringed-open-closed. Tensor
with zero is zero by the sheafified sectionwise construction. Apply the ringed
localization sequence 0 -> j_!j^{-1}H -> H -> i_*i^{-1}H -> 0. Its left term
vanishes, so eta_H is an isomorphism. Quasi-compactness of the open is exactly the
hypothesis required by Tag 09AH.
3. Consequently projection is a composite of isomorphisms, with inverse
 i_*(alpha^{-1}) followed by eta_H^{-1}. Naturality of sigma, the counit and the
unit gives the displayed equation for every pair of module maps.
4. Regard B as an R-module. Applying inverse image to its regular action gives the
unit-normalized eB. Sheafify the sectionwise tensors with the B-action on the B
factor to obtain S and T and their identifications eS and eT. On sections over V,
projection sends m tensor b to m tensor bar(b), where bar is the ring adjunction
unit. Hence projection(m tensor cb) = m tensor bar(c)bar(b), the prescribed target
B-action through B -> i_*i^{-1}B. Locally sections of a sheafified tensor are sums
of pure tensors, so this equality gives a B-linear map p with the specified
underlying projection. Its inverse is B-linear by injectivity of p: apply p to the
two sides of p^{-1}(cy) = c p^{-1}(y). This gives IsIso p, without flatness, finite
presentation, constructibility or any restriction on the ring map. -/
theorem closed_underived_projection {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) (R : Rings X) :
    (∀ (M : Modules (inverseRing i R)) (F : Modules R), IsIso (projection i R M F)) ∧
    (∀ (M M' : Modules (inverseRing i R)) (F F' : Modules R)
      (a : M ⟶ M') (b : F ⟶ F'),
      tensorMap ((proEtaleRingedDirectImage i R).map a) b ≫ projection i R M' F' =
        projection i R M F ≫
          (proEtaleRingedDirectImage i R).map (tensorMap a ((inverse i R).map b))) ∧
    (∀ (M : Modules (inverseRing i R)) (B : Rings X) (a : R ⟶ B),
      CoefficientLinear i R M B a) := by
  sorry

end AlgebraicGeometry.ProEtaleClosedProjection
