/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.Transport
public import WeilConjectures.SixFunctors.CondensedCompactSupportComposition
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.PurityDiagonalDualizingObject
public import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessTheorem
public import WeilConjectures.AlgebraicGeometry.SfProEtaleProjectionFormula
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Semilinear base change for normalized condensed purity factors

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Steps 1--2 and 5;
sk-thm-purity-transport, Steps 1--4
(blueprint: lem-pur-condensed-semilinear-purity-factors).

All objects and morphisms below belong to the actual derived categories of internal
modules over the pulled-back condensed coefficient rings. The right adjoints are
supplied with their adjunctions; the normalized purity comparison is the unique
counit-preserving comparison with the published explicit smooth adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PurityTransport

variable (ell : ℕ) [Fact ell.Prime]

/-- The four coefficient forms in this node, using the existing coefficient presentation.
The finite case is an actual positive uniformizer quotient, up to ring isomorphism.
Source: the coefficient paragraph
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
def SemilinearCoefficient : Coefficient ell → Prop
  | .finite A _ _ _ => ∃ (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ),
      1 ≤ n ∧ Nonempty (A ≃+* Padic.coefficientExtensionRing ell E.1 n)
  | .integral _ => True
  | .rational _ => True
  | .closure => True
  | .integers => True
  | .rationals => True

variable {ell} {D : WeilConjectures.FiniteFieldDatum.{u}}
  {c : Coefficient ell} {s : SmoothDatum D}

/-- The normalized purity isomorphism for any specified right adjoint of compact support.
This is right-adjoint uniqueness, hence fixes its counit and cannot choose an orientation.
Source: sk-thm-purity-transport, uniqueness clause
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
def semilinearGamma (a : ExplicitAdjunction ell D c s)
    (G : c.ctf ell s.Y.left ⥤ c.ctf ell s.X.left)
    (b : support ell c s.compactification a.support_closed ⊣ G) :
    source ell c s.map s.dim a.source_closed ≅ G :=
  a.adjunction.rightAdjointUniq b

/-- The normalized orientation is the unit component of normalized smooth purity,
with the actual pullback-unit identification of its Tate-line source.
Source: normalized diagonal orientation and sk-thm-purity-transport
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
def semilinearOrientation (a : ExplicitAdjunction ell D c s)
    (G : c.ctf ell s.Y.left ⥤ c.ctf ell s.X.left)
    (b : support ell c s.compactification a.support_closed ⊣ G)
    (hU : property ell c s.Y.left (unit ell c s.Y.left)) :
    c.derivedLine ell s.X.left s.dim ≅ (G.obj ⟨_, hU⟩).obj :=
  (sourceUnit ell c s.map s.dim).symm ≪≫
    (ObjectProperty.ι (property ell c s.X.left)).mapIso
      ((semilinearGamma a G b).app ⟨_, hU⟩)

/-- The restricted inverse image, retaining the published ambient pullback on objects
and maps. Its extra argument supplies membership proofs only.
Source: the native categories and P,Q of the statement
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
def semilinearPull {X Y : Scheme.{u}} (v : X ⟶ Y)
    (h : ∀ K, property ell c Y K → property ell c X
      ((CondensedRing.moduleObjectDerivedPullback (c.obj ell) v).obj K)) :
    c.ctf ell Y ⥤ c.ctf ell X :=
  (property ell c X).lift
    ((property ell c Y).ι ⋙ CondensedRing.moduleObjectDerivedPullback (c.obj ell) v)
    (fun K ↦ h K.obj K.property)

/-- Exceptional exchange is exactly the transpose of inverse compact-support exchange
followed by the pulled-back exceptional counit.
Source: the displayed definition of e_K
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
def semilinearMate {s' : SmoothDatum D}
    (a : ExplicitAdjunction ell D c s) (a' : ExplicitAdjunction ell D c s')
    (G : c.ctf ell s.Y.left ⥤ c.ctf ell s.X.left)
    (G' : c.ctf ell s'.Y.left ⥤ c.ctf ell s'.X.left)
    (b : support ell c s.compactification a.support_closed ⊣ G)
    (b' : support ell c s'.compactification a'.support_closed ⊣ G')
    (P : c.ctf ell s.Y.left ⥤ c.ctf ell s'.Y.left)
    (Q : c.ctf ell s.X.left ⥤ c.ctf ell s'.X.left)
    (B : support ell c s.compactification a.support_closed ⋙ P ≅
      Q ⋙ support ell c s'.compactification a'.support_closed)
    (K : c.ctf ell s.Y.left) : Q.obj (G.obj K) ⟶ G'.obj (P.obj K) :=
  b'.homEquiv _ _ (B.inv.app (G.obj K) ≫ P.map (b.counit.app K))

/-- The degree-zero regular module identifies canonically with the ambient tensor unit.
Source: the coefficient-unit convention
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
def semilinearDerivedUnit (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (X : Scheme.{u}) : unit ell c X ≅ 𝟙_ (c.derived ell X) :=
  DerivedCategory.singleFunctorObjUnitIso
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X))

/-- The actual inverse-projection tensor transpose, in the order f* K tensor omega.
The symmetry is the canonical Koszul symmetry in the derived category; the projection
is the published proper/open composite. Its inverse exists on these inputs.
Source: tensor-map paragraph of the statement
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
def semilinearTensor (a : ExplicitAdjunction ell D c s)
    (G : c.ctf ell s.Y.left ⥤ c.ctf ell s.X.left)
    (b : support ell c s.compactification a.support_closed ⊣ G)
    (N : c.ctf ell s.Y.left) (K : c.ctf ell s.Y.left)
    (hN : N.obj ≅ 𝟙_ (c.derived ell s.Y.left))
    (hT : property ell c s.X.left
      (((CondensedRing.upperStar (c.obj ell) s.map).leftDerivedFunctor.obj K.obj) ⊗
        (G.obj N).obj))
    (hPF : IsIso (CondensedRing.exceptionalProjectionMorphismOfCompactification
      (c.obj ell) s.compactification (G.obj N).obj K.obj)) :
    (((CondensedRing.upperStar (c.obj ell) s.map).leftDerivedFunctor.obj K.obj) ⊗
      (G.obj N).obj) ⟶ (G.obj K).obj :=
  letI := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology s.X.left) Ab.{u + 1})
      (condensedRingObj (c.obj ell) s.X.left))
  letI := hPF
  (b.homEquiv ⟨_, hT⟩ K
    (ObjectProperty.homMk
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification).map (β_ _ _).hom ≫
        inv (CondensedRing.exceptionalProjectionMorphismOfCompactification
          (c.obj ell) s.compactification (G.obj N).obj K.obj) ≫
        ((b.counit.app N).hom ▷ K.obj) ≫
        (hN.hom ▷ K.obj) ≫ (λ_ K.obj).hom))).hom

set_option maxHeartbeats 2000000 in
-- The published coherence witness contains the complete proper/open normalization cube.
/-- The canonical exchange family, extracted before specializing its geometric indices.
The complete normalization predicate stays in H. This factoring avoids expanding the
full six-functor coherence predicate during each geometric specialization.
Source: sk-thm-sf-comp-composition, canonical exchange family
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
@[irreducible] def semilinearExchangeFamily
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k]
    (H : CondensedRing.CompactSupportComposition.Coherent Λ k) :=
  @Exists.choose _ _ (H.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec)

/-- The specified proper/open exchange, before restriction to Dctf. Its full
normalization is retained in the dependency witness H.
Source: canonical compact-support exchange in the statement
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
@[irreducible] def semilinearExchangeModel
    (H : CondensedRing.CompactSupportComposition.Coherent (c.obj ell) D.k)
    (s' : SmoothDatum D) (u : s'.X.left ≅ s.X.left) (v : s'.Y.left ≅ s.Y.left)
    (sq : IsPullback u.hom s'.map s.map v.hom) :
    (localizing ell c s.X.left).ι ⋙
        (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification ⋙
          CondensedRing.moduleObjectDerivedPullback (c.obj ell) v.hom) ≅
      (localizing ell c s.X.left).ι ⋙
        (CondensedRing.moduleObjectDerivedPullback (c.obj ell) u.hom ⋙
          CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) s'.compactification) :=
  semilinearExchangeFamily (c.obj ell) D.k H
    (X := SepFinType.mk s.X) (Y := SepFinType.mk s.Y)
    (X' := SepFinType.mk s'.X) (Y' := SepFinType.mk s'.Y)
    (f := SepFinType.homMk (Over.homMk s.map (comp_over s.map _)))
    (f' := SepFinType.homMk (Over.homMk s'.map (comp_over s'.map _)))
    sq s.compactification s'.compactification

/-- Pullback of the coefficient unit, computed by exact pullback on the
single degree-zero regular module.
Source: canonical coefficient identifications of the statement
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
def semilinearUnitPull {X Y : Scheme.{u}} (v : X ⟶ Y) :
    (CondensedRing.moduleObjectDerivedPullback (c.obj ell) v).obj (unit ell c Y) ≅
      unit ell c X :=
  ((CondensedRing.upperStar (c.obj ell) v).singleFunctorCompLeftDerivedFunctorIso).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar (c.obj ell) v)).symm

/-- The monoidal and composition identification in the tensor square, before applying
1 tensor e_1. Both factors are the published derived comparison maps.
Source: canonical source identification in the second displayed formula
(blueprint: lem-pur-condensed-semilinear-purity-factors). -/
def semilinearTensorPull {s' : SmoothDatum D}
    (u : s'.X.left ≅ s.X.left) (v : s'.Y.left ≅ s.Y.left)
    (sq : CommSq u.hom s'.map s.map v.hom)
    (K : c.derived ell s.Y.left) (M : c.derived ell s.X.left) :
    (CondensedRing.moduleObjectDerivedPullback (c.obj ell) u.hom).obj
        (((CondensedRing.upperStar (c.obj ell) s.map).leftDerivedFunctor.obj K) ⊗ M) ≅
      ((CondensedRing.upperStar (c.obj ell) s'.map).leftDerivedFunctor.obj
          ((CondensedRing.moduleObjectDerivedPullback (c.obj ell) v.hom).obj K)) ⊗
        (CondensedRing.moduleObjectDerivedPullback (c.obj ell) u.hom).obj M :=
  (Functor.Monoidal.μIso
    (CondensedRing.upperStar (c.obj ell) u.hom).leftDerivedFunctor _ _).symm ≪≫
    tensorIso ((CondensedRing.pullbackSquareComparison (c.obj ell) sq).symm.app K) (Iso.refl _)

/-- Semilinear base change for the normalized orientation, canonical tensor transpose,
and the two normalized purity factorizations, in the native condensed categories.
The supplied membership and adjunction arguments only present the canonical restrictions;
B is required to be the exact proper/open exchange fixed by H, and gamma is constructed
by counit-preserving right-adjoint uniqueness. No choice of orientation or tensor map occurs.

Source: latest blueprint, thm-pur-weil-equivariance-of-purity-and-trace.proof.md,
Steps 1--2 and coefficient compatibility Step 5; sk-thm-purity-transport, Steps 1--4
(blueprint: lem-pur-condensed-semilinear-purity-factors).

Proof plan:
1. Inverse-image reindexing along u,v preserves Dctf. Use the normalized proper/open
exchange and its exceptional adjoint mate, retaining the mate counit equation.
2. At finite coefficients compare section-action realization with the ordinary
finite diagonal/DNC orientation and the inverse-projection transpose. Uniqueness
of adjunction transposes identifies the native tensor map and purity composite.
3. At integral coefficients use the full normalized-system equivalence, monoidal
reduction and the unit/counit-preserving realization. Transport the system arrow
identity, rather than appealing to faithfulness of separate finite evaluations.
4. Localize Hom groups for E and use the finite-subextension Hom colimit for Qbar.
The scalar comparisons preserve the units, counits and projection transposes.
This proves both factorization formulas and identifies their unit components.
5. Replace the structural maps a_X,a_Y by Spec(sigma) inverse followed by them.
This makes u,v linear without changing the underlying schemes, sites, diagonal,
Rees deformation charts, normal comparison, or affine integration orientation.
6. The normalized coefficient-system diagrams and realization counits are unchanged
by this auxiliary rebasing, also after rational localization and Hom colimits.
7. Apply normalized linear purity base change at the coefficient unit. Its source
comparison is exactly the actual root-normalized Tate pullback. This gives the
orientation equation for the original semilinear square.
8. For the proper compactification factor, use ringed exchange/tensor coherence
with the pulled-back condensed ring and its canonical derived tensor comparisons.
9. For the open factor, reindex local pure tensors and extend the supported entry
by zero; either order gives the same sections. Flat-term representatives descend
this equality to the ambient derived category, without extra signs.
10. Paste proper and open equalities, cancel compactification comparisons and invert
the projection maps on the stated inputs.
11. Transpose the two tensor composites under F' adjoint to G'. Expand the tensor
transposes and use the mate counit equation at the coefficient unit. Their transposes
coincide; injectivity of the Hom bijection proves the tensor equation. -/
theorem condensed_semilinear_purity_factors
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (c : Coefficient ell) (_hc : SemilinearCoefficient ell c)
    (A : AdjunctionFamily ell D)
    (_hA : BrownComparison ell D A ∧ ScalarCompatible ell D A ∧
      BaseChangeCompatible ell D A ∧ CompositionCompatible ell D hEll A ∧
      AffineNormalized ell D A)
    (s s' : SmoothDatum D) (hd : s.dim = s'.dim)
    (sigma : D.k ≃+* D.k)
    (u : s'.X.left ≅ s.X.left) (v : s'.Y.left ≅ s.Y.left)
    (_hu : u.hom ≫ s.X.hom = s'.X.hom ≫
      Spec.map (CommRingCat.ofHom sigma.toRingHom))
    (_hv : v.hom ≫ s.Y.hom = s'.Y.hom ≫
      Spec.map (CommRingCat.ofHom sigma.toRingHom))
    (sq : IsPullback u.hom s'.map s.map v.hom)
    (H : CondensedRing.CompactSupportComposition.Coherent (c.obj ell) D.k)
    (hP : ∀ K, property ell c s.Y.left K → property ell c s'.Y.left
      ((CondensedRing.moduleObjectDerivedPullback (c.obj ell) v.hom).obj K))
    (hQ : ∀ K, property ell c s.X.left K → property ell c s'.X.left
      ((CondensedRing.moduleObjectDerivedPullback (c.obj ell) u.hom).obj K))
    (G : c.ctf ell s.Y.left ⥤ c.ctf ell s.X.left)
    (G' : c.ctf ell s'.Y.left ⥤ c.ctf ell s'.X.left)
    (b : support ell c s.compactification (A c s).support_closed ⊣ G)
    (b' : support ell c s'.compactification (A c s').support_closed ⊣ G')
    (B : support ell c s.compactification (A c s).support_closed ⋙ semilinearPull v.hom hP ≅
      semilinearPull u.hom hQ ⋙ support ell c s'.compactification (A c s').support_closed)
    (_hB : ∀ K : c.ctf ell s.X.left,
      HEq (B.hom.app K).hom
        ((semilinearExchangeModel H s' u v sq).hom.app ((inclusion ell c s.X.left).obj K)))
    (hU : property ell c s.Y.left (unit ell c s.Y.left))
    (hU' : property ell c s'.Y.left (unit ell c s'.Y.left))
    (p : LinePullCoordinates ell c u.hom) :
    let P := semilinearPull v.hom hP
    let Q := semilinearPull u.hom hQ
    let N : c.ctf ell s.Y.left := ⟨unit ell c s.Y.left, hU⟩
    let N' : c.ctf ell s'.Y.left := ⟨unit ell c s'.Y.left, hU'⟩
    let e := semilinearMate (A c s) (A c s') G G' b b' P Q B
    let up : P.obj N ≅ N' := ObjectProperty.isoMk _ (semilinearUnitPull v.hom)
    let e1 := (e N).hom ≫ (G'.map up.hom).hom
    let a := semilinearOrientation (A c s) G b hU
    let a' := semilinearOrientation (A c s') G' b' hU'
    ∃ (hT : ∀ K : c.ctf ell s.Y.left, property ell c s.X.left
        (((CondensedRing.upperStar (c.obj ell) s.map).leftDerivedFunctor.obj K.obj) ⊗
          (G.obj N).obj))
      (hPF : ∀ K : c.ctf ell s.Y.left,
        IsIso (CondensedRing.exceptionalProjectionMorphismOfCompactification
          (c.obj ell) s.compactification (G.obj N).obj K.obj))
      (hT' : ∀ K : c.ctf ell s'.Y.left, property ell c s'.X.left
        (((CondensedRing.upperStar (c.obj ell) s'.map).leftDerivedFunctor.obj K.obj) ⊗
          (G'.obj N').obj))
      (hPF' : ∀ K : c.ctf ell s'.Y.left,
        IsIso (CondensedRing.exceptionalProjectionMorphismOfCompactification
          (c.obj ell) s'.compactification (G'.obj N').obj K.obj)),
      let t := fun K : c.ctf ell s.Y.left ↦ semilinearTensor (A c s) G b N K
        (semilinearDerivedUnit ell c s.Y.left) (hT K) (hPF K)
      let t' := fun K : c.ctf ell s'.Y.left ↦ semilinearTensor (A c s') G' b' N' K
        (semilinearDerivedUnit ell c s'.Y.left) (hT' K) (hPF' K)
      (CondensedRing.moduleObjectDerivedPullback (c.obj ell) u.hom).map a.hom ≫ e1 =
          (p.derived ell s.dim).hom ≫
            (eqToIso (congrArg (c.derivedLine ell s'.X.left) hd)).hom ≫ a'.hom ∧
      (∀ K : c.ctf ell s.Y.left,
        (CondensedRing.moduleObjectDerivedPullback (c.obj ell) u.hom).map (t K) ≫
            (e K).hom =
          (semilinearTensorPull u v sq.toCommSq K.obj (G.obj N).obj).hom ≫
            (((CondensedRing.upperStar (c.obj ell) s'.map).leftDerivedFunctor.obj
              (P.obj K).obj) ◁ e1) ≫ t' (P.obj K)) ∧
      (∀ K : c.ctf ell s.Y.left,
        (((CondensedRing.upperStar (c.obj ell) s.map).leftDerivedFunctor.obj K.obj) ◁ a.hom) ≫
            t K = ((semilinearGamma (A c s) G b).hom.app K).hom) ∧
      (∀ K : c.ctf ell s'.Y.left,
        (((CondensedRing.upperStar (c.obj ell) s'.map).leftDerivedFunctor.obj K.obj) ◁ a'.hom) ≫
            t' K = ((semilinearGamma (A c s') G' b').hom.app K).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
