/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence

/-! # Restriction-normalized immersion comparisons

Source: blueprint main-20261015, det-prop-scalar-six-pullback.proof.md, (2)--(3);
Stacks Project, proetale.tex, Tags 09AA and 09BN.
(blueprint: lem-sfb-normalized-immersion-comparison-coherence).

All structures below bundle parameters or clauses of this one conditional assertion.
The extension and inverse-image functors are the published arbitrary-ring functors.
No scalar-extension functor or comparison is constructed from a mere existence claim.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The schemes quantified over in the assertion, bundled with its two hypotheses.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
abbrev ImmersionComparisonBase :=
  { X : Scheme.{u} // IsLocallyNoetherian X ∧ CompactSpace X }

/-- Cartesian coefficient parameters, before imposing their identity and composition laws.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure ImmersionComparisonRings (I : Type v) where
  ring : ∀ (_r : I) (X : ImmersionComparisonBase.{u}),
    Sheaf (ProEt.topology X.val) CommRingCat.{u + 1}
  coefficient : ∀ (r : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a],
    (proEtaleSheafInverseImage a CommRingCat.{u + 1}).obj (ring r X) ≅ ring r S

namespace ImmersionComparisonRings

variable {I : Type v} (G : ImmersionComparisonRings.{u} I)

/-- Use the dependency's coefficient bundle without redefining module sheaves.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def object (r : I) (X : ImmersionComparisonBase.{u}) : LocallyClosedCoefficients.{u} where
  scheme := X.val
  locallyNoetherian := X.property.1
  compact := X.property.2
  ring := G.ring r X

/-- An immersion with exactly the given cartesian coefficient identification.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def arrow (r : I) {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val)
    [IsImmersion a] : LocallyClosedCoefficientImmersion (G.object r S) (G.object r X) where
  hom := a
  immersion := inferInstance
  coefficient := G.coefficient r a

/-- Coherence means the actual inverse-image identity and composition identifications.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure Cartesian : Prop where
  identity : ∀ (r : I) (X : ImmersionComparisonBase.{u}),
    G.arrow r (𝟙 X.val) = LocallyClosedCoefficientImmersion.identity (G.object r X)
  composition : ∀ (r : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b],
    G.arrow r (b ≫ a) = (G.arrow r a).comp (G.arrow r b)

/-- The ordinary unbounded derived category of the given coefficient ring sheaf.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
abbrev category (r : I) (X : ImmersionComparisonBase.{u}) :=
  DerivedCategory (proEtaleRingModules X.val (G.ring r X))

/-- Exact inverse image, localized termwise as in the dependency.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def pull (r : I) {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val)
    [IsImmersion a] : G.category r X ⥤ G.category r S :=
  (G.arrow r a).pull.mapDerivedCategory

/-- The dependency's extension, with the cartesian coefficient identification inserted.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def extend (E : LocallyClosedExtensionData.{u}) (r : I)
    {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val) [IsImmersion a] :
    G.category r S ⥤ G.category r X :=
  E.derived (S := G.object r S) (X := G.object r X) (G.arrow r a)

/-- Canonical restriction composition, using the actual module inverse-image compositor.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def pullComp (hG : G.Cartesian) (r : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b] :
    G.pull r (b ≫ a) ≅ G.pull r a ⋙ G.pull r b :=
  eqToIso (congrArg (fun k ↦ k.pull.mapDerivedCategory) (hG.composition r a b)) ≪≫
    Functor.mapDerivedCategoryNatIso ((G.arrow r a).pullComp (G.arrow r b)) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The published extension compositor, transported along cartesian coefficient coherence.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def gamma (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (hG : G.Cartesian) (r : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b] :
    G.extend E r b ⋙ G.extend E r a ≅ G.extend E r (b ≫ a) :=
  D.gamma (G.arrow r a) (G.arrow r b) ≪≫
    eqToIso (congrArg E.derived (hG.composition r a b).symm)

/-- The identity restriction identification, read from the normalized extension identity.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def pullId (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (hG : G.Cartesian) (r : I) (X : ImmersionComparisonBase.{u}) :
    G.pull r (𝟙 X.val) ≅ 𝟭 (G.category r X) :=
  eqToIso (congrArg (fun k ↦ k.pull.mapDerivedCategory) (hG.identity r X)) ≪≫
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (D.identity (G.object r X)).symm _ ≪≫
        D.restriction (.identity (G.object r X))

/-- The supplied F and q, including exactly their identity and composition coherence.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def Functors (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (hG : G.Cartesian) :=
  { data : (Σ functor :
      ∀ (r s : I) (X : ImmersionComparisonBase.{u}), G.category r X ⥤ G.category s X,
      ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a],
    functor r s X ⋙ G.pull s a ≅ G.pull r a ⋙ functor r s S) //
    (∀ (r s : I) (X : ImmersionComparisonBase.{u}) (M : G.category r X),
    (data.2 r s (𝟙 X.val)).hom.app M ≫
        (data.1 r s X).map ((G.pullId E D hG r X).hom.app M) =
      (G.pullId E D hG s X).hom.app ((data.1 r s X).obj M)) ∧
    (∀ (r s : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b]
    (M : G.category r X),
    (data.2 r s (b ≫ a)).hom.app M ≫
        (data.1 r s T).map ((G.pullComp hG r a b).hom.app M) =
      (G.pullComp hG s a b).hom.app ((data.1 r s X).obj M) ≫
        (G.pull s b).map ((data.2 r s a).hom.app M) ≫
          (data.2 r s b).hom.app ((G.pull r a).obj M)) }

variable {G}

/-- The supplied functor component of the comparison parameters.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def Functors.functor {E : LocallyClosedExtensionData.{u}} {D : E.DerivedCoherence}
    {hG : G.Cartesian} (F : G.Functors E D hG) (r s : I) (X : ImmersionComparisonBase.{u}) :
    G.category r X ⥤ G.category s X := F.val.1 r s X

/-- The supplied restriction comparison component of the parameters.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def Functors.q {E : LocallyClosedExtensionData.{u}} {D : E.DerivedCoherence}
    {hG : G.Cartesian} (F : G.Functors E D hG) (r s : I)
    {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val) [IsImmersion a] :
    F.functor r s X ⋙ G.pull s a ≅ G.pull r a ⋙ F.functor r s S :=
  F.val.2 r s a

namespace Functors

variable {E : LocallyClosedExtensionData.{u}} {D : E.DerivedCoherence}
  {hG : G.Cartesian} (F : G.Functors E D hG)

/-- The type of comparison isomorphisms; no existence is included in this notation.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
abbrev Comparison (r s : I) {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val)
    [IsImmersion a] := G.extend E r a ⋙ F.functor r s X ≅
      F.functor r s S ⋙ G.extend E s a

/-- The precise restriction normalization (N), including both restriction isomorphisms.
Source: node proof step 1 (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def Normalized {r s : I} {S X : ImmersionComparisonBase.{u}} {a : S.val ⟶ X.val}
    [IsImmersion a] (d : F.Comparison r s a) : Prop :=
  ∀ M : G.category r S,
    (G.pull s a).map (d.hom.app M) ≫
        (D.restriction (G.arrow s a)).hom.app ((F.functor r s S).obj M) =
      (F.q r s a).hom.app ((G.extend E r a).obj M) ≫
        (F.functor r s S).map ((D.restriction (G.arrow r a)).hom.app M)

/-- The two separately supplied comparisons, including their normalization. In a clopen
case both are retained as input; their equality is a conclusion, not an assumption.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure Elementary where
  openComparison : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (_ : IsOpenImmersion a), F.Comparison r s a
  closedComparison : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (_ : IsClosedImmersion a), F.Comparison r s a
  openNormalized : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (ha : IsOpenImmersion a),
    F.Normalized (openComparison r s a ha)
  closedNormalized : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (ha : IsClosedImmersion a),
    F.Normalized (closedComparison r s a ha)

/-- The actual factorization composite: insert inverse gamma, the two given comparisons,
and gamma. All data are existing isomorphisms, with explicit functor associators.
Source: node proof steps 3--4 (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def composite {r s : I} {S X T : ImmersionComparisonBase.{u}}
    {a : S.val ⟶ X.val} {b : T.val ⟶ S.val} [IsImmersion a] [IsImmersion b]
    (da : F.Comparison r s a) (db : F.Comparison r s b) : F.Comparison r s (b ≫ a) :=
  Functor.isoWhiskerRight (G.gamma E D hG r a b).symm (F.functor r s X) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (G.extend E r b) da ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight db (G.extend E s a) ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (F.functor r s T) (G.gamma E D hG s a b)

/-- The additional natural isomorphisms t for one triple of labels r, s, t, with exactly
the stated restriction square. Nothing is assumed for other triples, and no associativity
of these tower isomorphisms is assumed.
Source: blueprint proof (3) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure Tower (r s t : I) where
  iso : ∀ X : ImmersionComparisonBase.{u},
    F.functor r s X ⋙ F.functor s t X ≅ F.functor r t X
  compatible : ∀ {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (M : G.category r X),
    (G.pull t a).map ((iso X).hom.app M) ≫ (F.q r t a).hom.app M =
      (F.q s t a).hom.app ((F.functor r s X).obj M) ≫
        (F.functor s t S).map ((F.q r s a).hom.app M) ≫
          (iso S).hom.app ((G.pull r a).obj M)

/-- All the clauses asserted for the assembled comparisons. Factorization equations use
ordinary natural isomorphism equality, so two factorizations with equal composite maps
produce the very same comparison after equality transport.
Source: blueprint proof (2)--(3)
(blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure Coherent (B : F.Elementary)
    (d : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
      (a : S.val ⟶ X.val) [IsImmersion a], F.Comparison r s a) : Prop where
  normalized : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a], F.Normalized (d r s a)
  openComparison : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (ha : IsOpenImmersion a),
    d r s a = B.openComparison r s a ha
  closedComparison : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (ha : IsClosedImmersion a),
    d r s a = B.closedComparison r s a ha
  closedOpen : ∀ (r s : I) {S V X : ImmersionComparisonBase.{u}}
    (c : S.val ⟶ V.val) (v : V.val ⟶ X.val) [IsImmersion c] [IsImmersion v]
    (hc : IsClosedImmersion c) (hv : IsOpenImmersion v),
    d r s (c ≫ v) = F.composite (B.openComparison r s v hv) (B.closedComparison r s c hc)
  openClosed : ∀ (r s : I) {S Z X : ImmersionComparisonBase.{u}}
    (j : S.val ⟶ Z.val) (i : Z.val ⟶ X.val) [IsImmersion j] [IsImmersion i]
    (hj : IsOpenImmersion j) (hi : IsClosedImmersion i),
    d r s (j ≫ i) = F.composite (B.closedComparison r s i hi) (B.openComparison r s j hj)
  composition : ∀ (r s : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b]
    (M : G.category r T),
    (F.functor r s X).map ((G.gamma E D hG r a b).hom.app M) ≫
        (d r s (b ≫ a)).hom.app M =
      (d r s a).hom.app ((G.extend E r b).obj M) ≫
        (G.extend E s a).map ((d r s b).hom.app M) ≫
          (G.gamma E D hG s a b).hom.app ((F.functor r s T).obj M)
  tower : ∀ (r s t : I) (H : F.Tower r s t) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (M : G.category r S),
    (F.functor s t X).map ((d r s a).hom.app M) ≫
        (d s t a).hom.app ((F.functor r s S).obj M) ≫
          (G.extend E t a).map ((H.iso S).hom.app M) =
      (H.iso X).hom.app ((G.extend E r a).obj M) ≫
        (d r t a).hom.app M

end Functors
end ImmersionComparisonRings

/-- Restriction-normalized open and closed comparisons assemble independently of either
factorization order, respect immersion composition, and respect every compatible tower.

Source: blueprint main-20261015, det-prop-scalar-six-pullback.proof.md, (2)--(3);
Stacks Project, proetale.tex, Tags 09AA and 09BN.
(blueprint: lem-sfb-normalized-immersion-comparison-coherence).

Proof plan, following the seven steps of the node:
1. Write L for inverse image and rho for D.restriction. The input normalizations are
   exactly equation (N). The published normalized gamma has equation (G), transported
   to the derived category using its termwise characterization.
2. The dependency's restriction Hom bijection detects equality between extension images.
   Conjugating by existing comparison isomorphisms extends this detection to objects
   isomorphic to those images. Hence a comparison with the specified restriction is unique.
3. Restrict the binary composite. Naturality of rho, the two equations (N), and naturality
   and composition coherence of q give equation (B). Equation (G) then normalizes it.
4. Factor an immersion as closed then open and use composite. This gives a normalized
   isomorphism. Every other factorization, including open then closed, has the same
   normalization, so step 2 identifies it. It also agrees with the supplied comparisons.
5. The binary composite for arbitrary immersions is normalized by step 3. Uniqueness
   identifies it with d for their composite. Precompose with F(gamma) for the stated law.
6. Restrict the left tower path. Naturality of rho and q and normalization for rs and st
   reduce it to equation (L) in the node's proof.
7. Restrict the right tower path. The supplied q/t square and naturality of t give the
   same equation (L). Cancel rho and apply step 2, using the two comparison isomorphisms
   to identify the source with an extension image. This proves the tower law naturally.
Every nonformal input is lem-sfb-locally-closed-extension-coherence. -/
theorem normalizedImmersionComparisonCoherence
    {I : Type v} (G : ImmersionComparisonRings.{u} I) (hG : G.Cartesian)
    (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent) (D : E.DerivedCoherence)
    (F : G.Functors E D hG) (B : F.Elementary) :
    ∃ d : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
      (a : S.val ⟶ X.val) [IsImmersion a], F.Comparison r s a,
      F.Coherent B d := by
  sorry

end AlgebraicGeometry.Scheme
