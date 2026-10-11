/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Sheaf.AlgebraicGeometry.NagataQCOpenEqualityStage

/-!
# Stage of equality for two descended morphisms

Source: blueprint, sec-nagata-compactification, sk-prop-nagata-sketch-approximation,
node order 355, and Stacks Project, Tag 01ZM (3), proof
(blueprint: def-nagata-morphism-equality-stage).

The data record contains actual affine opens, generators of their coordinate rings,
and equality witnesses for the pullbacks of these generators. The definition takes
exactly the finite upper bound prescribed by the node, without assuming eventual
morphism equality. Finite presentation means locally of finite presentation,
quasi-compact and quasi-separated, as in Stacks.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Choice data in the construction of the equality stage.
Source: blueprint node order 355; Stacks Tag 01ZM (3), proof
(blueprint: def-nagata-morphism-equality-stage).

First choose finite affine covers of the base and target and finite algebra generators.
For each target chart use `nagataQCOpenEqualityStage` on its two inverse images.
Choose a finite affine cover of their intersection at that stage. The maps `phiU`
and `psiU` are the two restricted composites to the target chart; `overPhi` and
`overPsi` identify them with those composites. For each generator choose a later
stage `mu` where its two pullbacks agree. Such stages exist by the affine-limit
identification of sections (Spec preserves limits, node `lem-weil-pbc-spec-colimit-limit`)
and elementwise equality in a filtered ring colimit, clause (2) of
`lem-pc-filtered-colimit-commrings-elementwise`. The structure records these choices,
not a proof of their existence or the subsequent eventual-equality theorem. -/
structure NagataMorphismEqualityStageData
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    (p : X₀ ⟶ D.obj (op i₀)) (q : Y₀ ⟶ D.obj (op i₀))
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    (phi psi : X₀ ⟶ Y₀) (hphi : phi ≫ q = p) (hpsi : psi ≫ q = p)
    (d : I → I → I) (r : LinearOrder I) where
  /-- The binary upper bounds fixed in the node. -/
  boundData : ∀ i j, i ≤ d i j ∧ j ≤ d i j
  /-- Equality of the two base changes, equivalently of their first projections. -/
  equalLimitBaseChange :
    pullback.fst p (c.π.app (op i₀)) ≫ phi = pullback.fst p (c.π.app (op i₀)) ≫ psi
  /-- A finite affine cover of the base stage. -/
  J : Type u
  finiteJ : Fintype J
  T : J → (D.obj (op i₀)).Opens
  affineT : ∀ j, IsAffineOpen (T j)
  coverT : ⨆ j, T j = ⊤
  /-- A finite affine target cover subordinate to the base cover. -/
  K : J → Type u
  finiteK : ∀ j, Fintype (K j)
  V : ∀ j, K j → Y₀.Opens
  affineV : ∀ j k, IsAffineOpen (V j k)
  coverV : ⨆ j, ⨆ k, V j k = ⊤
  chartMap : ∀ j k, (V j k).toScheme ⟶ (T j).toScheme
  chartOver : ∀ j k, chartMap j k ≫ (T j).ι = (V j k).ι ≫ q
  finitePresentationChart : ∀ j k, (chartMap j k).appTop.hom.FinitePresentation
  /-- Finite sets of actual coordinate-ring elements, generating over the base ring.
  Subring closure of the image of R together with G expresses generation as R-algebra. -/
  G : ∀ j k, Finset Γ((V j k).toScheme, ⊤)
  generatorsGenerate : ∀ j k,
    Subring.closure (Set.range (chartMap j k).appTop ∪ (G j k : Set _)) = ⊤
  /-- Compact inverse images and their equality on the limit. -/
  compactPhi : ∀ j k, IsCompact ((phi ⁻¹ᵁ V j k : X₀.Opens) : Set X₀)
  compactPsi : ∀ j k, IsCompact ((psi ⁻¹ᵁ V j k : X₀.Opens) : Set X₀)
  equalOpens : ∀ j k,
    pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ (phi ⁻¹ᵁ V j k) =
      pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ (psi ⁻¹ᵁ V j k)
  /-- Exactly the previously defined compact-open equality stage, not an arbitrary stage. -/
  lambdaJK : ∀ j, K j → I
  selectedLambda : ∀ j k, lambdaJK j k = nagataQCOpenEqualityStage D c hc i₀ p
    (phi ⁻¹ᵁ V j k) (psi ⁻¹ᵁ V j k) (compactPhi j k) (compactPsi j k)
    (equalOpens j k) d r
  lambdaGE : ∀ j k, i₀ ≤ lambdaJK j k
  /-- A finite affine cover of the intersection of the two transported inverse images. -/
  L : ∀ j, K j → Type u
  finiteL : ∀ j k, Fintype (L j k)
  U : ∀ j k, L j k →
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE (lambdaGE j k)).op)).Opens
  affineU : ∀ j k l, IsAffineOpen (U j k l)
  coverU : ∀ j k, ⨆ l, U j k l =
    (pullback.fst p (D.map (homOfLE (lambdaGE j k)).op) ⁻¹ᵁ (phi ⁻¹ᵁ V j k)) ⊓
      (pullback.fst p (D.map (homOfLE (lambdaGE j k)).op) ⁻¹ᵁ (psi ⁻¹ᵁ V j k))
  /-- The two composites from each affine chart, factored through the target open. -/
  phiU : ∀ j k l, (U j k l).toScheme ⟶ (V j k).toScheme
  psiU : ∀ j k l, (U j k l).toScheme ⟶ (V j k).toScheme
  overPhi : ∀ j k l, phiU j k l ≫ (V j k).ι =
    (U j k l).ι ≫ pullback.fst p (D.map (homOfLE (lambdaGE j k)).op) ≫ phi
  overPsi : ∀ j k l, psiU j k l ≫ (V j k).ι =
    (U j k l).ι ≫ pullback.fst p (D.map (homOfLE (lambdaGE j k)).op) ≫ psi
  /-- The later coefficient stage for every chart and every generator.
  An object of Over (op lambdaJK) is precisely an index mu ≥ lambdaJK. -/
  mu : ∀ j k, L j k → (G j k) → Over (op (lambdaJK j k))
  /-- Equality of the images of x = phiU*(b) and y = psiU*(b) on U_mu.
  The displayed pullback is canonically the inverse image of U in X_mu. -/
  coefficientEquality : ∀ j k l b,
    (pullback.fst
      ((U j k l).ι ≫ pullback.snd p (D.map (homOfLE (lambdaGE j k)).op))
      (D.map (mu j k l b).hom)).appTop ((phiU j k l).appTop b.val) =
    (pullback.fst
      ((U j k l).ι ≫ pullback.snd p (D.map (homOfLE (lambdaGE j k)).op))
      (D.map (mu j k l b).hom)).appTop ((psiU j k l).appTop b.val)

/-- The selected finite upper bound of the base stage, all compact-open equality
stages and all coefficient equality stages.
Source: blueprint node order 355; Stacks Tag 01ZM (3), proof
(blueprint: def-nagata-morphism-equality-stage).

Enumerate the finitely many pairs (j,k), affine source charts l and generators b.
Form their finite set of stages together with i₀ and apply the already defined
`directedFiniteUpperBound`. No assertion that the two morphisms agree at this
stage is included in this definition; that is the subsequent blueprint theorem. -/
noncomputable def nagataMorphismEqualityStage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} {hc : IsLimit c}
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i₀ : I} [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    {p : X₀ ⟶ D.obj (op i₀)} {q : Y₀ ⟶ D.obj (op i₀)}
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    {phi psi : X₀ ⟶ Y₀} {hphi : phi ≫ q = p} {hpsi : psi ≫ q = p}
    {d : I → I → I} {r : LinearOrder I}
    (data : NagataMorphismEqualityStageData D c hc i₀ p q phi psi hphi hpsi d r) : I := by
  classical
  letI := data.finiteJ
  letI : ∀ j, Fintype (data.K j) := data.finiteK
  letI : ∀ j k, Fintype (data.L j k) := data.finiteL
  exact directedFiniteUpperBound i₀ d r
    (insert i₀ (Finset.univ.biUnion fun j => Finset.univ.biUnion fun k =>
      insert (data.lambdaJK j k) (Finset.univ.biUnion fun l =>
        (data.G j k).attach.image fun b => (data.mu j k l b).left.unop)))

end AlgebraicGeometry
