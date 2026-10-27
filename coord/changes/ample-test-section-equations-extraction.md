# Normalized section equations for scheme-test preparation

## Reason

Extract the six existing definitions into their own public module so the geometric and
module-descent obligations can be stated without importing their consumer. This avoids
an import cycle. Every original declaration name, signature, universe and definition
body is preserved; only its source module changes. The preparation structure and theorem
retain their original signatures. New charts and line-data structures only bundle strict
parts of the argument, with concrete data and no hidden proof holes.

## Old

The six definitions were declared directly in
`Sheaf.TraceFormula.AmpleSchemeTestLinePreparation`:

```lean
/-- The normalization of the ordinary/etale identification on every Zariski open.
A section of `schemeRestriction` is literally a section of `M` on that open test.
The tensor unit sends it to `1 ⊗ s`, and the identification must send it back to `s`.
The quantified equations on the open inclusion and its inverse-image top retain all
opens, including opens with sections not extending globally.
Source: Stacks, Descent, Tags 03DX (2), 03LC (1); Sheaves, Tag 0096
(blueprint: lem-trf-ample-scheme-test-line-preparation). -/
def AmpleTestRestrictionNormalized {S : Scheme.{u}} (F : AlgebraicSpace S)
    (V : F.EtaleSite) (M : F.Modules)
    (e : OrdinaryEtaleIdentification F V M ((F.schemeRestriction V).obj M)) : Prop :=
  ∀ (W : (F.etaleForget.obj V).Opens)
    (p : (schemeOpens F V).obj W ⟶ V)
    (_hp : F.etaleForget.map p = W.ι)
    (ht : (F.etaleForget.map p) ⁻¹ᵁ W = ⊤)
    (s : Γ((F.schemeRestriction V).obj M, W)),
    e.app ((schemeOpens F V).obj W) p
      (((tensorPullback (F.etaleForget.map p)).obj
          ((F.schemeRestriction V).obj M)).presheaf.map (eqToHom ht.symm).op
        (tensorPullbackSection (F.etaleForget.map p) ((F.schemeRestriction V).obj M) W s)) =
      s

/-- The section equation saying that local identifications induce exactly the specified
ordinary transitions on every overlap test. This is the same equation as in effective
invertible descent, with no restriction on the universe of the covering index.
Source: Stacks, Spaces Descent, Tag 04W8
(blueprint: lem-trf-ample-scheme-test-line-preparation). -/
def AmpleTestInducesTransitions {S : Scheme.{u}} {I : Type v}
    (F : AlgebraicSpace S) (V : I → F.EtaleSite) (R : I → I → Over S)
    (p₁ : ∀ i j : I, R i j ⟶ (V i).obj.left)
    (p₂ : ∀ i j : I, R i j ⟶ (V j).obj.left)
    (L : ∀ i : I, (F.etaleForget.obj (V i)).Modules)
    (α : ∀ i j : I,
      (tensorPullback (p₂ i j).left).obj (L j) ≅
        (tensorPullback (p₁ i j).left).obj (L i))
    (N : F.Modules) (e : ∀ i : I, OrdinaryEtaleIdentification F (V i) N (L i)) : Prop :=
  ∀ (i j : I) (U : F.EtaleSite) (a : U ⟶ V i) (b : U ⟶ V j)
    (r : U.obj.left ⟶ R i j)
    (h₁ : r ≫ p₁ i j = a.hom.left) (h₂ : r ≫ p₂ i j = b.hom.left)
    (s : Γ((tensorPullback (F.etaleForget.map b)).obj (L j), ⊤)),
    (e i).app U a
      (((atlasTransitionOver (L i) (L j) (p₁ i j) (p₂ i j) (α i j)
        r a.hom.left b.hom.left h₁ h₂).hom.app ⊤) s) = (e j).app U b s

/-- Pullback of an original overlap transition, with both tensor-composition
identifications. These are the existing unit-normalized composition maps.
Source: Stacks, Sheaves, Tag 0097; Spaces Descent, Tag 04W8
(blueprint: lem-trf-ample-scheme-test-line-preparation). -/
noncomputable def ampleTestPulledTransition {S : Scheme.{u}}
    {V W R V' W' D : Over S}
    (L : V.left.Modules) (K : W.left.Modules) (r₁ : R ⟶ V) (r₂ : R ⟶ W)
    (α : (tensorPullback r₂.left).obj K ≅ (tensorPullback r₁.left).obj L)
    (a : V' ⟶ V) (b : W' ⟶ W) (d₁ : D ⟶ V') (d₂ : D ⟶ W') (c : D ⟶ R)
    (h₁ : c ≫ r₁ = d₁ ≫ a) (h₂ : c ≫ r₂ = d₂ ≫ b) :
    (tensorPullback d₂.left).obj ((tensorPullback b.left).obj K) ≅
      (tensorPullback d₁.left).obj ((tensorPullback a.left).obj L) :=
  (tensorSectionsComp d₂.left b.left).app K ≪≫
    atlasTransitionOver L K r₁ r₂ α c (d₁ ≫ a) (d₂ ≫ b) h₁ h₂ ≪≫
      ((tensorSectionsComp d₁.left a.left).app L).symm

/-- The canonical section comparison from an iterated pullback to the original module.
The equation `h` specifies the common scheme map, so this includes its equality transport.
Source: Stacks, Sheaves, Tag 0097; Descent, Tag 03LC (1)
(blueprint: lem-trf-ample-scheme-test-line-preparation). -/
noncomputable def ampleTestCompositeSection {A B C : Scheme.{u}}
    (L : C.Modules) (p : A ⟶ B) (a : B ⟶ C) (q : A ⟶ C) (h : p ≫ a = q) :
    Γ((tensorPullback p).obj ((tensorPullback a).obj L), ⊤) ⟶
      Γ((tensorPullback q).obj L, ⊤) :=
  ((tensorSectionsComp p a).hom.app L).app ⊤ ≫
    (eqToHom (congrArg (fun k ↦ (tensorPullback k).obj L) h)).app ⊤

/-- Uniqueness of an effective realization of specified ordinary transitions,
retaining every local identification. This is the unique-isomorphism clause of
invertible descent, expressed on all localized-site sections.
Source: Stacks, Spaces Descent, Tag 04W8
(blueprint: lem-trf-ample-scheme-test-line-preparation). -/
def AmpleTestUniqueRealization {S : Scheme.{u}} {I : Type v}
    (X : AlgebraicSpace S) (V : I → X.EtaleSite) (D : I → I → Over S)
    (d₁ : ∀ i j : I, D i j ⟶ (V i).obj.left)
    (d₂ : ∀ i j : I, D i j ⟶ (V j).obj.left)
    (L : ∀ i : I, (X.etaleForget.obj (V i)).Modules)
    (β : ∀ i j : I,
      (tensorPullback (d₂ i j).left).obj (L j) ≅
        (tensorPullback (d₁ i j).left).obj (L i))
    (N : X.Modules) (e : ∀ i : I, OrdinaryEtaleIdentification X (V i) N (L i)) : Prop :=
  ∀ (N' : X.Modules) (_hN' : X.IsLineModule N')
    (e' : ∀ i : I, OrdinaryEtaleIdentification X (V i) N' (L i)),
    AmpleTestInducesTransitions X V D d₁ d₂ L β N' e' →
    ∃! z : N ≅ N', ∀ (i : I) (U : X.EtaleSite) (p : U ⟶ V i)
      (s : Γ((tensorPullback (X.etaleForget.map p)).obj (L i), ⊤)),
      z.hom.val.app (op U) ((e i).app U p s) = (e' i).app U p s

/-- The local characterization of the canonical comparison for an etale projection.
The section formula uses exactly the original normalized restriction identifications.
`HEq` avoids expanding the construction of restriction to compare its section carriers;
these carriers are definitionally the same by precomposition on the small etale sites.
Source: Stacks, Descent, Tag 03LC (1); Spaces Descent, Tag 04W8
(blueprint: lem-trf-ample-scheme-test-line-preparation). -/
def AmpleTestEtaleComparison {S : Scheme.{u}} {I : Type v}
    (F X : AlgebraicSpace S) (k : X ⟶ F) (M : F.Modules) (N : X.Modules)
    (Fᵢ : I → F.EtaleSite) (Xᵢ : I → X.EtaleSite)
    (a : ∀ i : I, (Xᵢ i).obj.left ⟶ (Fᵢ i).obj.left)
    (original : ∀ i : I, OrdinaryEtaleIdentification F (Fᵢ i) M
      ((F.schemeRestriction (Fᵢ i)).obj M))
    (identification : ∀ i : I, OrdinaryEtaleIdentification X (Xᵢ i) N
      ((tensorPullback (a i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))) : Prop :=
  ∀ hp : IsEtale k.hom.hom,
    ∃! z : N ≅ (pullback k hp).obj M,
      ∀ (i : I) (U : X.EtaleSite) (p : U ⟶ Xᵢ i)
        (q : (etaleMap k hp).obj U ⟶ Fᵢ i)
        (hq : (X.etaleForget.map p) ≫ (a i).left = F.etaleForget.map q)
        (s : Γ((tensorPullback (X.etaleForget.map p)).obj
          ((tensorPullback (a i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M)), ⊤)),
        HEq (z.hom.val.app (op U) ((identification i).app U p s))
          ((original i).app ((etaleMap k hp).obj U) q
            (ampleTestCompositeSection ((F.schemeRestriction (Fᵢ i)).obj M)
              (X.etaleForget.map p) (a i).left (F.etaleForget.map q) hq s))

```

## New

The exact same signatures and definition bodies are in
`Sheaf.TraceFormula.AmpleSchemeTestLinePreparationDefs`, publicly imported by the original
module. Their documentation now points to the new definition-owner node. The original
module's public imports are reduced to the definition owner, point-surjectivity,
presheaf geometric predicates and ampleness; its proof imports the three new obligations
and the existing invertibility, base-change ampleness and canonical-Proj criterion.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.TraceFormula.AmpleSchemeTestLinePreparation | S4 | Publicly reimports the extracted definitions and combines the three proof obligations. |

Repository searches found no other direct Lean importer of the item and no other Lean
module using any of these six names. Thus no consumer adaptation or consumer compile is
needed. The parent ample-local node still needs this theorem in its unfinished proof;
this delivery preserves its statement and route.

## Status

landed 20261026T082945-L-2243945 2026-10-26 (merge of deliver/S4/Sheaf.TraceFormula.AmpleSchemeTestLinePreparation)
