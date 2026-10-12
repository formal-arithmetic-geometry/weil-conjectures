# AlgebraicGeometry.Scheme.etale_chart_residue_triples_equivalence_ring_iso

## Reason

The source constructs a compatible equivalence, not compatibility for every
abstract equivalence. The declaration is unused: searching both library roots finds
only its own declaration; tools/downstream.py with --uses confirms this.
The already proved combined theorem supplies the source's existential result.

STATEMENT-DISPUTED: the universal assertion is false. Take A = Q, Y = Spec Q,
i the identity, and Ω an algebraic closure of Q. Here K is the entire algebraic
closure. An automorphism σ of K fixing Q induces an autoequivalence of triples by
replacing φ with σ ∘ φ and keeping B, α, q and all ring maps unchanged.
Compose the constructed chart equivalence with this autoequivalence. Consider the
neighbourhood Spec L, where L = Q(cuberoot(2)) is the real cubic subfield, with its
chosen embedding j into Ω. Choose σ carrying cuberoot(2) to a nonreal conjugate.
The alleged δ component, via ΓSpecIso, would give a Q-algebra automorphism β of L
with j = σ ∘ j ∘ β. This is impossible: the images j(L) and σ(j(L)) differ (the
former is real and the latter contains a nonreal element), whereas precomposition
with an automorphism does not change the image. The first formula forces
Q-linearity and the second forces equality of the two embeddings.

The corrected DAG statement is the existential compatible-equivalence assertion
of the source. Its Lean record points to the existing combined theorem; no duplicate
theorem is introduced. No target signature or definition changes. The node is not
a realized unit statement or step; no unit route is bypassed.

Source: [Stacks 04HX](https://stacks.math.columbia.edu/tag/04HX), proof's first
paragraph, and [Stacks 04HT](https://stacks.math.columbia.edu/tag/04HT).

## Old

```lean
theorem etale_chart_residue_triples_equivalence_ring_iso
    (Y : Scheme.{v}) (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{v}) (i : Spec A ⟶ Y) [IsOpenImmersion i]
    (xU : Spec (.of Ω) ⟶ Spec A) :
    let x := xU ≫ i
    let p := (SpecToEquivOfField Ω (Spec A) xU).1
    let F := (Spec A).residueField p
    let e := (SpecToEquivOfField Ω (Spec A) xU).2
    letI : Algebra F Ω := e.hom.toAlgebra
    let K := separableClosure F Ω
    let χ : F ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap F K)
    let Nall := (pointSmallEtale x).fiber.Elements
    let P : ObjectProperty Nall := fun c ↦ IsAffine c.1.left
    let N := P.FullSubcategory
    let Q : ObjectProperty N := fun c ↦ ∃ g : c.obj.1.left ⟶ Spec A, g ≫ i = c.obj.1.hom
    let NU := Q.FullSubcategory
    let D := (P.ι ⋙ CategoryOfElements.π (pointSmallEtale x).fiber ⋙
      Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
    let DU := Q.ι.op ⋙ D
    let T := EtaleResidueTriples A p K χ
    let DT := etaleResidueTriplesRingDiagram A p K χ
    (∀ (c : NU) (z : c.obj.obj.1.left.residueField
          (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).1),
        (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).2 z ∈ K) →
      ∀ (E : NUᵒᵖ ≌ T), ∃ (δ : DU ≅ E.functor ⋙ DT),
        ∀ c : NU,
          let t := E.functor.obj (op c)
          (∀ g : c.obj.obj.1.left ⟶ Spec A, g ≫ i = c.obj.obj.1.hom →
            (ΓSpecIso A).inv ≫ g.appTop ≫ δ.hom.app (op c) = t.α) ∧
          c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
            Spec.map (CommRingCat.ofHom K.subtype) ≫
              Spec.map ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ) ≫
              Spec.map (δ.hom.app (op c))
```

## New

The false declaration is retired, with no replacement of that name. The corrected
existential result is already proved as
`AlgebraicGeometry.Scheme.etale_chart_residue_triples_equivalence`:

```lean
theorem etale_chart_residue_triples_equivalence
    (Y : Scheme.{v}) (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{v}) (i : Spec A ⟶ Y) [IsOpenImmersion i]
    (xU : Spec (.of Ω) ⟶ Spec A) :
    let x := xU ≫ i
    let p := (SpecToEquivOfField Ω (Spec A) xU).1
    let F := (Spec A).residueField p
    let e := (SpecToEquivOfField Ω (Spec A) xU).2
    letI : Algebra F Ω := e.hom.toAlgebra
    let K := separableClosure F Ω
    let χ : F ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap F K)
    let Nall := (pointSmallEtale x).fiber.Elements
    let P : ObjectProperty Nall := fun c ↦ IsAffine c.1.left
    let N := P.FullSubcategory
    let Q : ObjectProperty N := fun c ↦ ∃ g : c.obj.1.left ⟶ Spec A, g ≫ i = c.obj.1.hom
    let NU := Q.FullSubcategory
    let D := (P.ι ⋙ CategoryOfElements.π (pointSmallEtale x).fiber ⋙
      Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
    let DU := Q.ι.op ⋙ D
    let T := EtaleResidueTriples A p K χ
    let DT := etaleResidueTriplesRingDiagram A p K χ
    (∀ (c : NU) (z : c.obj.obj.1.left.residueField
          (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).1),
        (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).2 z ∈ K) →
      ∃ (E : NUᵒᵖ ≌ T) (δ : DU ≅ E.functor ⋙ DT),
        (∀ c : NU,
          let t := E.functor.obj (op c)
          (∀ g : c.obj.obj.1.left ⟶ Spec A, g ≫ i = c.obj.obj.1.hom →
            (ΓSpecIso A).inv ≫ g.appTop ≫ δ.hom.app (op c) = t.α) ∧
          c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
            Spec.map (CommRingCat.ofHom K.subtype) ≫
              Spec.map ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ) ≫
              Spec.map (δ.hom.app (op c)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence | F1 | Retires its unused false lemma; both existing proofs and all other signatures stay identical. |

The second reading found 248 downstream modules; none mentions the retired declaration.
They need no adaptation. The DAG node has no statement or proof citers.

## Status

landed 20261012T173821-L-3294203 2026-10-12 (merge of deliver/F1/Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence)
