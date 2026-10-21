# AlgebraicGeometry.relativeMV_cover_chain_square

## Reason

The return for delivery `d5ef8ca63b` reports that the archived restoration was
already present in the library with identical text. The current live module is
therefore the baseline, not a missing source. This repair rewrites the assembly
of its three component equations so that the proof postcomposes supplied
identities rather than rewriting the full geometric goal. The initial eager
`dsimp only` and the two backward transparency overrides are unnecessary for
this form and are removed. The existing heartbeat allowance remains necessary
and is retained, with its existing explanatory comment.

No statement, definition, public import, dependency, or universe changes.
The theorem remains a complete proof using the same three declarations.

## Old

The current live declaration, verbatim:

```lean
theorem relativeMV_cover_chain_square
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (A B A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ a.left)
      (e₂ : DerivedCategory.Q.obj B ≅ (b U).left ⊞ (b V).left)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅
        (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (b (U ⊓ V)).right),
      DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map β ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
        e₃.hom ≫ (b (U ⊓ V)).hom := by
  dsimp only
  obtain ⟨A, B, A', B', t, t', α, β, H, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ⟩ :=
    relativeMV_direct_image_homotopy_comparison f f' g g' hpull K K' φ U V hcover
  obtain ⟨C, D, s, a, b, H', d₁, d₂, d₃, ha, hb, hc⟩ :=
    derivedPullback_cone_square_transposition g A B A' B' t t' α β H
  obtain ⟨T, i, c, hcomm, r₂, r₃, hr₂, hr₃⟩ :=
    CochainComplex.homotopy_square_cone_rectification s t' a b H'
  refine ⟨C, T, A', B', i, t', a, c, hcomm,
    d₁ ≪≫ e₁, r₂ ≪≫ d₂ ≪≫ e₂, r₃ ≪≫ d₃ ≪≫ e₃, e₁', e₂', e₃', ?_, ?_, ?_⟩
  · rw [ha]
    simp only [Iso.trans_hom, Category.assoc]
    rw [hα]
  · rw [hr₂, hb]
    simp only [Iso.trans_hom, Category.assoc]
    rw [hβ]
  · rw [hr₃, hc]
    simp only [Iso.trans_hom, Category.assoc]
    rw [hγ]
```

It was preceded by these local options:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Elaborating the resolved adjunction mates requires extra heartbeats.
```

## New

```lean
theorem relativeMV_cover_chain_square
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (A B A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ a.left)
      (e₂ : DerivedCategory.Q.obj B ≅ (b U).left ⊞ (b V).left)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅
        (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (b (U ⊓ V)).right),
      DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map β ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
        e₃.hom ≫ (b (U ⊓ V)).hom := by
  obtain ⟨A, B, A', B', t, t', α, β, H, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ⟩ :=
    relativeMV_direct_image_homotopy_comparison f f' g g' hpull K K' φ U V hcover
  obtain ⟨C, D, s, a, b, H', d₁, d₂, d₃, ha, hb, hc⟩ :=
    derivedPullback_cone_square_transposition g A B A' B' t t' α β H
  obtain ⟨T, i, c, hcomm, r₂, r₃, hr₂, hr₃⟩ :=
    CochainComplex.homotopy_square_cone_rectification s t' a b H'
  refine ⟨C, T, A', B', i, t', a, c, hcomm,
    d₁ ≪≫ e₁, r₂ ≪≫ d₂ ≪≫ e₂, r₃ ≪≫ d₃ ≪≫ e₃, e₁', e₂', e₃', ?_, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Category.assoc, hα] using
      congrArg (fun k ↦ k ≫ e₁'.hom) ha
  · simpa only [Iso.trans_hom, Category.assoc, hb, hβ] using
      congrArg (fun k ↦ k ≫ e₂'.hom) hr₂
  · simpa only [Iso.trans_hom, Category.assoc, hc, hγ] using
      congrArg (fun k ↦ k ≫ e₃'.hom) hr₃
```

Only the existing heartbeat option and comment remain. For the first component,
postcompose `ha` with `e₁'.hom` and simplify using `hα`. For the middle component,
postcompose `hr₂` with `e₂'.hom` and simplify using `hb` and `hβ`. For the cone
component, postcompose `hr₃` with `e₃'.hom` and simplify using `hc` and `hγ`.
Isomorphism composition and associativity identify the resulting equations with
the three required equations. In particular the third component is still the
specified homotopy-cone map, not a newly chosen triangle completion.

The node retains its statement, attachment and dependencies; its third proof
step and provenance describe the explicit postcomposition proof.

## Users

`tools/downstream.py --uses relativeMV_cover_chain_square` lists precisely the
following two modules as mentioning the declaration. There are seven downstream
modules in total. The single direct consumer is checked unchanged against the
new compiled item in a separate validation tree under the sandbox scratchpad.
No consumer adaptations are needed because the public interface is identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVCoverChainSquare | B4 | Rewrite the proof assembly and remove unnecessary normalization/transparency overrides. |
| Sheaf.AlgebraicGeometry.RelativeMVCoverRows | unclaimed | Same theorem, same witnesses and all three equations; source checked unchanged. |

Validation: the revised item compiled in a fresh validation tree in 27.8 s,
and the unchanged direct consumer compiled against it in 14.3 s. Both
`#print axioms` results are exactly `propext`, `Classical.choice`, `Quot.sound`.
There were no compiler warnings. Validation copies are outside the delivery's
`lean/` tree.

## Status

landed 20261021T100742-L-4132083 2026-10-21 (merge of deliver/B4/Sheaf.AlgebraicGeometry.RelativeMVCoverChainSquare)
