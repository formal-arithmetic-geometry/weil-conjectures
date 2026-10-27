# henselian_pointed_residual_cover_lift

## Reason

The stage-3 preflight requires a change record for added module commands. This packet
adds private proved helpers inside sections, local instance registrations for the affine
stages and cover, local irreducibility attributes for private pointed equivalences, and
elaboration options. These support the proof of the original theorem. Existing public
signatures, definitions, and public imports are verbatim unchanged. The instance registrations are local to the geometry section and the irreducibility
attributes are local to the enclosing namespace; there are no new global instances.

## Old

```lean
theorem henselian_pointed_residual_cover_lift (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) [ConnectedSpace (Spec (.of (B ⧸ J)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (B ⧸ J)))
    (c : Cocone (ObjectProperty.ι (fun A : Under (CommRingCat.of B) ↦
      Etale (Spec.map A.hom) ∧ Function.Bijective
        (Ideal.quotientMap (J.map A.hom.hom) A.hom.hom Ideal.le_comap_map))))
    (hc : IsColimit c) :
    ∃ (hE : ConnectedSpace (Spec c.pt.right))
      (h : Function.Bijective
        (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom Ideal.le_comap_map)),
      IsNoetherianRing c.pt.right ∧ HenselianRing c.pt.right (J.map c.pt.hom.hom) ∧
      J.map c.pt.hom.hom ≤ Ideal.jacobson ⊥ ∧
      RingHom.IndEtaleAcrossUniverses c.pt.hom.hom ∧
      (J = ⊥ → Function.Bijective c.pt.hom.hom) ∧
      Nonempty (@LiftData B _ J c.pt.right c.pt.hom hE inferInstance h Ω _ _ s)
```

The theorem body was `by sorry`. No helper declarations or helper attributes existed.

## New

```lean
theorem henselian_pointed_residual_cover_lift (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) [ConnectedSpace (Spec (.of (B ⧸ J)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (B ⧸ J)))
    (c : Cocone (ObjectProperty.ι (fun A : Under (CommRingCat.of B) ↦
      Etale (Spec.map A.hom) ∧ Function.Bijective
        (Ideal.quotientMap (J.map A.hom.hom) A.hom.hom Ideal.le_comap_map))))
    (hc : IsColimit c) :
    ∃ (hE : ConnectedSpace (Spec c.pt.right))
      (h : Function.Bijective
        (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom Ideal.le_comap_map)),
      IsNoetherianRing c.pt.right ∧ HenselianRing c.pt.right (J.map c.pt.hom.hom) ∧
      J.map c.pt.hom.hom ≤ Ideal.jacobson ⊥ ∧
      RingHom.IndEtaleAcrossUniverses c.pt.hom.hom ∧
      (J = ⊥ → Function.Bijective c.pt.hom.hom) ∧
      Nonempty (@LiftData B _ J c.pt.right c.pt.hom hE inferInstance h Ω _ _ s)
```

The theorem is proved. Private helper definitions construct stages, colimit cocones,
pointed equivalences, and their canonical comparisons. Every private theorem is proved.
The local `stageAffine` and `coverAffine` instances provide affine schemes during this
proof only. `smallPointedEquiv` and `smallFiniteIso` are locally irreducible after their
API lemmas; scoped transparency options prevent costly unfolding during elaboration.
No target statement or definition used in a target changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FundamentalGroup.HenselianPointedResidualCover | Z7 | Existing theorem proved; public interface unchanged. |

No downstream Lean module currently imports this item. Its unfinished DAG parents
remain intact and can use the original theorem signature. No consumer adaptation is
necessary.

## Status

landed 20261024T022557-L-3009725 2026-10-24 (merge of deliver/Z7/Sheaf.AlgebraicGeometry.FundamentalGroup.HenselianPointedResidualCover)
