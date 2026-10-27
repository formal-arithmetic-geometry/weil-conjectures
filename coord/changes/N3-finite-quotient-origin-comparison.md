# AlgebraicGeometry.Scheme.LisseFiniteQuotientEtaleOriginCore

## Reason

The core had no comparison between its level and K. Its constructor already has
an isomorphism nu*L to the fixed-coefficient pullback of K, but discarded it.
Lissity and cohomology vanishing alone cannot recover that isomorphism: choosing
level=0 satisfies the old level fields even for a nonzero finite constant K.
With identity charts and E=0 the transport conclusion would incorrectly imply
0 isomorphic to K. This is the defect already noted in the parent transport module.

Retain the actual origin comparison at V after restriction along the canonical
completion-quotient map. The constructor proves the new field by scalar cancellation,
comparison/pullback coherence, and inverse-image composition, using its existing eL.
No new existence theorem, axiom, sorry, or arbitrary data choice is introduced.

The two new concrete public functors expose the already used fixed-coefficient
encoding and its composite with quotient restriction and pullback. Public signatures
contain only public definitions; the encoding equivalence is the already proved
private scalarRestriction result, with the same concrete underlying construction.
The module additionally publicly imports the scalar-restriction definition used by
the new field. Existing definitions of the final origin and all target signatures stay
unchanged: the repaired core is an intermediate object used only in their proofs.

## Old

```lean
structure LisseFiniteQuotientEtaleOriginCore
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (V : Y.Etale) where
  level : DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
  lisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj level)
  vanishing : ∀ q : ℤ,
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj level)
  refinementLisse : ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj V) (q : ℤ),
    IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj K)))
```

## New

```lean
structure LisseFiniteQuotientEtaleOriginCore
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (V : Y.Etale) where
  level : DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
  lisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj level)
  vanishing : ∀ q : ℤ,
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj level)
  refinementLisse : ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj V) (q : ℤ),
    IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj K)))
  comparison : Nonempty
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)))
        V.left).mapDerivedCategory.obj
      ((Sheaf.restrictScalars V.left.smallEtaleTopology
        (constantAdicQuotientMap d.ideal n)).mapDerivedCategory.obj level) ≅
      (finiteQuotientOriginPullback (V.hom ≫ g) d n).obj K)
```

The additional public declarations in the core module are
`finiteQuotientOriginEncoding`, `finiteQuotientOriginEncoding_additive`,
`finiteQuotientOriginEncoding_equivalence`, and `finiteQuotientOriginPullback`.
The existing constructor's signature text is unchanged; its result now retains
comparison, proved by the final branch of its proof. The declaration and module
attachments of the core node list the new public API and the corrected statement.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.LisseFiniteQuotientEtaleOriginCore | unclaimed | Retain comparison and prove its constructor field; expose concrete fixed-coefficient API. |
| Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransportMap | N3 | Prove the assigned theorem, without added holes, by composing and reflecting isomorphisms. |
| Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransport | unclaimed | Existing proof and signature retained; remove obsolete STATEMENT-DISPUTED comment. |
| Sheaf.Paper.LisseFiniteQuotientEtaleOrigin | unclaimed | Existing proof consumes the repaired constructor and transport unchanged; compile as an unchanged direct consumer. |

These are all direct importers and all modules mentioning the core record or its
constructor. No other module constructs or deconstructs the core record. The DAG
citers are the assigned map, parent transport, and final origin nodes. All three
continue to hold; the final origin's public fields and target meanings do not change.
The blueprint unit's proper-base-change route is preserved.

## Status

landed 20261027T234119-L-1770 2026-10-27 (merge of deliver/N3/Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransportMap)
