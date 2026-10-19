# uniformConstructibleExt_exists and uniformConstructibleExt_cutoff

## Reason

Preserve the complete compiled existence argument and cutoff-finiteness argument while
flagging the mismatch between the original explicit clause and the repaired rational lemma.
The existing uniformConstructibleExt signature is unchanged. No definitions change.

## Old

The two added declarations did not exist. The sole existing theorem remains unchanged.

## New

```lean
theorem uniformConstructibleExt_exists
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (_hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k]
    (_hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ C : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ∃ d : ℕ, ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
        ∀ q : ℕ, d < q → Subsingleton (Abelian.Ext C.obj N.obj q))

theorem uniformConstructibleExt_cutoff
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k]
    (hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (S Z U : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
    [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j] :
    ∃ d : ℕ, (d : WithTop ℕ) =
      relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j +
        cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S + 2
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.UniformConstructibleExt | X9 | Adds two proved partial-clause declarations. |
| Sheaf.Paper.IndHeartIIVanishing | not adapted | Same imports and signatures available. |
| Sheaf.Paper.FiniteWindow | not adapted | Same imports and signatures available. |
| Sheaf.Paper.ConstructibleCompactness | not adapted | Same imports and signatures available. |
| Sheaf.Paper.FiniteWindowBounded | not adapted | Same public imports and signatures available. |

The new names have no existing users. No existing signature, public import, instance or
definition changes, so existing consumers require no adaptation. The completed dependency scan found 207 transitive importers and no textual use of
`uniformConstructibleExt` outside its own declaration; the four direct importers were read
and require no changes. Their statements remain identical, as do all target statements.

## Status

landed 20261019T034351-L-425989 2026-10-19 (merge of deliver/X9/Sheaf.Paper.UniformConstructibleExt)
