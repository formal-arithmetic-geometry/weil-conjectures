# AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_isSeparable

## Reason

The arbitrary Algebra κB k′ instance in the original statement is unrelated to
(Spec.preimage ρB).hom. Separability in the conclusion can therefore refer to a
completely different embedding from the geometric hypotheses. Require their equality.
This is an intermediate theorem, not one of the five Challenge targets.

For example, let F be an algebraic closure of Q(t), and let L be an algebraic
closure of Q(t,u). Embed F in L by a extending t↦u and by b extending t↦t.
The element a(t) is transcendental over b(F). Take S=T=Spec F, A=B=F,
k=k′=Ω=L, g=ι=ν=identity and σ=τ=Spec(a). The strict henselization of
Spec F is Spec F. Transport a through the canonical residue-field isomorphisms
to choose ρA and ρB; then all geometric equations hold. An algebra instance
induced by b makes the original separability conclusion false. The correction
requires a instead. No compiled geometric counterexample is claimed here.

Source: Stacks Tags 04HX and 095T use the given geometric residue embeddings.
The correction adds exactly that compatibility, already present at the only call.

## Old

```lean
theorem Etale.compatibleStrictHenselization_residue_isSeparable
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    [Algebra (IsLocalRing.ResidueField B) k'] :
    ∀ x : IsLocalRing.ResidueField A,
      IsSeparable (IsLocalRing.ResidueField B)
        ((Spec.preimage (ι ≫ ρA)).hom x)
```

## New

```lean
theorem Etale.compatibleStrictHenselization_residue_isSeparable
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    [Algebra (IsLocalRing.ResidueField B) k']
    (hAlgebra : algebraMap (IsLocalRing.ResidueField B) k' = (Spec.preimage ρB).hom) :
    ∀ x : IsLocalRing.ResidueField A,
      IsSeparable (IsLocalRing.ResidueField B)
        ((Spec.preimage (ι ≫ ρA)).hom x)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability | B3 | Corrected intermediate signature; proved from the single-model comparison. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial | unclaimed | Forced proof-only adaptation: append rfl to the separability call; every signature and visibility stays identical. |

`tools/downstream.py --uses compatibleStrictHenselization_residue_isSeparable`
finds only these two textual users. All 101 import descendants retain their
statements: the sole caller supplies the new hypothesis by definitional equality.
No definition has changed, so no target's meaning or elaborated type changes.

The single-model comparison module is new and completely proved by transporting
the existing strictHenselizationResidue theorem. Its existential residue embedding
is used only in the proof, not in a definition; its structural factorization
characterizes the embedding uniquely. No new theorem hole remains.

## Status

landed 20261012T225257-L-1800483 2026-10-12 (merge of deliver/B3/Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability)
