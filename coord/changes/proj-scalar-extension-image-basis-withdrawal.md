# AlgebraicGeometry.Proj.scalarExtension_image_basicOpen_isBasis

## Reason

STATEMENT-DISPUTED: the asserted basis is false. Take a field k, R=k, S=k[t],
A=k[x], B=k[t][x], graded by degree in x, with the canonical beta and psi.
Every B_n is the S-span of psi(A_n), and both irrelevant ideals are (x).
Each positive homogeneous element of A is c*x^n. Its image standard open is
empty if c=0 and all of Proj B otherwise. But Proj B=Spec k[t] has the
nonempty proper open D(t). The image opens are a cover, not a basis.
The old proof confused membership of one prime with containment of opens.

Withdraw the false split and repair its only consumer by the correct affine
cover argument. This is an intermediate statement repair, not a target change.
No existing definition or source-library declaration is changed.

## Old

```lean
theorem scalarExtension_image_basicOpen_isBasis
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ
      (HomogeneousIdeal.irrelevant 𝒜)) :
    TopologicalSpace.Opens.IsBasis (Set.range
      (fun i : Σ n : PNat, 𝒜 (n : ℕ) ↦ basicOpen ℬ (ψ (i.2 : A))))
```

## New

Withdraw the declaration: the item module is kept as an empty module
(`module` and the comment "Withdrawn: no declarations remain."; it is not listed
in deleted.txt). Keep its DAG node, mark the counterexample in its proof, empty
its proof_deps, and remove its lean attachment.
The statement of scalarExtension_twistMap_basicOpen_bijective stays verbatim.
Its proof uses Proj.mapAffineOpenCover, complete-chart bijectivity, quasi-coherence
of the two twists and tensor pullback, and the affine-cover isomorphism criterion.
The independent geometric step isQuasicoherent_twist is a new named theorem;
its proof is still sorry and is reported as such, not as a proof of the false lemma.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjScalarExtensionImageBasicOpenBasis | Q4 | False declaration withdrawn. |
| Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart | unclaimed in current snapshot | Replace its false-basis proof; preserve its statement and public imports. |

The downstream name scan finds only these two modules. All other transitive
consumer statements stay unchanged. The DAG has exactly one parent, the chart
node, whose proof dependencies are updated in this packet. The unit realizes
neither this false split nor this local proof as a mandatory unit step. The
current rework table has no quarantined parent or assigned build repair.

## Status

landed 20261028T055735-L-803123 2026-10-28 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.ProjScalarExtensionImageBasicOpenBasis)
