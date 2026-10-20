# FieldTheory.shearPolynomial and FieldTheory.shearOmega

## Reason

The proof constructs polynomial shear automorphisms and extends them to the fraction
field. These new private constructions have large bodies. Their irreducibility
attributes keep elaboration from repeatedly unfolding them; the proved coordinate
and inverse-coordinate equations supply their API. The static interface checker
flags the attribute commands, so this record documents them. Every pre-existing
public declaration retains its exact signature, visibility, definition, and attributes.

## Old

Neither private declaration existed. No original attribute is modified.

## New

```lean
@[irreducible] private noncomputable def shearPolynomial
    (K : Type u) [Field K] (n : ℕ) (c : Fin n → K) (j l : Fin n) (m : ℕ) :
    MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K := by
  let P := invariantPolynomial K n c j l
  let f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
    MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + MvPolynomial.C (c i) * P ^ m)
  let g : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
    MvPolynomial.aeval (fun i ↦ MvPolynomial.X i - MvPolynomial.C (c i) * P ^ m)
  have hf : f P = P := by simp [f, P, invariantPolynomial]; ring
  have hg : g P = P := by simp [g, P, invariantPolynomial]; ring
  exact AlgEquiv.ofAlgHom f g
    (by ext1 i; simp only [AlgHom.comp_apply, g, MvPolynomial.aeval_X, map_sub,
      map_mul, map_pow, hf]; simp [f])
    (by ext1 i; simp only [AlgHom.comp_apply, f, MvPolynomial.aeval_X, map_add,
      map_mul, map_pow, hg]; simp [g])

@[irreducible] private noncomputable def shearOmega
    (K : Type u) [Field K] (n : ℕ) (c : Fin n → K) (j l : Fin n) (m : ℕ) :
    bertiniOmega K n ≃ₐ[K] bertiniOmega K n :=
  IsFractionRing.algEquivOfAlgEquiv (shearPolynomial K n c j l m)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.FieldTheory.BertiniFieldExtension | Z8 | Constructs and uses the new private shears through proved equations. |
| Sheaf.AlgebraicGeometry.BertiniIrreducibleMember | T5 | Direct importer; uses only the unchanged public theorem and definitions. No adaptation. |

No downstream module can name either new private declaration. No target definition
or target statement changes. The public import list is unchanged; added imports are
proof-only.

## Status

landed 20261020T131240-L-1265991 2026-10-20 (merge of deliver/Z8/Sheaf.FieldTheory.BertiniFieldExtension)
