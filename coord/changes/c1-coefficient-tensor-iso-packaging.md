# AlgebraicGeometry.Scheme.CoefficientTensorChain.tensorIso

## Reason

Profiling the item after local transparency improvements and a generic totalization
API still found more than 60 seconds of checking in one file. Move the existing
naturality theorem and tensorIso definition to supporting modules, publicly
re-exported by the item. The full declaration names, signatures and definition
body are unchanged. Add a proved summand API for the same components to avoid
unfolding their monoidal presentation at the generic totalization call.

## Old

In `Sheaf.Paper.ProEtaleCoefficientTensorChainData`:

```lean
def tensorIso (o : SheafOfModules.RingIsoTensorTransport
    (J := ProEt.topology X)
    (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c) :
    total X S ⋙ (pbcRestrict c.hom).mapHomologicalComplex (.up ℤ) ≅
      (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).prod
        ((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ))) ⋙
        total X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  NatIso.ofComponents (fun Z ↦ o.totalIso Z.1 Z.2)
    (fun v ↦ tensorIso_naturality f R S c o _ _ v)
```

## New

In `Sheaf.Paper.ProEtaleCoefficientTensorIso`, publicly imported by the old module:

```lean
def tensorIso (o : SheafOfModules.RingIsoTensorTransport
    (J := ProEt.topology X)
    (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c) :
    total X S ⋙ (pbcRestrict c.hom).mapHomologicalComplex (.up ℤ) ≅
      (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).prod
        ((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ))) ⋙
        total X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  NatIso.ofComponents (fun Z ↦ o.totalIso Z.1 Z.2)
    (fun v ↦ tensorIso_naturality f R S c o _ _ v)
```

The accompanying tensorIso_naturality theorem is moved to
Sheaf.Paper.ProEtaleCoefficientTensorIsoNaturality with its original
signature and name. Its proof uses the proved generic mapTotalBifunctor API
instead of unfolding the total functor on each sheaf instance. This is a relocation of
existing data, with the same normalization; no target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleCoefficientTensorChainData | C1 | Publicly re-exports the relocated declarations and uses their summand API. |
| Sheaf.Paper.ProEtaleCoefficientTensorRepresentativeSquare | unclaimed | Original importer exceeded 60 seconds; inline the existing short diagram-pasting calculation to avoid expensive specialization. Signatures and public imports stay identical. |
| Sheaf.Paper.ProEtaleCoefficientTensorCompatibility | unclaimed | Uses the same tensorIso declaration through the representative-square module; its name, type and body are unchanged. |

The downstream name search gives 120 textual matches for tensorIso, most referring
to other namespaces. Inspection of qualified references and namespace openings
finds the item and these two actual users of CoefficientTensorChain.tensorIso.

The original representative-square importer failed the required consumer check:
`NOT ACCEPTED: this compile took 64 s > 60 s, the limit for one file`.
The adaptation inlines the body of its proved private paste_tensor_square helper
at its sole call and removes that now-unused helper. It uses morphisms instead
of whole natural transformations for the two compared expressions, and gives the
representative arrows explicit source and target types. It composes the same given
squares by naturality and functoriality; no exported signature or definition
changes. Profiling identified the helper specialization as an expensive proof
conversion. It uses the new proved representative-normalization API and local
irreducibility of proEtaleCanonicalTensorComparison and
proEtaleTensorPullbackTotalIso; those definitions are unchanged globally.
The proof route remains identical. The consumer's node records the new API
dependency, without changing its statement or statement dependencies.

## Status

landed 20261027T123423-L-2295156 2026-10-27 (merge of deliver/C1/Sheaf.Paper.ProEtaleCoefficientTensorChainData)
