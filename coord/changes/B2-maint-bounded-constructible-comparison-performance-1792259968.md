# boundedConstructibleTensorObjCompatibility and boundedConstructibleHomObjCompatibility

## Reason

The bounded-constructible item repeatedly failed because the componentwise identity
natural-isomorphism constructions expand the large monoidal and internal-Hom structures.
A fresh copy of the current library module times out at 60 seconds. Both functors in each
comparison are definitionally equal; using the identity isomorphism directly avoids
reconstructing its components and discharging redundant naturality goals.

This is a maintenance implementation repair, not proof progress on the three remaining
mathematical obligations. All signatures, names, attributes, visibility and imports stay
identical. Both hom and inverse still have identity components. No axiom or sorry is added.

## Old

```lean
noncomputable def boundedConstructibleTensorObjCompatibility
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Λ⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

noncomputable def boundedConstructibleHomObjCompatibility
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleHom Λ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Λ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
```

## New

```lean
noncomputable def boundedConstructibleTensorObjCompatibility
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Λ⟧).obj K.obj :=
  Iso.refl _

noncomputable def boundedConstructibleHomObjCompatibility
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleHom Λ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Λ⟧).obj (op K.obj) :=
  Iso.refl _
```

## Users

The source-only downstream check found 206 transitive importing modules. Its named-use
search and a separate source search found each changed name only at its own declaration.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | B2 | Two identity natural-isomorphism constructions simplified; signatures and component maps preserved. |

No consumer adaptation is needed. The unchanged BoundedConstructibleAdditive and
BoundedConstructibleBraided modules were compiled against the repaired module in a
separate maintenance mirror.

## Validation

All checks used tools/lean_file.sh, one file at a time, with SHEAF_FILE_TIMEOUT=60 and the
isolated SHEAF_GROUP=B2-maint-bc-1792259968. No lake build was run.

- Original module: timeout at 60 s.
- Repaired scratch copy: 37.4 s, exit 0.
- Repaired library module, producing the maintenance-mirror artifact: 42.2 s, exit 0.
- BoundedConstructibleAdditive: 4.1 s, exit 0.
- BoundedConstructibleBraided: 4.0 s, exit 0; an existing long-line warning at line 65 remains.

The declaration diff reports only the two body changes: no statement, public-import,
public-declaration or sorry-set change. The same three original mathematical holes remain.
Logs and the original snapshot are under lean/.sandbox/B2-maint-bc-1792259968/.

## Worker handoff

Refresh the sandbox against the maintenance commit before continuing. In particular,
copy these two definitions from the new base verbatim (their bodies are Iso.refl _);
retain the rest of the worker proof and node work. Earlier sandbox alternatives using
componentwise constructions, commTensorLeft or liftCompιIso are not the maintenance base.
A delivery that carries one of those alternatives still differs from the base and can
still be refused by the upstream-body gate.

The ell-adic coefficient corrections are already on the server in commits 7360fe485e
and 6153cc738e. Preserve those hypotheses. Do not repeat the earlier unrestricted-coefficient
repair or claim the remaining finiteness theorems have been proved by this maintenance.

## Status

open: maintenance source repair compiled; normal global-build verification remains with
the pipeline. This task changes no launcher, landing or review tool and no dispatcher state.
The existing worker sandbox is preserved.
