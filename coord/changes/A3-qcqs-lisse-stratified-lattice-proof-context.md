# qcqs_lisse_stratified_integral_lattices proof context

## Reason

Close the assigned theorem from existing affine etale lattices, finite affine cover
assembly, constructible finite-etale stratification, localization and trace-image descent.
The proof uses private generic coefficient predicates and helpers to avoid expensive
kernel conversion of concrete module categories. Preflight requests this record for the
additional local attribute commands. Four original unit-route imports are retained:
FiniteEtaleTraceImage, CartesianCoefficients, ContinuousLatticeSum and
LatticeSheafLocallyConstant. No unit statement or realization is removed.

Every existing public signature and public import stays unchanged. No consumer needs
adaptation; all added declarations are private, proved or explicitly constructed. There
is no change to an existing definition or to any target's meaning.

## Old

The original signature, verbatim (body `by sorry`):

```lean
theorem qcqs_lisse_stratified_integral_lattices
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) T),
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) M →
      ∃ S : Scheme.FiniteLocallyClosedStratification T,
        (∀ s : Fin S.n, Topology.IsConstructible (S.stratum s)) ∧
        ∀ s : Fin S.n,
          ∃ B : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
              (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (S.domain s)),
            IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) B ∧
            ∃ ι : B ⟶ (Mod.comap (padicIntegersToPadicSubfield (S.domain s) ℓ E)).obj
                ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
                  (S.immersion s)).obj M),
              Mono ι ∧ IsIso (Mod.extendHom
                (padicIntegersToPadicSubfield (S.domain s) ℓ E) ι)) ∧
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) M →
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ)
        (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj F.1) T)),
        IsLisseCoefficientModule (Profinite.continuousMapRingObj F.1) L ∧
        ∃ e : (Mod.extendScalars
            (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) T)).obj L ≅ M,
          ∃ S : Scheme.FiniteLocallyClosedStratification T,
            (∀ s : Fin S.n, Topology.IsConstructible (S.stratum s)) ∧
            ∀ s : Fin S.n,
              ∃ B : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
                  (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) (S.domain s)),
                IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ F.1) B ∧
                ∃ ι : B ⟶ (Mod.comap (padicIntegersToPadicSubfield (S.domain s) ℓ F)).obj
                    ((CondensedRing.upperStar (Profinite.continuousMapRingObj F.1)
                      (S.immersion s)).obj L),
                  Mono ι ∧
                  IsIso (Mod.extendHom (padicIntegersToPadicSubfield (S.domain s) ℓ F) ι) ∧
                  IsIso
                    ((Mod.extendScalarsComp (padicIntegersToPadicSubfield (S.domain s) ℓ F)
                      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F)
                        (S.domain s))).hom.app B ≫
                      (Mod.extendScalars (coefficientMap
                        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) (S.domain s))).map
                          (Mod.extendHom (padicIntegersToPadicSubfield (S.domain s) ℓ F) ι) ≫
                      (CondensedRing.pullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F)
                        (S.immersion s)).hom.app L ≫
                      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
                        (S.immersion s)).map e.hom))
```

The original file had no local reducibility or image-instance priority commands.

## New

The public signature stays verbatim:

```lean
theorem qcqs_lisse_stratified_integral_lattices
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) T),
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) M →
      ∃ S : Scheme.FiniteLocallyClosedStratification T,
        (∀ s : Fin S.n, Topology.IsConstructible (S.stratum s)) ∧
        ∀ s : Fin S.n,
          ∃ B : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
              (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (S.domain s)),
            IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) B ∧
            ∃ ι : B ⟶ (Mod.comap (padicIntegersToPadicSubfield (S.domain s) ℓ E)).obj
                ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
                  (S.immersion s)).obj M),
              Mono ι ∧ IsIso (Mod.extendHom
                (padicIntegersToPadicSubfield (S.domain s) ℓ E) ι)) ∧
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) M →
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ)
        (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj F.1) T)),
        IsLisseCoefficientModule (Profinite.continuousMapRingObj F.1) L ∧
        ∃ e : (Mod.extendScalars
            (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) T)).obj L ≅ M,
          ∃ S : Scheme.FiniteLocallyClosedStratification T,
            (∀ s : Fin S.n, Topology.IsConstructible (S.stratum s)) ∧
            ∀ s : Fin S.n,
              ∃ B : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
                  (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) (S.domain s)),
                IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ F.1) B ∧
                ∃ ι : B ⟶ (Mod.comap (padicIntegersToPadicSubfield (S.domain s) ℓ F)).obj
                    ((CondensedRing.upperStar (Profinite.continuousMapRingObj F.1)
                      (S.immersion s)).obj L),
                  Mono ι ∧
                  IsIso (Mod.extendHom (padicIntegersToPadicSubfield (S.domain s) ℓ F) ι) ∧
                  IsIso
                    ((Mod.extendScalarsComp (padicIntegersToPadicSubfield (S.domain s) ℓ F)
                      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F)
                        (S.domain s))).hom.app B ≫
                      (Mod.extendScalars (coefficientMap
                        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) (S.domain s))).map
                          (Mod.extendHom (padicIntegersToPadicSubfield (S.domain s) ℓ F) ι) ≫
                      (CondensedRing.pullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F)
                        (S.immersion s)).hom.app L ≫
                      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
                        (S.immersion s)).map e.hom))
```

The theorem has a complete proof, and all new private helpers are proved. The sole
new data-valued construction, `latticePullbackIso`, is the explicit composite of the
coefficient pullback comparison, pulled comparison, pullback equation and functor
composition comparisons. It is not chosen from an unproved existence statement.
The other new definitions are propositions or bundles of actual coefficient data.

The added local context commands are:

```lean
attribute [local irreducible] CondensedRing.pullIso CondensedRing.upperStarComp
  Mod.extendScalarsComp
attribute [local instance 2000] Limits.HasImages.has_image
attribute [local irreducible] latticePullbackIso

```

The finite-field helpers and final theorem use scoped elaboration options:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
```

These attributes are explicitly local, and the options affect only elaboration of the
following declaration. None changes the interface visible to importing modules. No public
instance, simp rule, notation or attribute is added. The original public imports remain.
The new proof imports are private. The item compiled without warnings in 29.5 seconds
before restoring the protected unit-route imports.

## Users

The read-only command `tools/downstream.py Sheaf.Paper.QcqsLisseStratifiedIntegralLattices
--uses qcqs_lisse_stratified_integral_lattices` found zero current Lean downstream modules
and one textual use, the item itself. Unfinished DAG parents may still use its statement;
that statement and its Lean attachment stay unchanged. No withdrawal is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QcqsLisseStratifiedIntegralLattices | A3 | Existing public interface unchanged; complete proof and private context only. |

## Status

landed 20261023T230338-L-3417237 2026-10-23 (merge of deliver/A3/Sheaf.Paper.QcqsLisseStratifiedIntegralLattices)
