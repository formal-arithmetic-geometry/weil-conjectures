# relativeSupportEdge, relativeSupportProEdge and relativeSupportProRestriction

## Reason

The full module exceeded the 60-second compile limit. The edge proof combines
canonical derived comparisons whose inferred endpoints expand cohomology objects.
Name the existing natural-number/integer cohomology isomorphism with the recorded
sheaf as its explicit target, and evaluate that named map in the edge.

The pro-etale composites identify scalar forgetting of a restricted module sheaf
with restriction of the underlying abelian sheaf. Record that reflexive
identification at the coefficient level, derive it once, and compose it with the
canonical pro-etale comparison. Both composites then have explicit matching
endpoints. The three final inferred result types are stated explicitly as well.
Local irreducibility attributes hide implementations during instance search;
existing definitions retain their exported transparency. The three new
isomorphisms are irreducible constructions with explicit types.

The edge still uses exactly the existing single/right-derived-plus/homology
comparison. The inserted coefficient isomorphism is `Iso.refl`, and its derived
image is the identity by `Functor.map_id`. No coefficient, restriction arrow,
comparison normalization or orientation is changed. Targets using these maps
should receive the independent semantic review required for a definition repair.


The E2 repair's server compile again exceeded the file limit. The unique ordinary
comparison isomorphisms and derived evaluation now also state their inferred
result types explicitly (verbatim below). Their bodies and inferred mathematical
types do not change. Local irreducibility starts immediately after the matching
invertibility API is proved, including the scalar-forgetting derived comparison;
this prevents later instance search from reopening those implementations.
The support-kernel implementation is also hidden immediately after its ordinary
evaluation API; the global kernel construction temporarily restores its ordinary
transparency. The later private kernel comparison and finite-limit proof unfold the kernel
explicitly.
All exported definition bodies and their transparency remain unchanged by these
local attributes. The cohomology-sheaf implementation is similarly hidden after
its named derived comparison; only the final transport of geometric vanishing
unfolds it explicitly.

The repeated proof expanding `Functor.rightDerivedBaseChange_app` is now proved
once in the private, category-generic `relativeSupportDerivedBaseChange_isIso`.
Its evaluation, scalar-forgetting and pro-etale specializations use that lemma.
This proof-only factoring avoids expanding the same derived definition three
times with large concrete sheaf categories; it changes no public definition.

## Old

```lean
noncomputable def relativeSupportEdge
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) (W : U.Etale) :
    supportCohomology (pullback.snd i W.hom) n
        ((relativeSupportRestriction W).obj (relativeSupportCoefficient P U r)) ⟶
      (relativeSupportCohomologySheaf P i r n).obj.obj (op W) :=
  (asIso (relativeSupportDerivedEvaluation i W n)).inv.app
      (relativeSupportCoefficient P U r) ≫
    ((relativeSupportKernel i).grothendieckLeftEdgeMap (relativeSupportEvaluation W)
      (relativeSupport_evaluationAcyclic i W) n).app (relativeSupportCoefficient P U r) ≫
    (relativeSupportEvaluation W).map
      (((relativeSupportKernel i).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
        n).inv.app (relativeSupportCoefficient P U r))

noncomputable def relativeSupportModuleRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U : Scheme.{u}} (W : U.Etale) (r : ℤ) :=
  (localizationRestriction (ModuleCat.{u + 1} P.Coefficient) W.hom inferInstance).obj
    (relativeSupportModuleCoefficient P U r)

noncomputable def relativeSupportProEdge
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) (W : U.Etale) :=
  (asIso (relativeSupportProComparison P.Coefficient (pullback.snd i W.hom) n
    (relativeSupportModuleRestriction P W r))).inv ≫ relativeSupportEdge P i r n W

noncomputable def relativeSupportProRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) {W W' : U.Etale}
    (a : W' ⟶ W) :=
  (asIso (relativeSupportProComparison P.Coefficient (pullback.snd i W.hom) n
    (relativeSupportModuleRestriction P W r))).inv ≫
    relativeSupportClassRestriction P i r n a ≫
    relativeSupportProComparison P.Coefficient (pullback.snd i W'.hom) n
      (relativeSupportModuleRestriction P W' r)
```

```lean
noncomputable def relativeSupportEvaluationIso {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) :=
  Classical.choose (relativeSupportEvaluationIso_existsUnique i W)

noncomputable def relativeSupportDerivedEvaluation {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) (n : ℕ) :=
  Functor.rightDerivedBaseChange
    (β := relativeSupportRestriction W) (γ := 𝟭 AddCommGrpCat.{u + 1})
    ((Functor.rightUnitor _).hom ≫ (relativeSupportEvaluationIso i W).hom) n

noncomputable def relativeSupportGlobalIso {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] :=
  Classical.choose (relativeSupportGlobalIso_existsUnique i)
```

## New

```lean
@[irreducible] noncomputable def relativeSupportCohomologyIso
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) :
    ((relativeSupportKernel i).rightDerived n).obj (relativeSupportCoefficient P U r) ≅
      relativeSupportCohomologySheaf P i r n :=
  ((relativeSupportKernel i).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
    n).symm.app (relativeSupportCoefficient P U r)

noncomputable def relativeSupportEdge
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) (W : U.Etale) :
    supportCohomology (pullback.snd i W.hom) n
        ((relativeSupportRestriction W).obj (relativeSupportCoefficient P U r)) ⟶
      (relativeSupportCohomologySheaf P i r n).obj.obj (op W) :=
  (asIso (relativeSupportDerivedEvaluation i W n)).inv.app
      (relativeSupportCoefficient P U r) ≫
    ((relativeSupportKernel i).grothendieckLeftEdgeMap (relativeSupportEvaluation W)
      (relativeSupport_evaluationAcyclic i W) n).app (relativeSupportCoefficient P U r) ≫
    (relativeSupportEvaluation W).map
      (relativeSupportCohomologyIso P i r n).hom

noncomputable def relativeSupportModuleRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U : Scheme.{u}} (W : U.Etale) (r : ℤ) :
    Sheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) :=
  (localizationRestriction (ModuleCat.{u + 1} P.Coefficient) W.hom inferInstance).obj
    (relativeSupportModuleCoefficient P U r)

@[irreducible] noncomputable def relativeSupportRestrictionCoefficientIso
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U : Scheme.{u}} (W : U.Etale) (r : ℤ) :
    (moduleAbelianForget P.Coefficient W.left).obj (relativeSupportModuleRestriction P W r) ≅
      (relativeSupportRestriction W).obj (relativeSupportCoefficient P U r) :=
  Iso.refl _

@[irreducible] noncomputable def relativeSupportProIso
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) (W : U.Etale) :
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj
        (ProEtale.supportCohomology (pullback.snd i W.hom) P.Coefficient n
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W.left).obj
            (relativeSupportModuleRestriction P W r))) ≅
      supportCohomology (pullback.snd i W.hom) n
        ((relativeSupportRestriction W).obj (relativeSupportCoefficient P U r)) :=
  (asIso (relativeSupportProComparison P.Coefficient (pullback.snd i W.hom) n
    (relativeSupportModuleRestriction P W r))).symm ≪≫
      ((supportSections (pullback.snd i W.hom)).rightDerived n).mapIso
        (relativeSupportRestrictionCoefficientIso P W r)

noncomputable def relativeSupportProEdge
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) (W : U.Etale) :
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj
        (ProEtale.supportCohomology (pullback.snd i W.hom) P.Coefficient n
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W.left).obj
            (relativeSupportModuleRestriction P W r))) ⟶
      (relativeSupportCohomologySheaf P i r n).obj.obj (op W) :=
  (relativeSupportProIso P i r n W).hom ≫ relativeSupportEdge P i r n W

noncomputable def relativeSupportProRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) {W W' : U.Etale}
    (a : W' ⟶ W) :
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj
        (ProEtale.supportCohomology (pullback.snd i W.hom) P.Coefficient n
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W.left).obj
            (relativeSupportModuleRestriction P W r))) ⟶
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj
        (ProEtale.supportCohomology (pullback.snd i W'.hom) P.Coefficient n
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W'.left).obj
            (relativeSupportModuleRestriction P W' r))) :=
  (relativeSupportProIso P i r n W).hom ≫
    relativeSupportClassRestriction P i r n a ≫ (relativeSupportProIso P i r n W').inv

```

```lean
noncomputable def relativeSupportEvaluationIso {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) :
    relativeSupportKernel i ⋙ relativeSupportEvaluation W ≅
      relativeSupportRestriction W ⋙ supportSections (pullback.snd i W.hom) :=
  Classical.choose (relativeSupportEvaluationIso_existsUnique i W)

noncomputable def relativeSupportDerivedEvaluation {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) (n : ℕ) :
    (relativeSupportKernel i ⋙ relativeSupportEvaluation W).rightDerived n ⋙
        𝟭 AddCommGrpCat.{u + 1} ⟶
      relativeSupportRestriction W ⋙ (supportSections (pullback.snd i W.hom)).rightDerived n :=
  Functor.rightDerivedBaseChange
    (β := relativeSupportRestriction W) (γ := 𝟭 AddCommGrpCat.{u + 1})
    ((Functor.rightUnitor _).hom ≫ (relativeSupportEvaluationIso i W).hom) n

noncomputable def relativeSupportGlobalIso {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] :
    supportSections i ≅
      relativeSupportKernel i ⋙ relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U)) :=
  Classical.choose (relativeSupportGlobalIso_existsUnique i)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Named canonical cohomology comparison in the edge; explicit coefficient normalization and pro-etale comparison isomorphism in the pro-etale composites. The module restriction body is unchanged. |

The current downstream scan lists 18 modules below the item. The exact-name
`--uses` scans for all seven existing declarations find only the item itself; none of those
17 modules directly uses a changed declaration. No other module directly uses these changed definitions. The theorem's separate
finite-stalk correction and its consumer audit are recorded in
`A3-relative-support-finite-stalks.md`. The definitions denote the same canonical
maps and coefficients.

## Status

landed 20261022T013344-L-3550290 2026-10-22 (merge of deliver/A3/Sheaf.Paper.RelativeSupportBottomDescent)
