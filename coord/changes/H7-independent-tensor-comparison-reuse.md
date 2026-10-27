# SheafOfModules.CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison

## Reason

The shared-size record duplicates the existing common record
`SheafOfModules.CanonicalRingedTensorComparisonOnSmallSites`. Follow the stage-3
rule for duplicate definitions by making this interface an abbreviation. It retains
the actual site sizes `s,h`, and the ring, module and set universe `max(s,h)`.

All five fields have exactly their original meaning: `q` is the scalar insertion,
`q_one` fixes insertion of `1 tensor m`, `mu` is the same oriented tensor
isomorphism, and `naturality` and `pure` retain their complete original equations.
The common record factors their types into named definitions, all of which unfold
to the original expressions. This also avoids regenerating the expanded duplicate
record declarations. Zero rings, zero modules and empty sites require no exceptions.
Target statements using this definition are reopened for the definition review
required by AGENTS.md section 4; no target statement is edited.

The two original holes are proved using the existing independent tensorator,
scalar-extension generators and an explicit unit construction. The scalar unit is
sectionwise tensor multiplication followed by sheafification; the right-unitor
formula follows from Mathlib’s lax monoidal unitality and counit naturality. The generic
`CochainTensorCoherenceData` imports this item and cannot be its proof dependency.
Its source and every consumer remain unchanged. Private proof helpers retain
independent coefficient and site universes, then specialize to the public shared-size
theorems. Both public theorem signatures, all other retained public signatures and all
original public imports remain verbatim. The common record is imported directly
for its public abbreviation. Private helpers use a generic rank-one linear
equivalence and an explicit-unitor API, keeping the large localization structure
abstract. Local instance bindings in the total definitions use `let` with the
same values, and the original transparency override is no longer needed. The preadditivity proof now reuses
`cochainModulesPreadditive`. All kernel and linter checks remain enabled.

The shared-size scope locally prioritizes Mathlib's existing
`hasSheafCompose_of_preservesLimitsOfSize` instance. Both site sizes fit `max(s,h)`;
this chooses a smaller proof of the same proposition, with no new hypothesis or data.

## Old

```lean
structure CanonicalRingedTensorComparison where
  /-- Scalar-extension insertion, as a map of underlying sheaves of sets. -/
  q : ∀ M : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj RI) ⋙
        sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{max s h})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S) ⋙
        sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{max s h})).obj (L.obj M))
  /-- Insertion is specifically m mapped to 1 tensor m. -/
  q_one : ∀ (M : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R))
      (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W),
    (q M).hom.app W m = (eqToHom (hobj M).symm).val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂
        CommRingCat.{max s h}
      RingCat.{max s h})).obj S).obj)).unit.app
        (changeOfRingsPresheaf.{h, s, max s h} c (I.modules.obj M))).app W
          ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m))
  /-- Tensor preservation with the orientation of 07A4. -/
  mu : ∀ M N : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N)
  /-- Naturality in both variables. -/
  naturality : ∀ {M M' N N' : SheafOfModules.{max s h} ((sheafCompose JC (forget₂
    CommRingCat.{max s h}
      RingCat.{max s h})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
    L.map ((monoidalCategory R).tensorHom f g) ≫ (mu M' N').hom =
      (mu M N).hom ≫ (monoidalCategory S).tensorHom (L.map f) (L.map g)
  /-- Canonical generalized pure-tensor formula, rather than an arbitrary tensor iso. -/
  pure : ∀ (M N : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj
      R)) (Z : Sheaf JC (Type (max s h)))
    (x : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{max s h})).obj M))
    (y : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{max s h})).obj N))
    (z : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{max s h})).obj
        ((monoidalCategory R).tensorObj M N))),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
      (tensorObjIsoSheafification M N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JC (forget₂
          CommRingCat.{max s h}
      RingCat.{max s h})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app W (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
    ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
      (uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        q ((monoidalCategory R).tensorObj M N) ≫
          (toSheaf ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S) ⋙
            sheafCompose JD
            (CategoryTheory.forget AddCommGrpCat.{max s h})).map (mu M N).hom).hom.app W t =
      (tensorObjIsoSheafification (L.obj M) (L.obj N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂
          CommRingCat.{max s h}
      RingCat.{max s h})).obj S).obj)).unit.app
          ((L.obj M).val ⊗ (L.obj N).val)).app W
            ((uInv.map x ≫ I.moduleUnderlying.inv.app M ≫ q M).hom.app W t
              ⊗ₜ[S.obj.obj W]
              (uInv.map y ≫ I.moduleUnderlying.inv.app N ≫ q N).hom.app W t))
```

## New

```lean
abbrev CanonicalRingedTensorComparison :=
  CanonicalRingedTensorComparisonOnSmallSites.{max s h, s, h, s, h}
    R S RI uInv I c L hobj
```

The five old fields correspond respectively to the common record's `q`, `q_one`,
`mu`, `naturality` and `pure`; the last three law types unfold the named conditions
in `Sheaf.Paper.RingedTopoiTensorComparisonData`.

## Users

Ran `tools/downstream.py` on the assigned module with `--uses
SheafOfModules.CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison`.
The tool matches the last name component conservatively; the table includes all
16 textual hits. Checked each actual namespace. The shared-size users carry the
record and use its fields, which the common record supplies with identical types.
No statement becomes stronger, weaker or different. A library-wide search found no
explicit references to the old record's generated constructor, projection, recursor
or noConfusion names. No consumer needs adaptation. Holder entries were refreshed against the current claim records. The assigned
module is edited; the common comparison-data module and the consumers are not (the
reviewer withdrew the delivered edit of Sheaf.Paper.RingedTopoiTensorComparisonData,
see coord/changes/H7-comparison-interface-abbreviations.md).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |
| Sheaf.Paper.CompletedTensorUnitInsertionData | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |
| Sheaf.Paper.ConstantNativePullbackMonoidal | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |
| Sheaf.Paper.ProjectionFormulaBaseChangeNaturality | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |
| Sheaf.Paper.ProjectionFormulaFiniteFree | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |
| Sheaf.Paper.ProjectionFormulaProjectiveSummand | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |
| Sheaf.Paper.ProjectionFormulaTotalization | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |
| Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses | H7 | Assigned item: common-record abbreviation and complete proofs of both holes. |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses | unclaimed | Carries the comparison or accesses its fields and total map. The alias supplies the identical fields. No adaptation. |
| Sheaf.Paper.ShiftedTensorMorphismCalculus | P5 | Carries the comparison or accesses its fields and total map. The alias supplies the identical fields. No adaptation. |
| Sheaf.Paper.SupportedSourceSystemCupCalculus | unclaimed | Carries the comparison or accesses its fields and total map. The alias supplies the identical fields. No adaptation. |
| Sheaf.Paper.ringedProjectionFormula_totalization_left | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |
| Sheaf.Paper.ringedProjectionFormula_totalization_right | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |
| Sheaf.SecSmoothPurity.CochainTensorCoherenceData | unclaimed | The existing ofLanded adapter copies the same five fields. No adaptation. |
| Sheaf.SecSmoothPurity.CoefficientComparisonsBalancedConstruction | unclaimed | Direct generic importer; the shared comparison fields retain their types. No adaptation. |
| Sheaf.SixFunctors.RingedDerivedIdentityComparison | unclaimed | Unrelated comparison namespace: conservative textual name match. No adaptation. |

The unit proof uses a generic private bridge before specializing to `max s h`.
The pure-tensor interface remains locally irreducible during the generator
calculation, avoiding expansion of the localization. Three private proved instance lemmas cache the existing weak sheafification and
underlying-set composition instances inside the private proof sections. They
do not enter public signatures or public definition bodies. These are proof changes.

## Status

landed 20261026T100301-L-4171286 2026-10-26 (merge of deliver/H7/Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses)

The proof also keeps the sheafification functor, its adjunction and the total comparison
locally irreducible. The isomorphism proof explicitly unfolds the total comparison once;
all constructions and public signatures are preserved.
