# Ordered symmetric Proj twist normalization

## Reason

The original coordinate lemma was false because its line isomorphism t was arbitrary.
Over Spec Q in rank one (r = 0), t and -t cannot both carry the nonzero standard
coordinate to the normalized quotient. The affine scheme comparison hypotheses
place no condition on t. This repairs the invalid split: line existence must
retain its affine coordinate normalization, and compatibility then descends.
The original parent theorem and all five Challenge declarations keep their types.
No definition used by a target changes. This is a statement repair, not a proof
of the old false lemma or a new decomposition claiming proof progress.

## Old

```lean
theorem ordered_twist_coordinate_compatibility (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (hRel : eRel.hom ≫ RelativeProjectiveSpace.π S r =
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
    (hAffine : ∀ V : S.affineOpens,
      ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (hθ : θ.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) =
      RelativeProjectiveSpace.π S r)
    (hθAffine : ∀ V : S.affineOpens, RelativeProjectiveSpace.IsIntegralProjComparison
      S r V (RelativeProjectiveSpace.affineToIntegral S r θ V))
    (t : (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line) :
    ∀ i : ULift.{u} (Fin (r + 1)),
      (Scheme.Modules.tensorPullback
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
        (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient =
      ((Scheme.Modules.boundaryPullbackComparison
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
            (Scheme.Modules.unit S) ≪≫
        Scheme.Modules.pullbackObjUnitIso
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
      ((Scheme.Modules.boundaryPullbackComparison (eRel ≪≫ θ).hom).app
          (Scheme.Modules.unit _) ≪≫
        Scheme.Modules.pullbackObjUnitIso (eRel ≪≫ θ).hom).inv ≫
      (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom
```

```lean
theorem exists_ordered_twist_line (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (hRel : eRel.hom ≫ RelativeProjectiveSpace.π S r =
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
    (hAffine : ∀ V : S.affineOpens,
      ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (hθ : θ.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) =
      RelativeProjectiveSpace.π S r)
    (hθAffine : ∀ V : S.affineOpens, RelativeProjectiveSpace.IsIntegralProjComparison
      S r V (RelativeProjectiveSpace.affineToIntegral S r θ V)) :
    ∃ t : (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line, True
```

The parent discarded the True witness from exists_ordered_twist_line and applied
ordered_twist_coordinate_compatibility to an arbitrary t.

## New

```lean
theorem ordered_twist_coordinate_compatibility (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (t : (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line)
    (hNormalized :
      ∀ V : S.affineOpens, ∀ i : ULift.{u} (Fin (r + 1)),
      (Scheme.Modules.restrictFunctor
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ V.1).ι).map
        ((Scheme.Modules.tensorPullback
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
        (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient) =
      (Scheme.Modules.restrictFunctor
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ V.1).ι).map
        (((Scheme.Modules.boundaryPullbackComparison
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
            (Scheme.Modules.unit S) ≪≫
        Scheme.Modules.pullbackObjUnitIso
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
      ((Scheme.Modules.boundaryPullbackComparison (eRel ≪≫ θ).hom).app
          (Scheme.Modules.unit _) ≪≫
        Scheme.Modules.pullbackObjUnitIso (eRel ≪≫ θ).hom).inv ≫
      (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom)) :
    ∀ i : ULift.{u} (Fin (r + 1)),
      (Scheme.Modules.tensorPullback
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
        (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient =
      ((Scheme.Modules.boundaryPullbackComparison
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
            (Scheme.Modules.unit S) ≪≫
        Scheme.Modules.pullbackObjUnitIso
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
      ((Scheme.Modules.boundaryPullbackComparison (eRel ≪≫ θ).hom).app
          (Scheme.Modules.unit _) ≪≫
        Scheme.Modules.pullbackObjUnitIso (eRel ≪≫ θ).hom).inv ≫
      (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom
```

```lean
theorem exists_ordered_twist_line (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (hRel : eRel.hom ≫ RelativeProjectiveSpace.π S r =
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
    (hAffine : ∀ V : S.affineOpens,
      ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (hθ : θ.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) =
      RelativeProjectiveSpace.π S r)
    (hθAffine : ∀ V : S.affineOpens, RelativeProjectiveSpace.IsIntegralProjComparison
      S r V (RelativeProjectiveSpace.affineToIntegral S r θ V)) :
    ∃ t : (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line,
    ∀ V : S.affineOpens, ∀ i : ULift.{u} (Fin (r + 1)),
      (Scheme.Modules.restrictFunctor
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ V.1).ι).map
        ((Scheme.Modules.tensorPullback
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
        (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient) =
      (Scheme.Modules.restrictFunctor
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ V.1).ι).map
        (((Scheme.Modules.boundaryPullbackComparison
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
            (Scheme.Modules.unit S) ≪≫
        Scheme.Modules.pullbackObjUnitIso
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
      ((Scheme.Modules.boundaryPullbackComparison (eRel ≪≫ θ).hom).app
          (Scheme.Modules.unit _) ≪≫
        Scheme.Modules.pullbackObjUnitIso (eRel ≪≫ θ).hom).inv ≫
      (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom)
```

The coordinate theorem now has a complete proof by sheaf separatedness. The line
existence theorem keeps its existing one sorry and additionally retains the local
normalization its proof already promises. The parent's proof keeps that witness
and passes it to coordinate descent. Four unused geometric hypotheses and the
public FreeProjectiveBundleBaseChangeSpace import are removed from Coordinates;
the parent already imports that module publicly itself.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates | Q5 | Proves the corrected local-to-global implication; zero holes. |
| Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistLine | unclaimed | Retains normalization in the existing gluing obligation; one hole remains. |
| Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistGluing | unclaimed | Only direct importer and caller of both changed declarations; passes the retained normalization; signature and visibility unchanged. |

A repository-wide declaration search finds no other callers. The only direct
importer of either changed module is SymmetricProjOrderedTwistGluing. All three
files compile together in import order against the sandbox overlay. Their wider
import closure keeps the same parent interface. No upstream source file changes.
The DAG citers of both corrected nodes are precisely
lem-trf-symmetric-proj-ordered-twist-gluing, adapted in this packet.

## Status

landed 20261027T210206-L-1669461 2026-10-27 (merge of deliver/Q5/Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates)
