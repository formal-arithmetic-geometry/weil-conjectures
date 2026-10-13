# AlgebraicGeometry.Etale.EtaleComplexCohomologyPresentation

## Reason

The old representation nests 24 dependent existential binders. Repeated elimination
and comparison of these large types made the unchanged module take approximately
60 seconds and made the new composition exceed the 60-second single-file limit.
The replacement is one Prop-valued inductive constructor with the very same 24
binders, in the same order, and the final True binder. No conclusion or hypothesis
changes. Elimination remains restricted to proofs, and no data are selected by a
definition. The complete module now compiles in approximately 47 seconds.

This is a representation change to the expensive definition, rather than splitting
a proof to evade its compile limit. The existing theorem names, signatures and
visibility are unchanged. The constructor of the new proposition supplies exactly
an old existential witness tuple, and conversely that tuple supplies its constructor.
Each direction is constructive and retains every witness and equality verbatim.

## Old

```lean
def EtaleComplexCohomologyPresentation
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H) : Prop :=
  ∃
    (D : I ⥤ Scheme.{u})
    (c : Cone D)
    (_hc : IsLimit c)
    (_compact : ∀ i : I, CompactSpace (D.obj i))
    (_quasiSeparated : ∀ i : I, QuasiSeparatedSpace (D.obj i))
    (_affine : ∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f))
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (_hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (_hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (a : ℤ)
    (_hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (_hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (p : ℤ)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (_hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K)))
    (eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i)))
    (_hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv)
    (L : Cocone G)
    (_hL : IsColimit L)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt p).obj
      (DerivedCategory.Q.obj L.pt))
    (_hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))), True
```

## New

```lean
abbrev EtaleComplexCohomologyPresentation
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H) : Prop :=
  EtaleComplexCohomologyPresentationData H B
```

The public support module
`Sheaf.AlgebraicGeometry.EtaleComplexCohomologyPresentationData` declares the
single-constructor proposition. Its constructor contains the original D, c, hc,
compactness, quasi-separatedness, affineness, F, phi, identity, composition, lower
bound, vanishing, G, eG, hG, p, P, hP, eH, hH, L, hL, eB, hB and True fields,
without any modification to their types. The constructor has no continuity field.
No axiom and no data-producing sorry is introduced.

## Users

The named-use check lists these three modules. Other transitive importers continue
to see exactly the previous public declaration signatures. The two external named users and the additional direct importer
HigherDirectImageRawAffineClassVanishing are compiled unchanged against the new
definition; no adaptation is delivered.
The target statements in Challenge.lean do not mention this predicate, and their
signatures and definitions are unchanged. A semantic review of this interface should
verify the constructor/existential correspondence described above.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | Same existential witnesses and equations; signatures unchanged. |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | N1 | Same existential witnesses and equations; signatures unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | W2 | Same existential witnesses and equations; signatures unchanged. |

The additional direct importer
`Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing` uses the
presentation and its continuity through the unchanged theorem interface; its
original file also compiles against this delivery without adaptation.

## Status

landed 20261013T100212-L-2500516 2026-10-13 (merge of deliver/W2/Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation)
