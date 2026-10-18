# Sorry ledger

Source scan; one hole per declaration, regardless of token count. Deleted declarations are not proofs.
Closure is the queue’s import upper bound. Classes use source references, not elaborated dependencies.
Progress = closed − added in the closure, with pruning reported separately.

Holes now: library **740**, closure **145**, holes in definitions **8**, definitions with undetermined data **8** (closure **3**).

Definitions with holes (def/instance/structure field):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible::AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible` (instance, line 457)
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible::AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible` (instance, line 448)
- `WeilConjectures.TraceFormula.Slop.Basic::AlgebraicGeometry.ProEtale.CondensedRing.Slop.boundedConstructibleLowerShriekComp` (def, line 144)
- `WeilConjectures.TraceFormula.Slop.Basic::AlgebraicGeometry.ProEtale.CondensedRing.Slop.unitEndRingEquiv` (def, line 160)
- `WeilConjectures.TraceFormula.Slop.Correspondence::AlgebraicGeometry.ProEtale.CondensedRing.Slop.Correspondence.traceClass` (def, line 206)
- `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek::AlgebraicGeometry.ProEtale.CondensedRing.isEquivalence_boundedConstructibleUpperStar_of_iso` (instance, line 90)
- `WeilConjectures.WeilObject.BoundedConstructible.TensorHom::AlgebraicGeometry.ProEtale.CondensedRing.isIso_weilHomComparisonApp` (instance, line 181)
- `WeilConjectures.WeilObject.BoundedConstructible.TensorHom::AlgebraicGeometry.ProEtale.CondensedRing.weilTensorComparison` (def, line 89)

Definitions with undetermined data (class-1 exceptions in `coord/hollow-definitions.md`):

- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace::AlgebraicGeometry.RelativeProjectiveSpace.construction` (line 793), chosen from `AlgebraicGeometry.exists_relativeProjData`
- `Sheaf.CategoryTheory.RingedSiteLocalizationCech::CategoryTheory.localization_fraction_iso` (line 68), chosen from `ModuleCat.localization_away_colimit`
- `Sheaf.Paper.IntegralReductionTowerWellDefined::WeilConjectures.integralTowerTransition` (line 208), chosen from `WeilConjectures.integralTowerMaps_existUnique`
- `Sheaf.Paper.IntegralReductionTowerWellDefined::WeilConjectures.integralTowerUnit` (line 201), chosen from `WeilConjectures.integralTowerMaps_existUnique`
- `Sheaf.Paper.LisseAdicSheaves::AlgebraicGeometry.Scheme.lisseCoefficientDiagramData` (line 527), chosen from `AlgebraicGeometry.Scheme.lisseCoefficientDiagram_exists`
- `Sheaf.Paper.ProjectionFormulaArrows::SheafOfModules.mixedTensorRepresentative` (line 290), chosen from `SheafOfModules.mixedTensorRepresentative_existsUnique`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback::SheafOfModules.ringedTopoiCanonicalDerivedTensorComparison` (line 760), chosen from `SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback`
- `WeilConjectures.SmoothPurity.Defs::AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` (line 106), chosen from `AlgebraicGeometry.ProEtale.CondensedRing.exists_normalizedSmoothPurityMaps`

| root | library | closure |
|---|---:|---:|
| Sheaf | 574 | 48 |
| WeilConjectures | 166 | 97 |

| baseline | scope | closed | added | net | deleted | changed holed statements |
|---|---|---:|---:|---:|---:|---:|
| 889327369 (Queue at the start of stage 3) | library | 1808 | 352 | 1456 | 733 | 14 |
| 660345513 (Application of proof-dependency imports) | library | 1805 | 351 | 1454 | 679 | 14 |
| 660345513 (Application of proof-dependency imports) | closure | 1500 | 76 | 1424 | 603 | 0 |

No closure delta is quoted across 660345513: proof-dependency imports changed the reached set.

| landing class | count |
|---|---:|
| proved | 4215 |
| decomposed | 56 |
| moved | 4159 |
| pruned | 147 |
| other | 634 |

Per group: whole-library closed/added/net since stage 3; landing count is not progress. Closure progress is shown only after the imports baseline.

| group | landings | closed | added | net | moved share |
|---|---:|---:|---:|---:|---:|
| <unknown> | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| A2 | 142 | 141 | 102 | 39 | 73/142 (51.4%) |
| A3 | 142 | 140 | 91 | 49 | 62/142 (43.7%) |
| A4 | 92 | 108 | 55 | 53 | 42/92 (45.7%) |
| A5 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| A6 | 3 | 4 | 0 | 4 | 0/3 (0.0%) |
| A7 | 2 | 2 | 2 | 0 | 2/2 (100.0%) |
| A8 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| A9 | 2 | 2 | 1 | 1 | 1/2 (50.0%) |
| B2 | 142 | 150 | 96 | 54 | 58/142 (40.8%) |
| B3 | 163 | 171 | 96 | 75 | 66/163 (40.5%) |
| B4 | 83 | 86 | 52 | 34 | 36/83 (43.4%) |
| B5 | 2 | 2 | 1 | 1 | 1/2 (50.0%) |
| B6 | 3 | 3 | 1 | 2 | 1/3 (33.3%) |
| B7 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| B8 | 2 | 6 | 0 | 6 | 0/2 (0.0%) |
| B9 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| C1 | 156 | 160 | 118 | 42 | 77/156 (49.4%) |
| C2 | 135 | 129 | 87 | 42 | 60/135 (44.4%) |
| C3 | 127 | 135 | 82 | 53 | 57/127 (44.9%) |
| C4 | 73 | 73 | 35 | 38 | 23/73 (31.5%) |
| C5 | 2 | 3 | 0 | 3 | 0/2 (0.0%) |
| C6 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| C7 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| C8 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| C9 | 2 | 2 | 1 | 1 | 1/2 (50.0%) |
| D2 | 155 | 152 | 93 | 59 | 64/155 (41.3%) |
| D3 | 124 | 141 | 74 | 67 | 53/124 (42.7%) |
| D4 | 82 | 88 | 48 | 40 | 29/82 (35.4%) |
| D5 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| D6 | 2 | 2 | 1 | 1 | 1/2 (50.0%) |
| D7 | 2 | 2 | 4 | -2 | 2/2 (100.0%) |
| D8 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| D9 | 2 | 2 | 1 | 1 | 1/2 (50.0%) |
| E1 | 170 | 203 | 109 | 94 | 83/170 (48.8%) |
| E2 | 134 | 129 | 87 | 42 | 62/134 (46.3%) |
| E3 | 127 | 146 | 100 | 46 | 60/127 (47.2%) |
| E4 | 62 | 69 | 33 | 36 | 22/62 (35.5%) |
| E5 | 2 | 4 | 0 | 4 | 0/2 (0.0%) |
| E6 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| E7 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| E8 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| E9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| F1 | 158 | 164 | 108 | 56 | 72/158 (45.6%) |
| F2 | 158 | 170 | 102 | 68 | 64/158 (40.5%) |
| F3 | 110 | 110 | 64 | 46 | 44/110 (40.0%) |
| F4 | 73 | 73 | 47 | 26 | 31/73 (42.5%) |
| F5 | 2 | 2 | 0 | 2 | 0/2 (0.0%) |
| F6 | 2 | 2 | 1 | 1 | 1/2 (50.0%) |
| F7 | 2 | 2 | 2 | 0 | 2/2 (100.0%) |
| F8 | 2 | 3 | 0 | 3 | 0/2 (0.0%) |
| F9 | 2 | 3 | 0 | 3 | 0/2 (0.0%) |
| G1 | 147 | 148 | 114 | 34 | 76/147 (51.7%) |
| G2 | 146 | 145 | 93 | 52 | 64/146 (43.8%) |
| G3 | 108 | 111 | 67 | 44 | 46/108 (42.6%) |
| G4 | 64 | 56 | 31 | 25 | 20/64 (31.2%) |
| G5 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| G6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| G7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| G8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| G9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| H1 | 145 | 144 | 111 | 33 | 77/145 (53.1%) |
| H2 | 120 | 131 | 92 | 39 | 66/120 (55.0%) |
| H3 | 128 | 146 | 103 | 43 | 70/128 (54.7%) |
| H4 | 65 | 64 | 42 | 22 | 31/65 (47.7%) |
| H5 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| H6 | 2 | 3 | 0 | 3 | 0/2 (0.0%) |
| H7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| H8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| H9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| J1 | 130 | 143 | 75 | 68 | 53/130 (40.8%) |
| J2 | 111 | 123 | 70 | 53 | 51/111 (45.9%) |
| J3 | 125 | 133 | 79 | 54 | 55/125 (44.0%) |
| J4 | 66 | 65 | 43 | 22 | 28/66 (42.4%) |
| J5 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| J6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| J7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| J8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| J9 | 1 | 1 | 2 | -1 | 1/1 (100.0%) |
| K1 | 126 | 156 | 89 | 67 | 61/126 (48.4%) |
| K2 | 127 | 127 | 84 | 43 | 65/127 (51.2%) |
| K3 | 113 | 113 | 79 | 34 | 57/113 (50.4%) |
| K4 | 70 | 57 | 35 | 22 | 24/70 (34.3%) |
| K5 | 1 | 1 | 2 | -1 | 1/1 (100.0%) |
| K6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| K7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| K8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| K9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| M1 | 146 | 152 | 94 | 58 | 65/146 (44.5%) |
| M2 | 135 | 145 | 104 | 41 | 70/135 (51.9%) |
| M3 | 113 | 116 | 73 | 43 | 52/113 (46.0%) |
| M4 | 50 | 54 | 25 | 29 | 18/50 (36.0%) |
| M5 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| M6 | 1 | 3 | 0 | 3 | 0/1 (0.0%) |
| M7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| M8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| M9 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| N1 | 141 | 142 | 110 | 32 | 75/141 (53.2%) |
| N2 | 134 | 124 | 79 | 45 | 58/134 (43.3%) |
| N3 | 93 | 88 | 66 | 22 | 46/93 (49.5%) |
| N4 | 61 | 60 | 48 | 12 | 29/61 (47.5%) |
| P1 | 124 | 145 | 93 | 52 | 67/124 (54.0%) |
| P2 | 137 | 134 | 82 | 52 | 56/137 (40.9%) |
| P3 | 107 | 99 | 83 | 16 | 54/107 (50.5%) |
| P4 | 59 | 71 | 42 | 29 | 28/59 (47.5%) |
| P5 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| P7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| P8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| P9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Q1 | 114 | 116 | 77 | 39 | 57/114 (50.0%) |
| Q2 | 109 | 112 | 81 | 31 | 54/109 (49.5%) |
| Q3 | 106 | 105 | 72 | 33 | 48/106 (45.3%) |
| Q4 | 52 | 55 | 30 | 25 | 22/52 (42.3%) |
| Q5 | 1 | 1 | 2 | -1 | 1/1 (100.0%) |
| Q6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Q7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Q8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Q9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| R1 | 130 | 134 | 99 | 35 | 68/130 (52.3%) |
| R2 | 127 | 136 | 75 | 61 | 52/127 (40.9%) |
| R3 | 102 | 99 | 67 | 32 | 44/102 (43.1%) |
| R4 | 64 | 55 | 41 | 14 | 26/64 (40.6%) |
| R5 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| R6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| R7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| R8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| R9 | 2 | 2 | 1 | 1 | 1/2 (50.0%) |
| S1 | 128 | 130 | 109 | 21 | 70/128 (54.7%) |
| S2 | 129 | 139 | 105 | 34 | 67/129 (51.9%) |
| S3 | 110 | 107 | 63 | 44 | 48/110 (43.6%) |
| S4 | 52 | 50 | 36 | 14 | 25/52 (48.1%) |
| S5 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| S6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| S7 | 1 | 2 | 0 | 2 | 0/1 (0.0%) |
| S8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| S9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| T1 | 116 | 120 | 82 | 38 | 56/116 (48.3%) |
| T2 | 137 | 159 | 97 | 62 | 64/137 (46.7%) |
| T3 | 106 | 101 | 77 | 24 | 53/106 (50.0%) |
| T4 | 72 | 64 | 38 | 26 | 24/72 (33.3%) |
| T5 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| T6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| T7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| T8 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| T9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| U1 | 129 | 132 | 92 | 40 | 62/129 (48.1%) |
| U2 | 139 | 133 | 93 | 40 | 64/139 (46.0%) |
| U3 | 101 | 104 | 70 | 34 | 50/101 (49.5%) |
| U4 | 57 | 57 | 40 | 17 | 28/57 (49.1%) |
| U5 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| U6 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| U7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| U8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| U9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| V1 | 119 | 112 | 86 | 26 | 56/119 (47.1%) |
| V2 | 130 | 133 | 90 | 43 | 62/130 (47.7%) |
| V3 | 111 | 116 | 78 | 38 | 57/111 (51.4%) |
| V4 | 54 | 48 | 38 | 10 | 25/54 (46.3%) |
| V5 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| V6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| V7 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| V8 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| V9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| W2 | 118 | 125 | 78 | 47 | 54/118 (45.8%) |
| W3 | 91 | 96 | 61 | 35 | 42/91 (46.2%) |
| W4 | 53 | 47 | 36 | 11 | 27/53 (50.9%) |
| W5 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| W6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| W7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| W8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| W9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| X2 | 125 | 122 | 95 | 27 | 64/125 (51.2%) |
| X3 | 105 | 100 | 63 | 37 | 44/105 (41.9%) |
| X5 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| X6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| X7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| X8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| X9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XR0d56945a24047e2a | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| XR1b27919aec52b018 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| XR33076d633fce5c89 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR701758115908ba19 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR70f81a388df1a824 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR916f3f6fae119923 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR9e6d7250028f1981 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| XRa0a656f89c54729e | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRa2c5451bd4aff80a | 1 | 0 | 2 | -2 | 0/1 (0.0%) |
| XRa3e07659d1a5d330 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XRaf46747ed5a82c85 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XRb0cc22400e136910 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRb44ad0154cf1285a | 1 | 3 | 0 | 3 | 0/1 (0.0%) |
| XRbb9b20b2b4a981ff | 2 | 0 | 0 | 0 | 0/2 (0.0%) |
| XRd4f549ddc0d8d578 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRd9718f5111d65eef | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XReedb48d351b955d4 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRf51ccf77cd4e9fca | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XRfef4bc449ceae451 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Y2 | 113 | 115 | 101 | 14 | 61/113 (54.0%) |
| Y3 | 108 | 94 | 57 | 37 | 46/108 (42.6%) |
| Y5 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Y6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Y7 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Y8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Y9 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Z2 | 3 | 4 | 0 | 4 | 1/3 (33.3%) |
| Z5 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Z6 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Z7 | 1 | 1 | 2 | -1 | 1/1 (100.0%) |
| Z8 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Z9 | 2 | 2 | 1 | 1 | 1/2 (50.0%) |
| launcher prover | 138 | 19 | 9 | 10 | 6/138 (4.3%) |

Nearest targets (claims from the scanned git tree; live leases may differ):

| module | distance | holes | group |
|---|---:|---:|---|
| Sheaf.SmoothPurity.NormalizedWitness | 1 | 1 | — |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | 2 | 3 | D3 |
| WeilConjectures.ZetaFunction.TraceFormula | 2 | 1 | — |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | 3 | 1 | — |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | 3 | 1 | — |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction | 3 | 1 | A3 |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | 3 | 1 | C3 |
| WeilConjectures.WeilSheaf.PoincareDuality | 3 | 1 | — |
| Sheaf.CategoryTheory.RingedDerivedRestriction | 4 | 1 | — |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | 4 | 1 | — |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | 4 | 1 | — |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | 4 | 1 | — |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | 4 | 2 | — |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension | 4 | 1 | — |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | 4 | 1 | — |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | 4 | 1 | — |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | 5 | 1 | — |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | 5 | 1 | D4 |
| Sheaf.CategoryTheory.Galois.GaloisTransitive | 5 | 1 | — |
| Sheaf.WeilSheaf.AffineCurveRangePositive | 5 | 1 | — |

Modules pruned since the imports baseline:

- `Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackComparison`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomIsSheaf`
- `Sheaf.Algebra.Category.ModuleCat.TorSymmetry`
- `Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels`
- `Sheaf.Algebra.ChangeIdealCompletion`
- `Sheaf.Algebra.CharpolyLocallyFree`
- `Sheaf.Algebra.ExtOneDirectSum`
- `Sheaf.Algebra.FiniteProjectiveTorAcyclic`
- `Sheaf.Algebra.FlatTorIdealCriterion`
- `Sheaf.Algebra.Homology.AcyclicLimitOrdinal`
- `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison`
- `Sheaf.Algebra.Homology.BalancedDerivedTensorModel`
- `Sheaf.Algebra.Homology.BaseChangeRHomPerfect`
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`
- `Sheaf.Algebra.Homology.DerivedTensorActionNaturality`
- `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology`
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`
- `Sheaf.Algebra.Homology.DerivedTensorTransitivity`
- `Sheaf.Algebra.Homology.DoubleComplexCokernelHomologyIso`
- `Sheaf.Algebra.Homology.FilteredColimitDerivedTensor`
- `Sheaf.Algebra.Homology.FilteredComplexZBDescription`
- `Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion`
- `Sheaf.Algebra.Homology.FreeResolutionSesSplit`
- `Sheaf.Algebra.Homology.FunctorialHomotopies`
- `Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator`
- `Sheaf.Algebra.Homology.KInjectiveProducts`
- `Sheaf.Algebra.Homology.KernelShiftedMappingCone`
- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`
- `Sheaf.Algebra.Homology.LowerTruncationStepSES`
- `Sheaf.Algebra.Homology.MappingCylinderSplitFactorization`
- `Sheaf.Algebra.Homology.MittagLefflerLimitHomology`
- `Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap`
- `Sheaf.Algebra.Homology.RoosComplex`
- `Sheaf.Algebra.Homology.RowCycleLiftsToZigzag`
- `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange`
- `Sheaf.Algebra.Homology.SubcategoryRightResolution`
- `Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor`
- `Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor`
- `Sheaf.Algebra.Homology.UnitEntrySplits`
- `Sheaf.Algebra.Homology.UpperTruncationStepSES`
- `Sheaf.Algebra.Homology.ZigzagModule`
- `Sheaf.Algebra.Homology.ZigzagModuleFunctorial`
- `Sheaf.Algebra.Homology.ZigzagToRowCokernel`
- `Sheaf.Algebra.Homology.ZigzagTrivialIfRowBoundary`
- `Sheaf.Algebra.LimitFinitePresentation`
- `Sheaf.Algebra.LocallyFreeCharpoly`
- `Sheaf.Algebra.LocallyFreeCharpolyProdMap`
- `Sheaf.Algebra.Module.GradedLocalizationExact`
- `Sheaf.Algebra.Module.LocalizedHomogeneousPiece`
- `Sheaf.Algebra.Module.ProjDegreeZeroLocalizationExact`
- `Sheaf.Algebra.Module.QuotientPrimaryComponentNoTorsion`
- `Sheaf.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso`
- `Sheaf.Algebra.ProjectiveDimensionWellDefined`
- `Sheaf.Algebra.Schanuel`
- `Sheaf.Algebra.TorDimensionShiftNatural`
- `Sheaf.Algebra.TorDimensionShifting`
- `Sheaf.Algebra.TorOneSurjectiveChangeRings`
- `Sheaf.Algebra.TwoTermHomotopyEquivalenceDirectSum`
- `Sheaf.AlgebraicGeometry.AbelianStrictlyHenselianOpenGerm`
- `Sheaf.AlgebraicGeometry.AffineCohomologyLocalization`
- `Sheaf.AlgebraicGeometry.AffineComplementFiniteOnIntegralCurve`
- `Sheaf.AlgebraicGeometry.AffineDerivedConcentration`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteBaseChange`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.AlgebraicGeometry.AffineFibreProductTransition`
- `Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections`
- `Sheaf.AlgebraicGeometry.AffineKoszulHomAlternatingCech`
- `Sheaf.AlgebraicGeometry.AffineLocalAcyclicOpenRestriction`
- `Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal`
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent`
- `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree`
- `Sheaf.AlgebraicGeometry.AffineTruncationKernelFlat`
- `Sheaf.AlgebraicGeometry.Ample`
- `Sheaf.AlgebraicGeometry.AmpleFiniteAffineCover`
- `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine`
- `Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine`
- `Sheaf.AlgebraicGeometry.AmpleIdealSection`
- `Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian`
- `Sheaf.AlgebraicGeometry.AmpleProjCanonicalMap`
- `Sheaf.AlgebraicGeometry.AmpleProjLocalChart`
- `Sheaf.AlgebraicGeometry.AmpleProjOpen`
- `Sheaf.AlgebraicGeometry.AmpleSeparated`
- `Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening`
- `Sheaf.AlgebraicGeometry.AssociatedModule`
- `Sheaf.AlgebraicGeometry.AssociatedModuleHom`
- `Sheaf.AlgebraicGeometry.AssociatedModulePullback`
- `Sheaf.AlgebraicGeometry.AssociatedSectionsLocalize`
- `Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts`
- `Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints`
- `Sheaf.AlgebraicGeometry.CechH1Injective`
- `Sheaf.AlgebraicGeometry.CechH1MapNatural`
- `Sheaf.AlgebraicGeometry.ChowFiniteType`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`
- `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperUniversallyClosedImage`
- `Sheaf.AlgebraicGeometry.ClosedSubsetQcIdeal`
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleIsomorphismLocal`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`
- `Sheaf.AlgebraicGeometry.CoherentProjRepresentation`
- `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`
- `Sheaf.AlgebraicGeometry.CommAlgebraSheaf`
- `Sheaf.AlgebraicGeometry.ComponentIntersectionsFinite`
- `Sheaf.AlgebraicGeometry.ConductorIdealRestriction`
- `Sheaf.AlgebraicGeometry.ConductorIdealZeroIntersection`
- `Sheaf.AlgebraicGeometry.ConductorSections`
- `Sheaf.AlgebraicGeometry.ConstantEtaleSheafShortExact`
- `Sheaf.AlgebraicGeometry.ConstantExtensionCover`
- `Sheaf.AlgebraicGeometry.ConstantModuleSheavesForgetColimits`
- `Sheaf.AlgebraicGeometry.ConstantPullbackCompositionCoherence`
- `Sheaf.AlgebraicGeometry.ConstantPullbackIdentityCoherence`
- `Sheaf.AlgebraicGeometry.ConstantRingModuleSheafEquivalence`
- `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural`
- `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric`
- `Sheaf.AlgebraicGeometry.ConstructibleClosedGenericCriterion`
- `Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteStalks`
- `Sheaf.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian`
- `Sheaf.AlgebraicGeometry.Curve.DenseIrreducibleOpens`
- `Sheaf.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions`
- `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient`
- `Sheaf.AlgebraicGeometry.Curve.ProperCohomology`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.Curve.SepClosedComparison`
- `Sheaf.AlgebraicGeometry.Curve.SepClosedComparisonCore`
- `Sheaf.AlgebraicGeometry.Curve.SepClosedComparisonCurve`
- `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris`
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
- `Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison`
- `Sheaf.AlgebraicGeometry.DescendAffine`
- `Sheaf.AlgebraicGeometry.DescendQCOpenFGSubalgebra`
- `Sheaf.AlgebraicGeometry.DescendSurjective`
- `Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek`
- `Sheaf.AlgebraicGeometry.DimOneQuasiProjective`
- `Sheaf.AlgebraicGeometry.DivisorClassCurve`
- `Sheaf.AlgebraicGeometry.DivisorModuleLocal`
- `Sheaf.AlgebraicGeometry.DvrFieldExtensionOrder`
- `Sheaf.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent`
- `Sheaf.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing`
- `Sheaf.AlgebraicGeometry.EtaleCechSectionwiseShortExact`
- `Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZeroAux`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`
- `Sheaf.AlgebraicGeometry.EtaleDirectedColimitDescent`
- `Sheaf.AlgebraicGeometry.EtaleEdgeMapBaseChange`
- `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
- `Sheaf.AlgebraicGeometry.EtaleFinitePushforwardUnitEdgeCompatibility`
- `Sheaf.AlgebraicGeometry.EtaleGeometricFibreConstantSections`
- `Sheaf.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageSectionDescription`
- `Sheaf.AlgebraicGeometry.EtaleLocalFiniteAtPoint`
- `Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePoints`
- `Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePointsElementary`
- `Sheaf.AlgebraicGeometry.EtaleLocalizeUpstairs`
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`
- `Sheaf.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField`
- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`
- `Sheaf.AlgebraicGeometry.EtaleOpenFpqcDescent`
- `Sheaf.AlgebraicGeometry.EtalePullbackForgetModules`
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
- `Sheaf.AlgebraicGeometry.EtaleResidueTriples`
- `Sheaf.AlgebraicGeometry.EtaleSectionsSurjectiveOfCechH1`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageExact`
- `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`
- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.EtaleShortExactLocalLift`
- `Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison`
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
- `Sheaf.AlgebraicGeometry.EtaleSplitsOffIsolatedPoints`
- `Sheaf.AlgebraicGeometry.EtaleSplitsOffQuasiFinitePart`
- `Sheaf.AlgebraicGeometry.EtaleStratificationLocalGluing`
- `Sheaf.AlgebraicGeometry.EtaleSubsheafFinalOpen`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `Sheaf.AlgebraicGeometry.EventuallyAffine`
- `Sheaf.AlgebraicGeometry.EventuallyClosedImmersion`
- `Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne`
- `Sheaf.AlgebraicGeometry.ExistsAmpleOfEnoughGloballyGenerated`
- `Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne`
- `Sheaf.AlgebraicGeometry.ExtEvaluation`
- `Sheaf.AlgebraicGeometry.FiberDegreeBound`
- `Sheaf.AlgebraicGeometry.FibreProductPointResidueField`
- `Sheaf.AlgebraicGeometry.FieldDiscreteModules`
- `Sheaf.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion`
- `Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion`
- `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
- `Sheaf.AlgebraicGeometry.FindGloballyGenerated`
- `Sheaf.AlgebraicGeometry.FiniteAffineFibreSections`
- `Sheaf.AlgebraicGeometry.FiniteClopenOpenCoverSection`
- `Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen`
- `Sheaf.AlgebraicGeometry.FiniteDimensionalResidueFieldOfIsolatedFiberPoint`
- `Sheaf.AlgebraicGeometry.FiniteDiscreteSeparatedAffine`
- `Sheaf.AlgebraicGeometry.FiniteEtaleDescent`
- `Sheaf.AlgebraicGeometry.FiniteEtaleDescentData`
- `Sheaf.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTrace`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists`
- `Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange`
- `Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation`
- `Sheaf.AlgebraicGeometry.FiniteIsolatedPointsOfFiniteType`
- `Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDerivedHom`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`
- `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`
- `Sheaf.AlgebraicGeometry.FiniteOpenCoverDegreeSum`
- `Sheaf.AlgebraicGeometry.FinitePiecePersistence`
- `Sheaf.AlgebraicGeometry.FinitePushforwardLocallyFree`
- `Sheaf.AlgebraicGeometry.FiniteSectionsCover`
- `Sheaf.AlgebraicGeometry.FiniteSeparableMultiplicationEtale`
- `Sheaf.AlgebraicGeometry.FiniteTypeEtaleModuleStalk`
- `Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocal`
- `Sheaf.AlgebraicGeometry.FiniteUnramifiedOnePointClosed`
- `Sheaf.AlgebraicGeometry.FirstOrderThickeningBaseChange`
- `Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent`
- `Sheaf.AlgebraicGeometry.FlatOfFpqcCover`
- `Sheaf.AlgebraicGeometry.FlatPrecomposePus`
- `Sheaf.AlgebraicGeometry.FlatUnramifiedFormallyEtale`
- `Sheaf.AlgebraicGeometry.FormallySmooth`
- `Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal`
- `Sheaf.AlgebraicGeometry.FpqcAffineDescent`
- `Sheaf.AlgebraicGeometry.FpqcAffineStandardRefinement`
- `Sheaf.AlgebraicGeometry.FpqcDescendQuasiCompact`
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`
- `Sheaf.AlgebraicGeometry.FpqcLocalOnBaseCriterion`
- `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend`
- `Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent`
- `Sheaf.AlgebraicGeometry.FpqcTensorSections`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleSite`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
- `Sheaf.AlgebraicGeometry.FunctionField`
- `Sheaf.AlgebraicGeometry.GeometricPointMorphismStalkBijection`
- `Sheaf.AlgebraicGeometry.GlobalGenerationNonvanishingCover`
- `Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction`
- `Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact`
- `Sheaf.AlgebraicGeometry.GlobalSectionsStalkComparison`
- `Sheaf.AlgebraicGeometry.GlueComponentLineBundles`
- `Sheaf.AlgebraicGeometry.GlueComponentReducedCoverSections`
- `Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle`
- `Sheaf.AlgebraicGeometry.GradedSheafStructures`
- `Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy`
- `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image`
- `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift`
- `Sheaf.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`
- `Sheaf.AlgebraicGeometry.ImmersionAffineConstructiblePieces`
- `Sheaf.AlgebraicGeometry.ImmersionFiberDegreeOne`
- `Sheaf.AlgebraicGeometry.InjectiveEtaleConstantRingModule`
- `Sheaf.AlgebraicGeometry.InjectiveEtaleModuleCechH1`
- `Sheaf.AlgebraicGeometry.InjectiveModuleSheafH1`
- `Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreChooseG`
- `Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreImageClopen`
- `Sheaf.AlgebraicGeometry.IntegralDimOneAmple`
- `Sheaf.AlgebraicGeometry.IntegralOverringJacobsonPower`
- `Sheaf.AlgebraicGeometry.InvertibleSectionRing`
- `Sheaf.AlgebraicGeometry.InvertibleTensorQcoherent`
- `Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfDegreeOfEtaleCover`
- `Sheaf.AlgebraicGeometry.IsFiniteOfFpqcCover`
- `Sheaf.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange`
- `Sheaf.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed`
- `Sheaf.AlgebraicGeometry.IsolatedFibrePointBaseChange`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.AlgebraicGeometry.KilledSheafModuleLift`
- `Sheaf.AlgebraicGeometry.LftOverFieldIsolatedPointResidueFinite`
- `Sheaf.AlgebraicGeometry.LimitContainedInConstructible`
- `Sheaf.AlgebraicGeometry.LocallyConstantFiniteValuesFiniteType`
- `Sheaf.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent`
- `Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty`
- `Sheaf.AlgebraicGeometry.MatchingObjectFibreProduct`
- `Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison`
- `Sheaf.AlgebraicGeometry.ModuleAcyclicCohomologyComparisonZero`
- `Sheaf.AlgebraicGeometry.ModuleAcyclicUnderlyingSections`
- `Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis`
- `Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyBoundary`
- `Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic`
- `Sheaf.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1`
- `Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit`
- `Sheaf.AlgebraicGeometry.ModuleSubobjectGenericConstancy`
- `Sheaf.AlgebraicGeometry.ModuleSubobjectGenericNeighbourhood`
- `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction`
- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `Sheaf.AlgebraicGeometry.Modules.ModuleSkyscraperStalkAdjunction`
- `Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum`
- `Sheaf.AlgebraicGeometry.Modules.ResidueFiber`
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcOpenImmersionDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover`
- `Sheaf.AlgebraicGeometry.Morphisms.Projective`
- `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`
- `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent`
- `Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope`
- `Sheaf.AlgebraicGeometry.NagataFixedBaseSeparatedStage`
- `Sheaf.AlgebraicGeometry.NormalGenericConstant`
- `Sheaf.AlgebraicGeometry.NormalizationProperties`
- `Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit`
- `Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom`
- `Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction`
- `Sheaf.AlgebraicGeometry.PicardH1RestrictionCompatibility`
- `Sheaf.AlgebraicGeometry.PicardLift`
- `Sheaf.AlgebraicGeometry.PopescuDelocalizeWeakLocalizationSmooth`
- `Sheaf.AlgebraicGeometry.PositiveTensorFamily`
- `Sheaf.AlgebraicGeometry.PresheafModuleStalkFilteredColimit`
- `Sheaf.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent`
- `Sheaf.AlgebraicGeometry.ProjPolynomialTwistChart`
- `Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist`
- `Sheaf.AlgebraicGeometry.ProjStandardOpenBasis`
- `Sheaf.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism`
- `Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists`
- `Sheaf.AlgebraicGeometry.ProjectiveLineTwistMultiplication`
- `Sheaf.AlgebraicGeometry.ProjectiveSpace.KoszulResolution`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistGluedIdentification`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts`
- `Sheaf.AlgebraicGeometry.ProperBasic`
- `Sheaf.AlgebraicGeometry.ProperCoproduct`
- `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition`
- `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange`
- `Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange`
- `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`
- `Sheaf.AlgebraicGeometry.PullbackIsoNsmulDevissage`
- `Sheaf.AlgebraicGeometry.PushforwardCoherentOnOpen`
- `Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebra`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusion`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraColimit`
- `Sheaf.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover`
- `Sheaf.AlgebraicGeometry.QuasiCoherentMayerVietorisOpenCover`
- `Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`
- `Sheaf.AlgebraicGeometry.QuasicoherentSheafHom`
- `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`
- `Sheaf.AlgebraicGeometry.ReducedCurveNormalization`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism`
- `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`
- `Sheaf.AlgebraicGeometry.SchemeClopenIdempotent`
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`
- `Sheaf.AlgebraicGeometry.SchemeModulesFunctorialInjectiveEmbeddings`
- `Sheaf.AlgebraicGeometry.SchemeTheoreticUnion`
- `Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology`
- `Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing`
- `Sheaf.AlgebraicGeometry.SemiRepresentableObject`
- `Sheaf.AlgebraicGeometry.SemilocalDimOneConductor`
- `Sheaf.AlgebraicGeometry.SeparatedAffineCoverCriterion`
- `Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjective`
- `Sheaf.AlgebraicGeometry.SerreSectionModuleComparison`
- `Sheaf.AlgebraicGeometry.SerreSectionModuleFinite`
- `Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint`
- `Sheaf.AlgebraicGeometry.Sites.FiniteEtaleCoproductSections`
- `Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`
- `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`
- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`
- `Sheaf.AlgebraicGeometry.SmoothZeroDifferentialsAffineOpenEtale`
- `Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant`
- `Sheaf.AlgebraicGeometry.SpecFieldPointResidueField`
- `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`
- `Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods`
- `Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange`
- `Sheaf.AlgebraicGeometry.StandardFpqcQuotientTopology`
- `Sheaf.AlgebraicGeometry.StandardSmoothAffineDiagonalGenerators`
- `Sheaf.AlgebraicGeometry.SteinUniversallyClosedFactor`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`
- `Sheaf.AlgebraicGeometry.TensorGeneratingSections`
- `Sheaf.AlgebraicGeometry.TensorGloballyGenerated`
- `Sheaf.AlgebraicGeometry.TensorSectionAffineOpen`
- `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists`
- `Sheaf.AlgebraicGeometry.UniversalThickeningAffineCase`
- `Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange`
- `Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces`
- `Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestriction`
- `Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover`
- `Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct`
- `Sheaf.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition`
- `Sheaf.AlgebraicGeometry.UnramifiedFibrePointIsolated`
- `Sheaf.AlgebraicGeometry.UnramifiedOverFieldDiscrete`
- `Sheaf.AlgebraicGeometry.UpperShriekRightAdjoint`
- `Sheaf.AlgebraicGeometry.Variety`
- `Sheaf.AlgebraicGeometry.ZariskiCohomologyLocallyZero`
- `Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction`
- `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives`
- `Sheaf.AlgebraicGeometry.ZariskiUnitsRestriction`
- `Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint`
- `Sheaf.AlgebraicGeometry.ZeroDimNoetherianAffine`
- `Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete`
- `Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan`
- `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`
- `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution`
- `Sheaf.CategoryTheory.Abelian.CompatibleNullHomotopyAssembly`
- `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift`
- `Sheaf.CategoryTheory.Abelian.HorseshoeResolutions`
- `Sheaf.CategoryTheory.AdjunctionTransferFunctorialInjectives`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.BoundedSubobjectSize`
- `Sheaf.CategoryTheory.BoundedSubobjectSurjection`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence`
- `Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy`
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`
- `Sheaf.CategoryTheory.CartanEilenbergProperties`
- `Sheaf.CategoryTheory.CartanEilenbergVerticalNullhomotopy`
- `Sheaf.CategoryTheory.CohomologyColimitSites`
- `Sheaf.CategoryTheory.ColimitSiteCechComplex`
- `Sheaf.CategoryTheory.ColimitSiteSections`
- `Sheaf.CategoryTheory.ColimitSites`
- `Sheaf.CategoryTheory.CommAlgebraSheafModule`
- `Sheaf.CategoryTheory.CoskeletonMatchingTuples`
- `Sheaf.CategoryTheory.DeltaFunctor`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit`
- `Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification`
- `Sheaf.CategoryTheory.DerivedCoupleExact`
- `Sheaf.CategoryTheory.DerivedFunctorInverts`
- `Sheaf.CategoryTheory.DiscreteModulesAbelian`
- `Sheaf.CategoryTheory.EdgeCollapse`
- `Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal`
- `Sheaf.CategoryTheory.EssentiallyConstantSplitting`
- `Sheaf.CategoryTheory.EssentiallyConstantSystem`
- `Sheaf.CategoryTheory.ExactCouple`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.CategoryTheory.FilteredColimitCategories`
- `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence`
- `Sheaf.CategoryTheory.FilteredPageTwoModel`
- `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`
- `Sheaf.CategoryTheory.Galois.AbstractEquivalence`
- `Sheaf.CategoryTheory.GrothendieckAbelian.AcyclicQuotientComplexesBoundedSize`
- `Sheaf.CategoryTheory.GrothendieckAbelian.FunctorialInjectiveComplexEmbedding`
- `Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveCriterion`
- `Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveDegreewiseExistence`
- `Sheaf.CategoryTheory.GrothendieckAbelian.ObjectsSmall`
- `Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel`
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
- `Sheaf.CategoryTheory.HalfPlaneGradedCanonical`
- `Sheaf.CategoryTheory.HomotopyHomExactOfInjective`
- `Sheaf.CategoryTheory.HomotopyLimitVanishing`
- `Sheaf.CategoryTheory.HorizontalComparisonLift`
- `Sheaf.CategoryTheory.ImageFiltration`
- `Sheaf.CategoryTheory.InjectiveIffExtendsSubobjectGenerator`
- `Sheaf.CategoryTheory.InjectiveResolutionSESComplexes`
- `Sheaf.CategoryTheory.InjectiveSheafCechAcyclic`
- `Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact`
- `Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism`
- `Sheaf.CategoryTheory.LocalizationHomColimit`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`
- `Sheaf.CategoryTheory.MatchingObjectCoskeleton`
- `Sheaf.CategoryTheory.MittagLefflerExactSequence`
- `Sheaf.CategoryTheory.MittagLefflerLimitExact`
- `Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets`
- `Sheaf.CategoryTheory.OpcyclesTorSurjection`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.PresheafChangeOfRingsAdjunction`
- `Sheaf.CategoryTheory.PushoutShortExactSequence`
- `Sheaf.CategoryTheory.QuotientJShriek`
- `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `Sheaf.CategoryTheory.RightLocalizationHomColimit`
- `Sheaf.CategoryTheory.SheafAlgebrasDirectedColimit`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
- `Sheaf.CategoryTheory.SiteCechComplex`
- `Sheaf.CategoryTheory.SiteCechMathlibComparison`
- `Sheaf.CategoryTheory.SiteCechVanishingCriterion`
- `Sheaf.CategoryTheory.SiteCohomologyPullback`
- `Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf`
- `Sheaf.CategoryTheory.SiteCoveringsCommonRefinement`
- `Sheaf.CategoryTheory.SiteEquivalenceMorphismOfSites`
- `Sheaf.CategoryTheory.SiteEquivalenceMorphismTransport`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`
- `Sheaf.CategoryTheory.SiteFilteredColimitSections`
- `Sheaf.CategoryTheory.SiteInjectiveCechAcyclic`
- `Sheaf.CategoryTheory.SiteLerayDegenerate`
- `Sheaf.CategoryTheory.SiteMorphismComposition`
- `Sheaf.CategoryTheory.SiteSesCechH1Surjective`
- `Sheaf.CategoryTheory.SiteSystemStrictification`
- `Sheaf.CategoryTheory.Sites.BinaryContractedProductPresentation`
- `Sheaf.CategoryTheory.Sites.CoherentContractedPowers`
- `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation`
- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
- `Sheaf.CategoryTheory.Sites.CohomologySiteEquivalence`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtension`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorPushoutExtension`
- `Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic`
- `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`
- `Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf`
- `Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation`
- `Sheaf.CategoryTheory.Sites.TorsorExtensionPushforward`
- `Sheaf.CategoryTheory.Sites.TorsorH1BoundaryRepresentative`
- `Sheaf.CategoryTheory.Sites.TorsorH1Functoriality`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtension`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtensionPresentation`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerTorsor`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedProductPresentation`
- `Sheaf.CategoryTheory.Sites.ZariskiExtTorsor`
- `Sheaf.CategoryTheory.Sites.ZariskiTorsorExtensionPushout`
- `Sheaf.CategoryTheory.SpecialCocontinuousCoverings`
- `Sheaf.CategoryTheory.SpectralSequenceComparison`
- `Sheaf.CategoryTheory.SpectralSequencePageInduction`
- `Sheaf.CategoryTheory.TowerSplitEnvelope`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`
- `Sheaf.CategoryTheory.Triangulated.TriangleMorphismExtension`
- `Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`
- `Sheaf.CategoryTheory.TruncationCoupleExact`
- `Sheaf.CategoryTheory.TruncationDescends`
- `Sheaf.FieldTheory.ExistsPBasis`
- `Sheaf.FieldTheory.FiniteGaloisReceivingSeparableExtensions`
- `Sheaf.FieldTheory.FinitePurelyInseparableScalarDescent`
- `Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced`
- `Sheaf.FieldTheory.FinitelyGeneratedFieldCompleteIntersectionModel`
- `Sheaf.FieldTheory.GeometricallyReducedExtensionSeparable`
- `Sheaf.FieldTheory.IntersectionSubfieldsDifferentials`
- `Sheaf.FieldTheory.IntersectionSubfieldsSubspace`
- `Sheaf.FieldTheory.MakeSeparable`
- `Sheaf.FieldTheory.MakeSeparablyGenerated`
- `Sheaf.FieldTheory.NormalExtensionFixedField`
- `Sheaf.FieldTheory.PBasisDifferentialsBasis`
- `Sheaf.FieldTheory.PBasisExtension`
- `Sheaf.FieldTheory.PIndependentDifferentialsIndependent`
- `Sheaf.FieldTheory.PthRootsExtensionDegree`
- `Sheaf.FieldTheory.PurelyInseparableDegreePIntermediate`
- `Sheaf.FieldTheory.PurelyInseparablePthRootTower`
- `Sheaf.FieldTheory.SeparableExtension`
- `Sheaf.FieldTheory.SeparableRootPthPower`
- `Sheaf.FieldTheory.SeparableSplitPurelyInseparableResidueFields`
- `Sheaf.FieldTheory.SeparableTensorPurelyInseparable`
- `Sheaf.FieldTheory.SeparablyGeneratedDifferentialsDimension`
- `Sheaf.FieldTheory.SeparablyGeneratedSeparable`
- `Sheaf.FieldTheory.SeparablyGeneratedTensorReduced`
- `Sheaf.FieldTheory.SeparatingTranscendenceBasisFiniteSubextension`
- `Sheaf.FieldTheory.TensorFieldExtensionGaloisInvariants`
- `Sheaf.GroupTheory.GroupAlgebraFunctorialInjectiveEmbeddings`
- `Sheaf.LinearAlgebra.IdempotentEndomorphismCharpolyField`
- `Sheaf.LinearAlgebra.IdempotentImageBaseChange`
- `Sheaf.LinearAlgebra.Matrix.CauchyBinet`
- `Sheaf.LinearAlgebra.Matrix.LeftInverseMinors`
- `Sheaf.LinearAlgebra.NonzeroMaximalMinorOfInjective`
- `Sheaf.LinearAlgebra.SplitExtensionFreePresentation`
- `Sheaf.LinearAlgebra.SymmetricAlgebra.DegreeExact`
- `Sheaf.LinearAlgebra.SymmetricAlgebra.Graded`
- `Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`
- `Sheaf.LinearAlgebra.TriangularChangeOfBasis`
- `Sheaf.Paper.AffineProjectiveComplexDerivedHom`
- `Sheaf.Paper.ArtinianIdealLengthOneFiltration`
- `Sheaf.Paper.BoundaryCechCompatibility`
- `Sheaf.Paper.BoundaryCechInjectiveMiddle`
- `Sheaf.Paper.BoundaryDerivationSquareZero`
- `Sheaf.Paper.CartanEilenbergLeftExactCohomology`
- `Sheaf.Paper.CechNerveFreeHomology`
- `Sheaf.Paper.ColimitSitesInjectiveSystem`
- `Sheaf.Paper.ColimitSurjectiveRingMap`
- `Sheaf.Paper.ConstantSheafOpenMaps`
- `Sheaf.Paper.CyclicExtensionCocycle`
- `Sheaf.Paper.DerivationExtendsFiniteType`
- `Sheaf.Paper.DirectImageSplitCoverProduct`
- `Sheaf.Paper.DirectedColimitBaseChangeElementwise`
- `Sheaf.Paper.EtaleFiniteDataDescent`
- `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`
- `Sheaf.Paper.EtaleRestrictionPullbackUnit`
- `Sheaf.Paper.EtaleStandardCoverCech`
- `Sheaf.Paper.FiniteEtaleEtaleLocalSplit`
- `Sheaf.Paper.FiniteHypercoverDescent`
- `Sheaf.Paper.FiniteSplitEtaleHypercover`
- `Sheaf.Paper.FiniteSplitHypercoverRefinement`
- `Sheaf.Paper.FlatFibresIrreducible`
- `Sheaf.Paper.FlatLocalCriterionNonzerodivisor`
- `Sheaf.Paper.FreeCechComplexExact`
- `Sheaf.Paper.FreeComplexMapsToResolution`
- `Sheaf.Paper.GabberZariskiEtaleRestrictionInjective`
- `Sheaf.Paper.HypercoverCohomology`
- `Sheaf.Paper.HypercoverCohomologyColimit`
- `Sheaf.Paper.HypercoverFreeResolution`
- `Sheaf.Paper.ImagePresheafSheafificationIso`
- `Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization`
- `Sheaf.Paper.InverseImageExtensionByEmptyConstant`
- `Sheaf.Paper.InverseImageFreeEtaleModule`
- `Sheaf.Paper.InverseImageStalkGerm`
- `Sheaf.Paper.KoszulComplex`
- `Sheaf.Paper.KoszulDifferential`
- `Sheaf.Paper.KoszulDifferentialSquareZero`
- `Sheaf.Paper.PlusConstructionFunctorial`
- `Sheaf.Paper.PolynomialIdealCoefficientsMonomial`
- `Sheaf.Paper.PowerSetComplexContractible`
- `Sheaf.Paper.ReducedSourceFactors`
- `Sheaf.Paper.RelativeGlobalCompleteIntersection`
- `Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation`
- `Sheaf.Paper.SectionsOverQuasiCompactOpen`
- `Sheaf.Paper.SeparableResidueCotangentInjective`
- `Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange`
- `Sheaf.Paper.SheavesKilledByNZmodModules`
- `Sheaf.Paper.SiteCoveringIsomorphicFamily`
- `Sheaf.Paper.SiteCoveringMorphismsSameH0Map`
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`
- `Sheaf.Paper.SitePlusInjectiveSeparated`
- `Sheaf.Paper.SitePlusOfSeparatedIsSheaf`
- `Sheaf.Paper.SitePlusOfSheafIso`
- `Sheaf.Paper.SitePlusSeparated`
- `Sheaf.Paper.SiteSheafificationSectionsLocal`
- `Sheaf.Paper.SmoothAtMaximalIdeal`
- `Sheaf.Paper.SmoothRetractRelativeGlobalCompleteIntersection`
- `Sheaf.Paper.StrictlyHenselianEtaleAcyclic`
- `Sheaf.Paper.TorLongExactFirstVariable`
- `Sheaf.Paper.TorsionModuleFlatBaseChangeIso`
- `Sheaf.Paper.TrivialKanHomotopyEquivalence`
- `Sheaf.Paper.WeilPbcNormalizationInResidueFieldExtension`
- `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`
- `Sheaf.Paper.ZariskiH0ProperHenselianPair`
- `Sheaf.Paper.ZeroDimensionalCohomology`
- `Sheaf.RepresentationTheory.CoinducedContinuousAcyclic`
- `Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding`
- `Sheaf.RepresentationTheory.CoinducedHomotopyContinuous`
- `Sheaf.RepresentationTheory.CoinducedHomotopyIdentity`
- `Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants`
- `Sheaf.RepresentationTheory.ContinuousCochainsShortExact`
- `Sheaf.RepresentationTheory.DiscreteContinuousCohomology`
- `Sheaf.RepresentationTheory.DiscreteContinuousFunctorialInjectives`
- `Sheaf.RepresentationTheory.DiscreteContinuousInjectives`
- `Sheaf.RepresentationTheory.DiscreteContinuousRep`
- `Sheaf.RepresentationTheory.DiscreteRep`
- `Sheaf.RepresentationTheory.OpenStabilizerAdjunction`
- `Sheaf.RepresentationTheory.SylowModuleFiltration`
- `Sheaf.RingTheory.AffineBasicSetDifference`
- `Sheaf.RingTheory.AffineBasicSetsDisjointRefinement`
- `Sheaf.RingTheory.AnalyticallyUnramified`
- `Sheaf.RingTheory.AnnihilatorAssociatedPrimes`
- `Sheaf.RingTheory.AnnihilatorAssociatedPrimesExactSequence`
- `Sheaf.RingTheory.AnnihilatorElementFlatBaseChange`
- `Sheaf.RingTheory.AnnihilatorLocalizationAway`
- `Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`
- `Sheaf.RingTheory.AssociatedGradedRing`
- `Sheaf.RingTheory.AssociatedPrimeLocalizeAtPrime`
- `Sheaf.RingTheory.AssociatedPrimePowerQuotient`
- `Sheaf.RingTheory.BijectiveQuotientMapPowOfFlat`
- `Sheaf.RingTheory.CohenRing`
- `Sheaf.RingTheory.ColimitCategoryFpAlgebras`
- `Sheaf.RingTheory.ColimitFinitelyPresentedAlgebras`
- `Sheaf.RingTheory.CompletedModuleAssociatedGradedGenerators`
- `Sheaf.RingTheory.CompletionFiniteQuotient`
- `Sheaf.RingTheory.ConormalGeneratorsGlobalCompleteIntersection`
- `Sheaf.RingTheory.DVRValuationRingCharacterization`
- `Sheaf.RingTheory.DirectedUnionSubringsFlatModule`
- `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime`
- `Sheaf.RingTheory.EtaleFiniteFactorDecomposition`
- `Sheaf.RingTheory.EtaleLiftCoprimeFactorization`
- `Sheaf.RingTheory.EtaleRetractionFiniteProductLocal`
- `Sheaf.RingTheory.EtaleRetractionFiniteTypeSplitting`
- `Sheaf.RingTheory.EtaleRingMapConormalCriterion`
- `Sheaf.RingTheory.ExistsNegativeValuationOfTensorSurjective`
- `Sheaf.RingTheory.FiniteGabberPolynomial`
- `Sheaf.RingTheory.FiniteHomogeneousGenerators`
- `Sheaf.RingTheory.FiniteIffFormalGlueing`
- `Sheaf.RingTheory.FiniteIntegralConductor`
- `Sheaf.RingTheory.FinitePresentationAndFlatOfFiniteFreeStandardCover`
- `Sheaf.RingTheory.FiniteProjectiveOfStandardCover`
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`
- `Sheaf.RingTheory.FiniteQuotientComponentQuasiFinite`
- `Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit`
- `Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimes`
- `Sheaf.RingTheory.GradedAlgebra.ShortExactGradedComponent`
- `Sheaf.RingTheory.GradedKernelFinite`
- `Sheaf.RingTheory.GradedNakayamaFree`
- `Sheaf.RingTheory.GradedNakayamaGeneration`
- `Sheaf.RingTheory.GradedPrimeAvoidance`
- `Sheaf.RingTheory.GradedSubmoduleFinite`
- `Sheaf.RingTheory.GradedSyzygy`
- `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`
- `Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition`
- `Sheaf.RingTheory.HenselianLocalRootLifting`
- `Sheaf.RingTheory.HenselianOfEtaleSectionLifting`
- `Sheaf.RingTheory.ImprovePresentationSmoothConormalFree`
- `Sheaf.RingTheory.IndStandardSmooth`
- `Sheaf.RingTheory.IntegralIdempotentAnnihilatingPolynomial`
- `Sheaf.RingTheory.IsolatedPrimeResidueFinite`
- `Sheaf.RingTheory.JacobianPresentationLift`
- `Sheaf.RingTheory.JacobsonDenominatorFunctionField`
- `Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal`
- `Sheaf.RingTheory.KrullIntersectionLocalization`
- `Sheaf.RingTheory.LiftMonicCoprimeFactorizationEtale`
- `Sheaf.RingTheory.LocalCompleteIntersectionFieldChange`
- `Sheaf.RingTheory.LocalDimensionZeroHenselian`
- `Sheaf.RingTheory.LocalDomainDimOnePrincipalLocalization`
- `Sheaf.RingTheory.MinimalGradedPresentation`
- `Sheaf.RingTheory.MinimalPresentationTor`
- `Sheaf.RingTheory.ModuleLocalizationFilteredColimit`
- `Sheaf.RingTheory.MvPolynomial.TwoVariableSyzygy`
- `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfReducedStronglyTranscendental`
- `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfStronglyTranscendental`
- `Sheaf.RingTheory.PolynomialDistinctLinearCRT`
- `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`
- `Sheaf.RingTheory.PopescuLiftOnce`
- `Sheaf.RingTheory.PopescuLiftTwice`
- `Sheaf.RingTheory.PowerSeriesFieldCohenFsAdic`
- `Sheaf.RingTheory.PowerSeriesOntoCompletion`
- `Sheaf.RingTheory.PrescribedResidueBasisSpreads`
- `Sheaf.RingTheory.PresentationsHomotopyEquivalent`
- `Sheaf.RingTheory.PrincipalMaximalDimOneRegular`
- `Sheaf.RingTheory.ProjectiveDimensionSESKernel`
- `Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel`
- `Sheaf.RingTheory.QuasiFiniteAtPrimePermanence`
- `Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization`
- `Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen`
- `Sheaf.RingTheory.QuasiFiniteLocusOpen`
- `Sheaf.RingTheory.QuasiFiniteMonogenicIntegralClosure`
- `Sheaf.RingTheory.RadicialPrimeUniqueDegreeP`
- `Sheaf.RingTheory.ReducedIdealsZeroIntersection`
- `Sheaf.RingTheory.RegularSequenceShortExactSequence`
- `Sheaf.RingTheory.RegularSequenceSwapTwo`
- `Sheaf.RingTheory.RootLiftingEtaleRetraction`
- `Sheaf.RingTheory.SemilocalDedekindDvrReduction`
- `Sheaf.RingTheory.SemilocalNormalizationDimOne`
- `Sheaf.RingTheory.SeparablePolynomialQuotientReduced`
- `Sheaf.RingTheory.SeparateImageClosedFromClosed`
- `Sheaf.RingTheory.SimpleFiltration`
- `Sheaf.RingTheory.SplitInjectionAfterCompletion`
- `Sheaf.RingTheory.StandardSmoothDimensionAtPoints`
- `Sheaf.RingTheory.SymmetricAlgebraQuotientModule`
- `Sheaf.RingTheory.SymmetricProjectivePresentationConormal`
- `Sheaf.RingTheory.TensorFiniteTypeLimit`
- `Sheaf.RingTheory.TorStrictlyProZero`
- `Sheaf.RingTheory.UniversalFirstOrderThickening`
- `Sheaf.RingTheory.ValuationRingNormal`
- `Sheaf.RingTheory.ZariskiPairFlatIntegralIsomorphism`
- `Sheaf.RingTheory.ZariskiPairRankOnePropagation`
- `Sheaf.RingTheory.ZariskisMainAway`
- `Sheaf.Topology.AbelianCohomologyDeltaFunctor`
- `Sheaf.Topology.BasisSheafSectionsGerms`
- `Sheaf.Topology.ClosedPushforwardBoundaryNaturality`
- `Sheaf.Topology.ClosedPushforwardConstantPresheaf`
- `Sheaf.Topology.ClosedPushforwardConstantRestriction`
- `Sheaf.Topology.ClosedPushforwardConstantStalks`
- `Sheaf.Topology.ContinuousOpenNormalStabilizer`
- `Sheaf.Topology.ExistsUniqueIsGenericPointOfFinite`
- `Sheaf.Topology.FilteredInjectiveCechAcyclic`
- `Sheaf.Topology.InverseImageClosedPushforwardConstant`
- `Sheaf.Topology.InverseImageOperationExt`
- `Sheaf.Topology.InverseImagePresheafModule`
- `Sheaf.Topology.LocallyConstantGermEvaluation`
- `Sheaf.Topology.LocallyConstantMapsPresheaf`
- `Sheaf.Topology.LocallyConstantMapsSheaf`
- `Sheaf.Topology.NoetherianCohomologyDimOne`
- `Sheaf.Topology.SetsExtensionByEmpty`
- `Sheaf.Topology.SetsExtensionByEmptyAdjunction`
- `Sheaf.Topology.SetsInverseImageComposition`
- `Sheaf.Topology.SheafBasisSurjection`
- `Sheaf.Topology.SheafCokernelLocalImage`
- `Sheaf.Topology.SheafDirectedColimitFiniteCoequalizers`
- `Sheaf.Topology.SheafFiniteRelationTruncations`
- `Sheaf.Topology.SheafFiniteTruncationColimit`
- `Sheaf.Topology.SheavesDirectedColimitSections`
- `Sheaf.Topology.SheavesInjectiveDirectedColimitSections`
- `Sheaf.Topology.SkyscraperConstantOnPointClosure`
- `Sheaf.Topology.Spectral.ConstructibleTopologyHausdorff`
- `Sheaf.Topology.SpectralClosedSubspace`
- `Sheaf.Topology.SpectralDirectedLimit`
- `Sheaf.Topology.SpectralDirectedLimitFiniteSober`
- `Sheaf.Topology.SpectralFiniteCoequalizer`
- `Sheaf.Topology.SpectralFiniteCoequalizerEmbedsConstant`
- `Sheaf.Topology.SpectralLimitConstructibleClosed`
- `Sheaf.Topology.SpectralLimitConstructibleClosedNonempty`
- `Sheaf.Topology.SpectralLimitDescendOpens`
- `Sheaf.Topology.SpectralLimitPullbackSections`
- `Sheaf.Topology.SpectralMapConstructibleContinuous`
- `Sheaf.Topology.SpectralSheafColimitConstantEmbeddings`
- `Sheaf.Topology.SurjectionKernelPairCoequalizer`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension`
- `WeilConjectures.SixFunctors.Finite.GlobalSections`

Scanner limitations: macro-generated declarations, elaborated anonymous/private names, and tactic dependencies cannot be recovered from source. Synthetic names are source keys, not elaborated names.

Diagnostics:

- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderRetracts>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ>
