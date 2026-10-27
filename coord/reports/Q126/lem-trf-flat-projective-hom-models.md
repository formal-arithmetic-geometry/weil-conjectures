## Worker report

The module `Sheaf.Algebra.Homology.FlatProjectiveHomModels` states
`ModuleCat.flat_projective_hom_models`. Its only postponed theorem is that theorem;
its proof is `sorry`. Its docstring contains all seven proof steps and their DAG
inputs. There is no statement correction, new definition node, or dependency repair.

The four helper definitions belong to the item's canonical comparisons. The two
complex functors are abbreviations for the recorded ordinary extension/restriction
functors applied termwise. `projectiveHomModelMap` extracts the map uniquely fixed
on homogeneous coordinates by `projective_hom_evaluation_model`.
`projectiveHomModelIso` extracts the isomorphism uniquely fixed by that theorem's
signed evaluation and adjunction-counit square. These choices have determined data,
not arbitrary existence choices. The evaluation theorem has an existing proof and
is added to `stmt_deps` because these helper definitions use it in the statement.
No data or definition contains `sorry`.

Clause-by-clause translation:

- Commutative rings and a flat ring map: `{R S : Type u} [CommRing R]
  [CommRing S] (φ : R →+* S) (hφ : φ.Flat)`. The universe is arbitrary, using the
  ordinary module interfaces' common ambient universe. There is no extra algebra
  structure to choose: `extendScalars φ` uses precisely φ.
- Ordinary unbounded cochain complexes: `CochainComplex (ModuleCat.{u} R) ℤ`;
  `DerivedCategory.Q` is the recorded localization. No support bound occurs on C.
  `flatExtensionComplex φ` is `(extendScalars φ).mapHomologicalComplex (.up ℤ)`,
  with S acting on the left tensor factor. `flatRestrictionComplex φ` is the
  corresponding restriction functor.
- Tensoring cycles and boundaries: the witnesses `z C i` and `b C i` are
  isomorphisms from extended cycles and `image (C.d (i-1) i)` to the corresponding
  objects of FC. The first two equations identify their specified inclusions
  (`iCycles`, `image.ι`); the third identifies the differential's quotient onto
  its image (`factorThruImage`). These equations fix the maps uniquely, hence also
  force boundary naturality under every chain map, rather than choosing unrelated
  isomorphisms of boundary modules.
- Cohomology: `h C i` identifies extended `C.homology i` with `H^i(FC)`.
  The equation using `homologyπ` fixes it as the quotient of the cycle comparison.
  Explicit equations with `cyclesMap` and `homologyMap` give naturality in C.
- Quasi-isomorphisms: the next conjunct quantifies over arbitrary C,D,f and says
  `QuasiIso f → QuasiIso ((flatExtensionComplex φ).map f)`.
- LF: `ordinaryDerivedExtendScalars φ`, the dependency's fixed normalized universal
  derived pair. `c : Q ⋙ LF ≅ F ⋙ Q` is a natural isomorphism, and
  `c.hom = (ordinaryDerivedChangeOfRings φ).counit` fixes its normalization.
- Every K-flat resolution k: the displayed equation is
  `c_C = LF(Qk)⁻¹ ≫ c_K ≫ Q(Fk)`. Thus its first two factors are precisely the
  fixed universal K-flat model comparison, not a free choice. The next equation
  compares two resolutions and their augmentations, and the next equation states
  the three-resolution cocycle. K-flatness uses the recorded ordinary
  `MorphismProperty.kFlat`; only the resolution map is assumed a quasi-isomorphism,
  and no termwise flatness is imposed.
- Adjunction: `∃ a : LF ⊣ derivedRestrictScalars φ`. Its unit equation uses the SAME
  c and the exact-restriction localization comparison. Its right-hand side is Q
  of the unit of `(extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)`,
  whose component is `x ↦ 1 ⊗ x`. The counit equation is LF of the restriction
  comparison followed by c and Q of the SAME termwise adjunction's counit,
  `s ⊗ y ↦ s • y`. The equations hold on all representatives, not merely K-flat
  representatives or degree-zero modules. Being an Adjunction includes both
  triangle identities.
- P is bounded above: `hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i)`.
  Projective terms: `hp : ∀ i : ℤ, Module.Projective R (P.X i)`.
  The witnesses hbS and hpS assert those same properties for FP over S, with no
  finite-generation assumption. The target `N` is quantified as any complex.
- HR and HS are exactly `CochainComplex.moduleHomComplex P N` and
  `moduleHomComplex (FP) (FN)`, respectively. These are product, module-valued Hom
  complexes with the dependency's differential, not direct sums or Hom groups.
- The R comparison `eR` is explicitly equal to `projectiveHomModelIso R P hb hp N`.
  The S comparison `eS` has target `ordinaryModuleDerivedInternalHom S` of LF(QP),
  LF(QN); its equation says that postcomposing with RHom(cP⁻¹,cN) gives exactly
  `projectiveHomModelIso S (FP) hbS hpS (FN)`. Equivalently eS is that canonical
  comparison followed by RHom(cP,cN⁻¹), with the required contravariance in P.
- The same R comparison with target U(FN) is `eU`, explicitly equal to the same
  canonical R-model isomorphism applied to that target.
- Mixed naturality of the canonical model is written separately over R and S
  using `projectiveHomModelMap` and `ordinaryModuleDerivedInternalHom.map`.
  Naturality of c and the normalization equation then give mixed naturality of eS.
  The final four conjuncts explicitly say that target quasi-isomorphisms induce
  invertible localized Hom maps, and source maps equal after localization induce
  equal localized Hom maps, over each ring. They include homotopic source maps and
  the localization's inverse quasi-isomorphisms. No bound or K-flatness assumption
  occurs on N, U(FN), HR or HS.
- The node allows ordinary module categories or their singleton-site equivalent.
  This statement uses the ordinary option. The imported recorded singleton
  comparison identifies its module tensor and Hom products with the sheaf ones;
  no new site, sheaf Hom, or derived-Hom definition is substituted.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` (via `Module.Flat`).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, the existing ordinary-module localization instance.
- `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`:
  `CategoryTheory.singleton_site_module_comparison`, singleton evaluation,
  scalar/unit comparison and the ordinary-module interpretation.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.OrdinaryDerivedChangeOfRings`, `ordinaryDerivedChangeOfRings`,
  `ordinaryDerivedExtendScalars`, its fixed `counit` and `computes` fields.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex`, defined using HomComplex.Cochain and δ_hom.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`
  and its product/sheaf differential description.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, an abbreviation for the
  existing K-injective-derived closed internal-Hom bifunctor.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  the public `CategoryTheory.MorphismProperty.kFlat` interface for ordinary modules;
  its sheaf-specific predicate is not misapplied to ModuleCat.
- `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`.
- `Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel`:
  `CochainComplex.projective_hom_evaluation_model`; its full coordinate,
  signed-evaluation, counit-square, and naturality specifications were read.

All recorded proof-dependency modules are imported, including the flat exactness,
exact derived factorization, coefficient adjunction, K-flat resolution, projective
evaluation, projective tensor base change, and derived projective-representative
Mathlib modules. `lem-trf-ringed-scalar-universal-resolution-comparison` has no
recorded Lean module on this base, so there is no proof-only module to import.
The statement uses the already available fixed ordinary universal counit directly;
no unstated prerequisite is needed to type it.

Edge cases checked mathematically: zero ring and zero modules; zero P or N;
identity and nonfaithful flat maps; complexes unbounded in both directions; P
bounded above but not below; infinitely generated projective terms; arbitrary
negative cochain degrees; no finite product restriction on Hom. Flatness alone
is enough for the cycle/quotient identifications. No assertion that tensor
commutes with an infinite product is made. In particular this is not the stronger
flat base-change isomorphism for arbitrary unbounded RHom inputs.

Searches for an existing statement:

1. `msearch.py ... leanfinder` query: "Flat scalar extension identifies cycles
   boundaries and cohomology of unbounded complexes and computes derived internal
   Hom from bounded above projective complexes". Eight hits included Ext,
   isKProjective_of_projective, and K-projective cohomology-class/derived-Hom facts;
   none states the complete normalized scalar-extension and projective-Hom result.
2. `msearch.py ... loogle` query:
   "Functor.mapHomologicalComplex, HomologicalComplex.cycles, ModuleCat.extendScalars".
   No hits; remote Loogle reports unknown identifier Functor.mapHomologicalComplex.
3. `msearch.py ... grep` query:
   `flat.*homology|extendScalars.*[Pp]rojective|cyclesIso` in Algebra/Homology.
   Twenty-five hits were generic cycle isomorphisms and short-complex preservation
   facts, not this combined result.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id,
   `flat_projective_hom`, `projectiveHom`, `projective_hom`: found the usable
   projective evaluation theorem, its consumers, and a downstream documentation
   reference to this item. No existing combined theorem.
5. Source read: Stacks more-algebra.tex, lemma-RHom-out-of-projective (0A66),
   lemma-tensor-hom-adjoint (0GMT), and lemma-base-change-RHom. The 0A66 proof
   expressly permits any target complex and computes by Hom(P,N) via a K-injective
   resolution. These are consistent with the unchanged node statement.

Validation: server-only `scompile.py` compiles the module; only expected sorry
warnings are allowed. The delivery dry run and final delivery are run afterward.

## Second reading by Q126

Reopened the node and the complete Lean file and matched the clauses listed above.
The initial Hom conclusions used bare existence; replaced them with named canonical
model isomorphisms, their equality/normalization equations, mixed naturality over
both coefficient rings, and explicit localization compatibility. Added the explicit
three-resolution cocycle. Checked variance: the equation for eS uses cP.inv and
cN.hom to return to the FP,FN model, hence its forward comparison uses cP.hom and
cN.inv as the node specifies. Checked the restriction comparison's orientation in
both the unit and counit equations. No mathematical statement or source hypothesis
changed. This is the dispatcher's worker reread; the maintainer performs the
independent delivery review.
