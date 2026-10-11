## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing` states
`AlgebraicGeometry.smoothProper_dualizing`, with its sole proof `by sorry`.
No definitions or proofs are added. The source was opened and read at
https://stacks.math.columbia.edu/tag/0BRT (Lemma 48.15.7, statement and complete proof).
The local literature checkout does not contain duality.tex. The web source agrees with
the node: Noetherian base, smooth proper morphism of relative dimension d, right adjoint
on quasi-coherent complexes, and the isomorphism in D(O_X). Reversing an isomorphism
changes no assertion of existence.

Hypotheses and clauses, individually:

- Schemes X and S: `(X S : Scheme.{u})`, with no restriction on the scheme universe.
- S quasi-compact: `[CompactSpace S]`, precisely the record of
  `def-weil-pbc-quasi-compact-scheme`, with no Hausdorff assumption.
- S locally Noetherian: `[IsLocallyNoetherian S]`, precisely `pqf-def-locnoeth`.
  These two assumptions say Noetherian, without adding separatedness of S.
- Morphism: `(f : X ⟶ S)`.
- Nonnegative integer relative dimension: `(d : ℕ)`. Every nonnegative integer is
  represented, including zero; the cohomological shift uses its cast to ℤ.
- Smooth of that relative dimension: `[SmoothOfRelativeDimension d f]`. Its standard
  smooth local chart condition is the dependency's recorded equivalent of smoothness
  and fibre dimension d; no extra independent smoothness assumption is needed.
- Proper: `[IsProper f]`, the recorded separated, finite type, universally closed notion.
- Derived categories of O_X- and O_S-modules: the two explicit
  `HasDerivedCategory` binders use the common `SheafOfModules.{u} (moduleRings …)`
  carrier. Independent wX and wS allow the localization's hom universes to vary.
- Rf_* on quasi-coherent complexes: `R` is a functor between the recorded
  `schemeDerivedQCohCategory` full subcategories. `comparison` identifies
  `R ⋙ (schemeDerivedQCohProperty S).ι` with
  `(schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f`.
  Thus R is the restriction of the actual derived pushforward, not an unconstrained
  substitute. This is the same encoding used by the landed curve specialization.
- f^!: `a` has the required functor direction and `adj : R ⊣ a` says it is the right
  adjoint. These binders specify the adjoint referred to in the statement.
- O_S in degree zero: `O : schemeDerivedQCohCategory S` and `hO` identify its underlying
  object with `DerivedCategory.singleFunctor … 0` applied to `SheafOfModules.unit`.
  They are representative data for the structure sheaf, not an extra geometric condition.
- Ω¹_{X/S}: `f.relativeDifferentials`, from the recorded dependency. Its general
  signature accepts arbitrary scheme morphisms, so the node's replacement of the curve
  structure map by f needs no dependency module. It is the sheafification of relative
  Kähler differentials, with universal derivation. The read upstream
  `relativeDifferentialsSpecIso`, `relativeDifferentialsRestrictIso`, and
  `relativeDifferentialsCompIso` give precisely the affine Ω_{A/R} description.
  The read landed `diagonalConormal_iso_relativeDifferentials` gives its canonical
  identification with Δ*(I/I²); its docstring constructs this identification locally
  by I = ker(A ⊗_R A → A). Thus the diagonal and affine descriptions in the node
  specify this same shared object, rather than separate conclusion conjuncts.
  The base change dependency's fibre product convention is `Limits.pullback f f`.
  The closed diagonal follows from properness; no closed-diagonal hypothesis is added.
- Ωᵈ_{X/S}: `Scheme.Modules.exteriorSheaf f.relativeDifferentials d` uses the already
  landed sheafified sectionwise exterior powers. On an affine open, localization of
  exterior powers identifies this with the sheaf associated to ⋀^d_A Ω_{A/R}.
  Added `def-sc-sheaf-exterior-power` to stmt_deps to record this landed notion,
  as permitted by the standing brief's STMT_DEPS MAY GAIN LANDED NODES rule.
- Placement and shift: `DerivedCategory.singleFunctor … 0` puts that module in degree
  zero; `⟦(d : ℤ)⟧` is the cohomological shift [d], with the positive sign in the source.
- Isomorphism: `Nonempty ((a.obj O).obj ≅ …)` says an isomorphism exists in the full
  `schemeDerivedCategory X`, exactly the source's D(O_X), not merely on cohomology.

Dependencies used (source signatures and docstrings read):

- `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension` (and its smoothness implication).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`,
  `AlgebraicGeometry.schemeDerivedDirectImage`.
- Its dependency `Sheaf.AlgebraicGeometry.DerivedCategory`,
  `schemeDerivedCategory`, `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`,
  `AlgebraicGeometry.Scheme.Modules.exteriorSheaf` (newly cited landed node).
- Within those shared definitions: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`; `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`,
  `ExteriorAlgebra`, `exteriorPower`.
- The explanatory diagonal construction uses the recorded fibre-product conventions
  in `Sheaf.AlgebraicGeometry.BaseChangeConventions`, read in full, and the shared
  diagonal-conormal identification above. No unused imports of those explanatory
  constructions are needed in the theorem module.

The docstring gives all seven proof steps of the node, including Noetherian adjoints,
Koszul regularity of the diagonal, flat evaluation, projection formula, Koszul duality,
conormal differentials, and cancellation of the invertible determinant.

Edge cases checked before writing: d = 0 gives Ω^0 = O_X and shift zero, consistent
with finite étale duality (the landed exteriorSheaf_zero_iso records Ω^0 = O_X).
The empty scheme and empty fibres are allowed; there is no Nonempty or surjectivity
hypothesis. A nonempty smooth fibre has the specified dimension, without requiring
fibres everywhere nonempty. In dimension one, the first exterior power is the module
itself, matching the landed smoothProperCurve_dualizing; for P¹ over a field the formula
is O(-2)[1]. The definitions use alternating exterior powers in all characteristics,
including characteristic two. Non-affine and non-separated Noetherian bases are allowed.
No statement fault, correction, or disputed assertion was found.

Searches made:

- msearch.py LeanFinder: “The right adjoint of derived pushforward for a smooth proper
  morphism is top exterior differentials shifted by relative dimension”. Eight hits:
  ordinary module pushforward adjunctions, continuous pushforward adjunctions, and
  pseudofunctor adjunctions; none gives derived smooth proper duality.
- msearch.py Loogle: `AlgebraicGeometry.SmoothOfRelativeDimension, ExteriorAlgebra`:
  zero hits.
- msearch.py LeanSearch: “smooth proper relative dualizing complex top exterior power
  differentials”: service unavailable, Internal Server Error; no mathematical verdict.
- msearch.py Mathlib grep: `dualizing|upperShriek|smoothProper.*dual` in AlgebraicGeometry:
  zero hits.
- rg over WeilConjectures and lean/Sheaf:
  `smoothProper.*dual|relative_dualizing|relativeDualizing|smooth.*dualizing`:
  upstream étale-sheaf purity is about different coefficients/categories; project's
  SmoothProperCurveDualizing is only dimension one over a field. Neither is this theorem.
- grep -rn of the item id in WeilConjectures: no hits.
- rg of `relativeDifferentials|exteriorPower|smooth.*relative|relativeDimension|dualizing|
  qcDerivedPushforward|derivedPushforward` in lean/Sheaf/AlgebraicGeometry located
  Modules/ExteriorSheaf and the curve and Koszul-immersion dualizing statements.
  Read ExteriorSheaf and its def-sc-sheaf-exterior-power node in full and reused it.
- rg of `smoothProper_dualizing` in dag/lean_names_upstream.json, Mathlib,
  WeilConjectures, and lean/Sheaf: no conflicting name.

Validation: lcompile.py compiled the module in 2.6 seconds with exit code zero and no
errors or warnings. Final server compile and mechanical preflight are performed by
`deliver2.py V1 lem-sc-smooth-proper-relative-dualizing-general --no-push`.

## Second reading by V1

I reread the node statement, its Stacks source (Tag 0BRT, Lemma 48.15.7), and
`SmoothProperRelativeDualizing.lean` item by item.

- Objects: `X S : Scheme.{u}` render the schemes; `[CompactSpace S]` and
  `[IsLocallyNoetherian S]` render the quasi-compact locally Noetherian (hence
  Noetherian) base; `f : X ⟶ S` renders the morphism; `d : ℕ` renders the
  nonnegative relative dimension; `[SmoothOfRelativeDimension d f]` and
  `[IsProper f]` render smoothness and properness.
- Derived categories: the two `HasDerivedCategory` binders on
  `SheafOfModules (moduleRings ·.toRingedSpace)` render the two derived
  categories of O-modules. `R`, `comparison` render the restriction of
  `schemeDerivedDirectImage f` to `schemeDerivedQCohCategory`; `a` and
  `adj : R ⊣ a` render its right adjoint `f^!`.
- The object `O : schemeDerivedQCohCategory S` and `hO` identify it with the
  degree-zero structure sheaf. The conclusion
  `Nonempty ((a.obj O).obj ≅ (singleFunctor ...
  (Scheme.Modules.exteriorSheaf f.relativeDifferentials d))⟦(d : ℤ)⟧)` renders
  the isomorphism in `D(O_X)` with `Ω^d_{X/S}[d]`. `Nonempty` is equivalent to
  the source's displayed isomorphism (the source displays the inverse
  orientation), so no conclusion clause is changed.
- `f.relativeDifferentials` is the shared relative Kähler differential sheaf,
  and `Scheme.Modules.exteriorSheaf ... d` is the recorded sheafified exterior
  power. No extra separatedness, finiteness, nonemptiness, characteristic, or
  universe restriction is present.

Edge cases checked: `d = 0` uses the landed `exteriorSheaf_zero_iso` and zero
shift; empty schemes and empty fibres are admitted; no surjectivity or
`Nonempty` assumption is introduced; all characteristics (including two) and
arbitrary allowed scheme universes remain covered.

Searches reread: LeanFinder/Loogle/LeanSearch searches for smooth-proper
relative duality, grep of Mathlib and `WeilConjectures`, and `rg` over
`lean/Sheaf` found no existing declaration of this theorem. The existing
`exteriorSheaf` declaration and its node were checked and reused; the recorded
`def-sc-sheaf-exterior-power` dependency is therefore appropriate.

No mismatch was found and no source or Lean change was required in this second
reading. The module compiles cleanly with `lcompile.py`; all proofs remain
`sorry` as required for stage 2.
